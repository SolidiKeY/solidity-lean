import Solidity.Semantics.AbiEntry

/-!
Guarded regression: dynamic bytes must validate their payload after the head
and length words; eager allocation panic must not be confused with calldata
reference entry or an ordinary revert. Nonempty bytes make success observable.
Fuel is this reference evaluator's recursion bound, not EVM gas. These controls
cover one bytes parameter, not general ABI/compiler progress or fork behavior.
-/
set_option autoImplicit false
namespace Solidity.H62.AuditLanguage.AbiDynamicWitness
open AbiEntry

def memoryParams : List Param := [⟨.bytes, .memory, false⟩]
def calldataParams : List Param := [⟨.bytes, .calldata, false⟩]
def payload : List UInt8 := [18, 52]
def input (free : Nat) : Input :=
  ⟨List.replicate 35 0 ++ [32] ++ List.replicate 31 0 ++ [2] ++ payload, free⟩
def truncated : Input := ⟨(input 128).data.take 69, 128⟩

theorem memory_success (fuel : Nat) :
    entry (input 128) (fuel + 2) memoryParams =
      .ok (.cons (.val (.bytes payload)) .nil) := by
  rfl

private theorem calldata_entry_of_reference (I : Input) (fuel addr len : Nat)
    (enough : ¬ I.size < 4 + headsOf calldataParams)
    (reference : cref I .bytes 4 0 = .ok (addr, len)) :
    entry I fuel calldataParams = .ok (.cons (.ref addr len) .nil) := by
  unfold entry
  rw [if_neg enough]
  simp only [calldataParams, enter, reference]
  rfl

theorem calldata_reference (free fuel : Nat) :
    entry (input free) fuel calldataParams = .ok (.cons (.ref 68 2) .nil) := by
  have data : (input free).data = (input 0).data := rfl
  have offset : load (input free).data 4 = 32 := by
    rw [data]
    decide
  have length : load (input free).data 36 = 2 := by
    rw [data]
    decide
  have size : (input free).size = 70 := by rfl
  have reference : cref (input free) .bytes 4 0 = .ok (68, 2) := by
    simp only [cref, Shape.dynamic, offset, Nat.add_zero, length, size, Shape.stride]
    rfl
  have enough : ¬ (input free).size < 4 + headsOf calldataParams := by
    rw [size]
    decide
  exact calldata_entry_of_reference (input free) fuel 68 2 enough reference


theorem calldata_observation (free fuel : Nat) :
    cvalRef (input free) (fuel + 1) .bytes 68 2 = .ok (.bytes payload) := by
  rfl

theorem memory_truncated_reverts (fuel : Nat) :
    entry truncated (fuel + 2) memoryParams = .error .revert := by
  rfl

theorem calldata_truncated_reverts (fuel : Nat) :
    entry truncated fuel calldataParams = .error .revert := by
  rfl

theorem memory_allocation_panics (fuel : Nat) :
    entry (input lim) (fuel + 2) memoryParams = .error .panic := by
  rfl

theorem memory_insufficient_fuel :
    entry (input 128) 1 memoryParams = .error .fuel := by
  rfl

/-- One decoder must preserve exact bytes, allocation panic, truncation revert,
and insufficient fuel; a single successful run cannot replace these observations. -/
def BytesMemoryBehavior (decode : Input → Nat → Except Fail (Entries memoryParams)) : Prop :=
  (∀ fuel, decode (input 128) (fuel + 2) = .ok (.cons (.val (.bytes payload)) .nil)) ∧
  (∀ fuel, decode (input lim) (fuel + 2) = .error .panic) ∧
  (∀ fuel, decode truncated (fuel + 2) = .error .revert) ∧
  decode (input 128) 1 = .error .fuel

theorem actual_memory_behavior : BytesMemoryBehavior (fun I fuel => entry I fuel memoryParams) := by
  exact ⟨memory_success, memory_allocation_panics, memory_truncated_reverts,
    memory_insufficient_fuel⟩

theorem fixed_result_refused (result : Except Fail (Entries memoryParams)) :
    ¬ BytesMemoryBehavior (fun _ _ => result) := by
  intro h
  have impossible := (h.1 0).symm.trans (h.2.1 0)
  cases impossible

#print axioms memory_success
#print axioms calldata_reference
#print axioms calldata_observation
#print axioms actual_memory_behavior
#print axioms fixed_result_refused

/-! Guarded regression: the allocation cap is inclusive, and exceeding it must
panic rather than revert. The following statements quantify over arbitrary
input data, starting allocation, requested size and returned offset. -/
theorem allocation_success_iff (I : Input) (a size next : Nat) :
    alloc I a size = .ok next ↔ next = a + roundUp size ∧ I.free + next ≤ lim := by
  by_cases h : I.free + (a + roundUp size) ≤ lim
  · rw [alloc, if_pos h]
    constructor
    · intro equal
      cases equal
      exact ⟨rfl, h⟩
    · rintro ⟨rfl, _⟩
      rfl
  · rw [alloc, if_neg h]
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨rfl, bounded⟩
      exact False.elim (h bounded)

theorem allocation_panic_iff (I : Input) (a size : Nat) :
    alloc I a size = .error .panic ↔ lim < I.free + (a + roundUp size) := by
  by_cases h : I.free + (a + roundUp size) ≤ lim
  · rw [alloc, if_pos h]
    constructor
    · intro impossible
      cases impossible
    · intro tooLarge
      exact False.elim ((Nat.not_lt_of_ge h) tooLarge)
  · rw [alloc, if_neg h]
    constructor
    · intro _
      exact Nat.lt_of_not_ge h
    · intro _
      rfl

theorem allocation_lower_free {I J : Input} {a size next : Nat}
    (lower : J.free ≤ I.free) (success : alloc I a size = .ok next) :
    alloc J a size = .ok next := by
  have bounds := (allocation_success_iff I a size next).mp success
  exact (allocation_success_iff J a size next).mpr
    ⟨bounds.1, Nat.le_trans (Nat.add_le_add_right lower next) bounds.2⟩

theorem allocation_never_reverts (I : Input) (a size : Nat) :
    alloc I a size ≠ .error .revert := by
  unfold alloc
  split <;> intro impossible <;> cases impossible

-- roundUp 33 = 64: equality is admitted, while one greater must panic.
theorem allocation_exact_limit :
    alloc (input (lim - 64)) 0 33 = .ok 64 := by
  apply (allocation_success_iff _ _ _ _).mpr
  exact ⟨by decide, by decide⟩

theorem allocation_one_over_limit :
    alloc (input (lim - 63)) 0 33 = .error .panic := by
  apply (allocation_panic_iff _ _ _).mpr
  decide

#print axioms allocation_success_iff
#print axioms allocation_panic_iff
#print axioms allocation_lower_free
#print axioms allocation_never_reverts
#print axioms allocation_exact_limit
#print axioms allocation_one_over_limit
end Solidity.H62.AuditLanguage.AbiDynamicWitness
