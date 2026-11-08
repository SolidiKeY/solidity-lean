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

/-! Guarded regression: creating a calldata reference does not read the payload
and must not inherit an eager decoder's fuel requirement. The head-size and
reference-layout checks remain mandatory; later cvalRef reads still use fuel. -/
theorem calldata_entry_equation (I : Input) (fuel : Nat) :
    entry I fuel calldataParams =
      if I.size < 4 + headsOf calldataParams then .error .revert
      else match cref I .bytes 4 0 with
        | .ok (addr, len) => .ok (.cons (.ref addr len) .nil)
        | .error failure => .error failure := by
  simp only [entry, calldataParams, enter]
  cases reference : cref I .bytes 4 0 <;> rfl

theorem calldata_entry_fuel_independent (I : Input) (first second : Nat) :
    entry I first calldataParams = entry I second calldataParams := by
  rw [calldata_entry_equation, calldata_entry_equation]

theorem calldata_reference_failure (I : Input) (fuel : Nat) (failure : Fail)
    (enough : ¬ I.size < 4 + headsOf calldataParams)
    (refused : cref I .bytes 4 0 = .error failure) :
    entry I fuel calldataParams = .error failure := by
  rw [calldata_entry_equation, if_neg enough, refused]

theorem calldata_short_head (I : Input) (fuel : Nat)
    (short : I.size < 4 + headsOf calldataParams) :
    entry I fuel calldataParams = .error .revert := by
  rw [calldata_entry_equation, if_pos short]

-- The concrete reference enters at zero fuel, but observing it cannot.
theorem calldata_zero_fuel_observation (free : Nat) :
    cvalRef (input free) 0 .bytes 68 2 = .error .fuel := by
  rfl

#print axioms calldata_entry_equation
#print axioms calldata_entry_fuel_independent
#print axioms calldata_reference_failure
#print axioms calldata_short_head
#print axioms calldata_zero_fuel_observation

/-! Guarded regression: eager bytes checks are ordered. A missing length word
reverts first; an oversized length or failed allocation can panic before payload
validation. Constructive success must retain all four checks on one input. -/
theorem memory_bytes_success_of_bounds (I : Input) (fuel pos a next : Nat)
    (head : pos + 31 < I.size)
    (length : load I.data pos ≤ lim)
    (allocation : alloc I a (roundUp (load I.data pos) + 32) = .ok next)
    (payload : pos + 32 + load I.data pos ≤ I.size) :
    mdec I (fuel + 1) .bytes pos a =
      .ok (.bytes (bytesAt I.data (pos + 32) (load I.data pos)), next) := by
  simp only [mdec, head, if_true, Nat.not_lt.mpr length, if_false, allocation,
    Nat.not_lt.mpr payload]

theorem memory_bytes_missing_length (I : Input) (fuel pos a : Nat)
    (missing : ¬ pos + 31 < I.size) :
    mdec I (fuel + 1) .bytes pos a = .error .revert := by
  simp only [mdec, missing, if_false]

theorem memory_bytes_oversized_length (I : Input) (fuel pos a : Nat)
    (head : pos + 31 < I.size) (oversized : lim < load I.data pos) :
    mdec I (fuel + 1) .bytes pos a = .error .panic := by
  simp only [mdec, head, oversized, if_true]

theorem memory_bytes_allocation_failure (I : Input) (fuel pos a : Nat) (failure : Fail)
    (head : pos + 31 < I.size) (length : load I.data pos ≤ lim)
    (allocation : alloc I a (roundUp (load I.data pos) + 32) = .error failure) :
    mdec I (fuel + 1) .bytes pos a = .error failure := by
  simp only [mdec, head, if_true, Nat.not_lt.mpr length, if_false, allocation]

theorem memory_bytes_truncated_payload (I : Input) (fuel pos a next : Nat)
    (head : pos + 31 < I.size) (length : load I.data pos ≤ lim)
    (allocation : alloc I a (roundUp (load I.data pos) + 32) = .ok next)
    (truncated : I.size < pos + 32 + load I.data pos) :
    mdec I (fuel + 1) .bytes pos a = .error .revert := by
  simp only [mdec, head, if_true, Nat.not_lt.mpr length, if_false, allocation, truncated]

-- Bytes have no nested elements: positive mdec fuel does not affect this branch.
theorem memory_bytes_positive_fuel_independent (I : Input) (first second pos a : Nat) :
    mdec I (first + 1) .bytes pos a = mdec I (second + 1) .bytes pos a := by
  rfl

#print axioms memory_bytes_success_of_bounds
#print axioms memory_bytes_missing_length
#print axioms memory_bytes_oversized_length
#print axioms memory_bytes_allocation_failure
#print axioms memory_bytes_truncated_payload
#print axioms memory_bytes_positive_fuel_independent

/-! Guarded regression: constructive success alone must not hide missing guard
premises. The converse recovers every check from an actual successful bytes
result, with no restriction on the input calldata or allocation start. -/
theorem memory_bytes_success_iff (I : Input) (fuel pos a next : Nat) :
    mdec I (fuel + 1) .bytes pos a =
      .ok (.bytes (bytesAt I.data (pos + 32) (load I.data pos)), next) ↔
    pos + 31 < I.size ∧ load I.data pos ≤ lim ∧
      alloc I a (roundUp (load I.data pos) + 32) = .ok next ∧
      pos + 32 + load I.data pos ≤ I.size := by
  constructor
  · intro success
    by_cases head : pos + 31 < I.size
    · by_cases length : load I.data pos ≤ lim
      · cases allocation : alloc I a (roundUp (load I.data pos) + 32) with
        | error failure =>
          rw [memory_bytes_allocation_failure I fuel pos a failure head length allocation] at success
          cases success
        | ok actual =>
          by_cases payload : pos + 32 + load I.data pos ≤ I.size
          · have expected := memory_bytes_success_of_bounds I fuel pos a actual head length allocation payload
            have same : actual = next :=
              congrArg Prod.snd (Except.ok.inj (expected.symm.trans success))
            exact ⟨head, length, congrArg (fun n => (Except.ok n : Except Fail Nat)) same, payload⟩
          · rw [memory_bytes_truncated_payload I fuel pos a actual head length allocation
              (Nat.lt_of_not_ge payload)] at success
            cases success
      · rw [memory_bytes_oversized_length I fuel pos a head (Nat.lt_of_not_ge length)] at success
        cases success
    · rw [memory_bytes_missing_length I fuel pos a head] at success
      cases success
  · rintro ⟨head, length, allocation, payload⟩
    exact memory_bytes_success_of_bounds I fuel pos a next head length allocation payload

theorem memory_bytes_lower_free {I J : Input} (fuel pos a next : Nat)
    (data : J.data = I.data) (lower : J.free ≤ I.free)
    (success : mdec I (fuel + 1) .bytes pos a =
      .ok (.bytes (bytesAt I.data (pos + 32) (load I.data pos)), next)) :
    mdec J (fuel + 1) .bytes pos a =
      .ok (.bytes (bytesAt J.data (pos + 32) (load J.data pos)), next) := by
  have bounds := (memory_bytes_success_iff I fuel pos a next).mp success
  have size : J.size = I.size := congrArg List.length data
  have length : load J.data pos = load I.data pos := congrArg (fun bytes => load bytes pos) data
  apply (memory_bytes_success_iff J fuel pos a next).mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [size]
    exact bounds.1
  · rw [length]
    exact bounds.2.1
  · rw [length]
    exact allocation_lower_free lower bounds.2.2.1
  · rw [size, length]
    exact bounds.2.2.2

#print axioms memory_bytes_success_iff
#print axioms memory_bytes_lower_free

/-! Guarded regression: eager bytes panic must not be credited to a missing
length word or truncated payload. This exact characterization retains the
ordered head/length checks and the actual allocator's panic condition. -/
theorem memory_bytes_panic_iff (I : Input) (fuel pos a : Nat) :
    mdec I (fuel + 1) .bytes pos a = .error .panic ↔
    pos + 31 < I.size ∧
      (lim < load I.data pos ∨
        (load I.data pos ≤ lim ∧
          alloc I a (roundUp (load I.data pos) + 32) = .error .panic)) := by
  constructor
  · intro panic
    by_cases head : pos + 31 < I.size
    · by_cases length : load I.data pos ≤ lim
      · cases allocation : alloc I a (roundUp (load I.data pos) + 32) with
        | error failure =>
          have propagated := memory_bytes_allocation_failure I fuel pos a failure head length allocation
          have same : failure = .panic := Except.error.inj (propagated.symm.trans panic)
          exact ⟨head, Or.inr ⟨length,
            congrArg (fun f => (Except.error f : Except Fail Nat)) same⟩⟩
        | ok next =>
          by_cases payload : pos + 32 + load I.data pos ≤ I.size
          · rw [memory_bytes_success_of_bounds I fuel pos a next head length allocation payload] at panic
            cases panic
          · rw [memory_bytes_truncated_payload I fuel pos a next head length allocation
              (Nat.lt_of_not_ge payload)] at panic
            cases panic
      · exact ⟨head, Or.inl (Nat.lt_of_not_ge length)⟩
    · rw [memory_bytes_missing_length I fuel pos a head] at panic
      cases panic
  · rintro ⟨head, oversized | ⟨length, allocation⟩⟩
    · exact memory_bytes_oversized_length I fuel pos a head oversized
    · exact memory_bytes_allocation_failure I fuel pos a .panic head length allocation

theorem memory_bytes_panic_bound_iff (I : Input) (fuel pos a : Nat) :
    mdec I (fuel + 1) .bytes pos a = .error .panic ↔
    pos + 31 < I.size ∧
      (lim < load I.data pos ∨
        (load I.data pos ≤ lim ∧
          lim < I.free + (a + roundUp (roundUp (load I.data pos) + 32)))) := by
  rw [memory_bytes_panic_iff, allocation_panic_iff]

#print axioms memory_bytes_panic_iff
#print axioms memory_bytes_panic_bound_iff
end Solidity.H62.AuditLanguage.AbiDynamicWitness
