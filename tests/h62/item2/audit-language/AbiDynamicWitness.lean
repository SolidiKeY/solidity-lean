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
end Solidity.H62.AuditLanguage.AbiDynamicWitness
