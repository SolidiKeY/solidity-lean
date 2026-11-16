import tests.h62.item2.«audit-language».AbiBytesEntry

/-!
Guarded regression: an entry contract must determine low-fuel priority, exact
payloads and failure kinds together. Preserving successful results while swapping
panic/revert must not satisfy it. The specification is complete only for one
memory-bytes reference entry, not general ABI/compiler/gas/fork correctness.
-/
set_option autoImplicit false
namespace Solidity.H62.AuditLanguage.AbiBytesEntrySpec
open AbiEntry AbiDynamicWitness AbiBytesSpec AbiBytesEntry

def EntryBytesResult (I : Input) : Entries memoryParams :=
  .cons (.val (.bytes (bytesAt I.data (4 + load I.data 4 + 32)
    (load I.data (4 + load I.data 4))))) .nil

def EntryPanicBounds (I : Input) : Prop :=
  4 + headsOf memoryParams ≤ I.size ∧ load I.data 4 ≤ lim ∧
    MemoryBytesPanicBounds I (4 + load I.data 4) 0

theorem entry_success_exact_iff (I : Input) (fuel : Nat) (values : Entries memoryParams) :
    entry I (fuel + 2) memoryParams = .ok values ↔
      MemoryEntryBounds I ∧ values = EntryBytesResult I := by
  constructor
  · intro success
    exact ⟨(memory_entry_success_exists_iff I fuel).mp ⟨values, success⟩,
      memory_entry_success_value I fuel values success⟩
  · rintro ⟨⟨head, offset, next, bounds⟩, rfl⟩
    exact memory_entry_supported_of_contract _ actual_memory_bytes_behavior_spec
      I fuel next head offset bounds

/-- One decoder must satisfy low-fuel priority and every sufficiently fueled outcome. -/
def MemoryEntryBehaviorSpec (decode : Input → Nat → Except Fail (Entries memoryParams)) : Prop :=
  (∀ I, decode I 0 =
    if I.size < 4 + headsOf memoryParams then .error .revert else .error .fuel) ∧
  (∀ I, decode I 1 =
    if I.size < 4 + headsOf memoryParams then .error .revert
    else if lim < load I.data 4 then .error .revert else .error .fuel) ∧
  (∀ I fuel values, decode I (fuel + 2) = .ok values ↔
    MemoryEntryBounds I ∧ values = EntryBytesResult I) ∧
  (∀ I fuel, decode I (fuel + 2) = .error .panic ↔ EntryPanicBounds I) ∧
  (∀ I fuel, decode I (fuel + 2) = .error .revert ↔ MemoryEntryRevertBounds I)

theorem actual_memory_entry_behavior_spec :
    MemoryEntryBehaviorSpec (fun I fuel => entry I fuel memoryParams) := by
  refine ⟨memory_entry_zero_fuel, memory_entry_one_fuel, entry_success_exact_iff, ?_, memory_entry_revert_iff⟩
  intro I fuel
  exact memory_entry_panic_iff I fuel

theorem entry_behavior_spec_pointwise
    (decode : Input → Nat → Except Fail (Entries memoryParams))
    (contract : MemoryEntryBehaviorSpec decode) (I : Input) (fuel : Nat) :
    decode I fuel = entry I fuel memoryParams := by
  cases fuel with
  | zero => exact (contract.1 I).trans (memory_entry_zero_fuel I).symm
  | succ fuel =>
    cases fuel with
    | zero => exact (contract.2.1 I).trans (memory_entry_one_fuel I).symm
    | succ fuel =>
      cases result : entry I (fuel + 2) memoryParams with
      | ok values =>
        exact (contract.2.2.1 I fuel values).mpr ((entry_success_exact_iff I fuel values).mp result)
      | error failure =>
        cases failure with
        | panic => exact (contract.2.2.2.1 I fuel).mpr ((memory_entry_panic_iff I fuel).mp result)
        | revert => exact (contract.2.2.2.2 I fuel).mpr ((memory_entry_revert_iff I fuel).mp result)
        | fuel => exact False.elim (memory_entry_two_plus_ne_fuel I fuel result)

theorem entry_behavior_spec_iff_pointwise
    (decode : Input → Nat → Except Fail (Entries memoryParams)) :
    MemoryEntryBehaviorSpec decode ↔ ∀ I fuel, decode I fuel = entry I fuel memoryParams := by
  constructor
  · intro contract I fuel
    exact entry_behavior_spec_pointwise decode contract I fuel
  · intro agreement
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro I
      rw [agreement I 0]
      exact memory_entry_zero_fuel I
    · intro I
      rw [agreement I 1]
      exact memory_entry_one_fuel I
    · intro I fuel values
      rw [agreement I (fuel + 2)]
      exact entry_success_exact_iff I fuel values
    · intro I fuel
      rw [agreement I (fuel + 2)]
      exact memory_entry_panic_iff I fuel
    · intro I fuel
      rw [agreement I (fuel + 2)]
      exact memory_entry_revert_iff I fuel

def swappedEntryFailureDecode (I : Input) (fuel : Nat) : Except Fail (Entries memoryParams) :=
  match entry I fuel memoryParams with
  | .ok values => .ok values
  | .error failure => .error (swapPanicRevert failure)

theorem swapped_entry_preserves_success (I : Input) (fuel : Nat) (values : Entries memoryParams) :
    swappedEntryFailureDecode I fuel = .ok values ↔ entry I fuel memoryParams = .ok values := by
  unfold swappedEntryFailureDecode
  cases result : entry I fuel memoryParams with
  | ok actual => rfl
  | error failure => constructor <;> intro impossible <;> cases impossible

theorem swapped_entry_behavior_refused : ¬ MemoryEntryBehaviorSpec swappedEntryFailureDecode := by
  intro contract
  have short : (⟨[], 128⟩ : Input).size < 4 + headsOf memoryParams := by decide
  have observed : swappedEntryFailureDecode ⟨[], 128⟩ 0 = .error .panic := by
    unfold swappedEntryFailureDecode
    rw [memory_entry_zero_fuel, if_pos short]
    rfl
  have claimed := contract.1 ⟨[], 128⟩
  rw [if_pos short] at claimed
  have impossible : (Except.error Fail.panic : Except Fail (Entries memoryParams)) = .error .revert :=
    observed.symm.trans claimed
  cases impossible

#print axioms entry_success_exact_iff
#print axioms actual_memory_entry_behavior_spec
#print axioms entry_behavior_spec_pointwise
#print axioms entry_behavior_spec_iff_pointwise
#print axioms swapped_entry_preserves_success
#print axioms swapped_entry_behavior_refused
end Solidity.H62.AuditLanguage.AbiBytesEntrySpec
