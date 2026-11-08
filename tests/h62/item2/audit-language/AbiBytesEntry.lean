import tests.h62.item2.«audit-language».AbiBytesSpec

/-!
Guarded regression: correctness of the low-level bytes decoder must not bypass
entry's head-size or dynamic-offset checks. The consumer bridge retains those
checks and the extra melem fuel layer. It covers a single memory bytes parameter,
not general ABI entry, compilation, EVM gas or fork correctness.
-/
set_option autoImplicit false
namespace Solidity.H62.AuditLanguage.AbiBytesEntry
open AbiEntry AbiDynamicWitness AbiBytesSpec

theorem memory_entry_eq_eager (I : Input) (fuel : Nat) :
    entry I fuel memoryParams =
      if I.size < 4 + headsOf memoryParams then .error .revert
      else match eager I fuel .bytes 0 with
        | .ok value => .ok (.cons (.val value) .nil)
        | .error failure => .error failure := by
  unfold entry eager
  by_cases short : I.size < 4 + headsOf memoryParams
  · rw [if_pos short, if_pos short]
  · rw [if_neg short, if_neg short]
    delta memoryParams
    rw [enter.eq_2]
    dsimp only []
    cases decoded : melem I fuel .bytes 4 4 0 with
    | error failure => rfl
    | ok pair =>
      rcases pair with ⟨value, next⟩
      rfl

theorem eager_bytes_positive_equation (I : Input) (fuel : Nat) :
    eager I (fuel + 1) .bytes 0 =
      if lim < load I.data 4 then .error .revert
      else match mdec I fuel .bytes (4 + load I.data 4) 0 with
        | .ok (value, _) => .ok value
        | .error failure => .error failure := by
  unfold eager
  rw [melem.eq_2, Shape.dynamic.eq_2, if_pos rfl]
  by_cases offset : lim < load I.data 4
  · rw [if_pos offset, if_pos offset]
  · rw [if_neg offset, if_neg offset]
    rw [Nat.add_zero]
    cases decoded : mdec I fuel .bytes (4 + load I.data 4) 0 with
    | error failure => rfl
    | ok pair =>
      rcases pair with ⟨value, next⟩
      rfl

theorem eager_bytes_with_contract
    (decode : Input → Nat → Nat → Nat → Except Fail (Val .bytes × Nat))
    (contract : MemoryBytesBehaviorSpec decode) (I : Input) (fuel : Nat) :
    eager I (fuel + 1) .bytes 0 =
      if lim < load I.data 4 then .error .revert
      else match decode I fuel (4 + load I.data 4) 0 with
        | .ok (value, _) => .ok value
        | .error failure => .error failure := by
  rw [behavior_spec_pointwise decode contract I fuel (4 + load I.data 4) 0]
  exact eager_bytes_positive_equation I fuel

theorem memory_entry_with_contract
    (decode : Input → Nat → Nat → Nat → Except Fail (Val .bytes × Nat))
    (contract : MemoryBytesBehaviorSpec decode) (I : Input) (fuel : Nat) :
    entry I (fuel + 1) memoryParams =
      if I.size < 4 + headsOf memoryParams then .error .revert
      else if lim < load I.data 4 then .error .revert
      else match decode I fuel (4 + load I.data 4) 0 with
        | .ok (value, _) => .ok (.cons (.val value) .nil)
        | .error failure => .error failure := by
  rw [memory_entry_eq_eager, eager_bytes_with_contract decode contract]
  by_cases short : I.size < 4 + headsOf memoryParams
  · rw [if_pos short, if_pos short]
  · rw [if_neg short, if_neg short]
    by_cases offset : lim < load I.data 4
    · rw [if_pos offset, if_pos offset]
    · rw [if_neg offset, if_neg offset]
      cases decoded : decode I fuel (4 + load I.data 4) 0 with
      | error failure => rfl
      | ok pair =>
        rcases pair with ⟨value, next⟩
        rfl

theorem memory_entry_zero_fuel (I : Input) :
    entry I 0 memoryParams =
      if I.size < 4 + headsOf memoryParams then .error .revert else .error .fuel := by
  rw [memory_entry_eq_eager]
  rfl

#print axioms memory_entry_eq_eager
#print axioms eager_bytes_positive_equation
#print axioms eager_bytes_with_contract
#print axioms memory_entry_with_contract
#print axioms memory_entry_zero_fuel

/-! Guarded regression: entry progress must follow from numeric input bounds,
not a premise asserting successful decoding. Its output must contain the actual
bytes; an always-error or empty-success substitute must fail the contract. -/
theorem memory_entry_supported_of_contract
    (decode : Input → Nat → Nat → Nat → Except Fail (Val .bytes × Nat))
    (contract : MemoryBytesBehaviorSpec decode) (I : Input) (fuel next : Nat)
    (head : 4 + headsOf memoryParams ≤ I.size) (offset : load I.data 4 ≤ lim)
    (bounds : MemoryBytesBounds I (4 + load I.data 4) 0 next) :
    entry I (fuel + 2) memoryParams =
      .ok (.cons (.val (.bytes (bytesAt I.data (4 + load I.data 4 + 32)
        (load I.data (4 + load I.data 4))))) .nil) := by
  have decoded := (contract.1 I fuel (4 + load I.data 4) 0 next).mpr bounds
  rw [memory_entry_with_contract decode contract I (fuel + 1),
    if_neg (Nat.not_lt.mpr head), if_neg (Nat.not_lt.mpr offset), decoded]

/-- Exact supported success using only numeric head/offset/capacity/payload conditions. -/
def MemoryEntrySuccessSpec (decode : Input → Nat → Except Fail (Entries memoryParams)) : Prop :=
  ∀ I fuel next, 4 + headsOf memoryParams ≤ I.size → load I.data 4 ≤ lim →
    MemoryBytesBounds I (4 + load I.data 4) 0 next →
    decode I (fuel + 2) =
      .ok (.cons (.val (.bytes (bytesAt I.data (4 + load I.data 4 + 32)
        (load I.data (4 + load I.data 4))))) .nil)

theorem actual_memory_entry_success_spec :
    MemoryEntrySuccessSpec (fun I fuel => entry I fuel memoryParams) := by
  intro I fuel next head offset bounds
  exact memory_entry_supported_of_contract _ actual_memory_bytes_behavior_spec I fuel next head offset bounds

theorem error_only_memory_entry_refused (failure : Fail) :
    ¬ MemoryEntrySuccessSpec (fun _ _ => .error failure) := by
  intro contract
  have run := contract (input 128) 0 64 (by decide) (by decide)
    (by unfold MemoryBytesBounds; decide)
  cases run

def emptyMemoryEntry (_ : Input) (_ : Nat) : Except Fail (Entries memoryParams) :=
  .ok (.cons (.val (.bytes [])) .nil)

theorem empty_memory_entry_refused : ¬ MemoryEntrySuccessSpec emptyMemoryEntry := by
  intro contract
  have run := contract (input 128) 0 64 (by decide) (by decide)
    (by unfold MemoryBytesBounds; decide)
  have offset : load (input 128).data 4 = 32 := by decide
  have length : load (input 128).data 36 = 2 := by decide
  have copied : bytesAt (input 128).data 68 2 = payload := by decide
  rw [offset, length, copied] at run
  let observe : Except Fail (Entries memoryParams) → Nat := fun result =>
    match result with
    | .ok (.cons (.val (.bytes bytes)) .nil) => bytes.length
    | _ => 0
  have impossible := congrArg observe run
  change (0 : Nat) = 2 at impossible
  cases impossible

#print axioms memory_entry_supported_of_contract
#print axioms actual_memory_entry_success_spec
#print axioms error_only_memory_entry_refused
#print axioms empty_memory_entry_refused
end Solidity.H62.AuditLanguage.AbiBytesEntry
