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
end Solidity.H62.AuditLanguage.AbiBytesEntry
