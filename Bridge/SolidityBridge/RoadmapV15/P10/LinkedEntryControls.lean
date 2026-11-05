import SolidityBridge.RoadmapV15.P10.LinkedEntry
import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Actual prefix clients at empty/full legal capacity, both permissions and
populated callers. Successful counted prefix does not imply whole-run success. -/
namespace SolidityBridge.RoadmapV15.P10.LinkedEntryControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (seed u accounts)
def words : List UInt256 := [u 0,u 258,u 513]

theorem both_permissions (perm : Bool) :
    Assembly.driverSteps 2 3 #[u 73] (linkedEntryInput (seed 2 perm) words) =
      .ok (linkedEntryNext (seed 2 perm) words) ∧
    (linkedEntryNext (seed 2 perm) words).gasAvailable.toNat = 0 := by
  exact ⟨(linked_entry_prefix _ _ _ (by decide) (by change 2 ≤ 2;decide) 0).1,
    linked_entry_debit _ _ (by change 2 ≤ 2;decide)⟩

theorem legal_capacity_boundaries :
    Assembly.driverSteps 2 3 #[] (linkedEntryInput (seed 2 false) []) =
      .ok (linkedEntryNext (seed 2 false) []) ∧
    Assembly.driverSteps 2 3 #[u 72] (linkedEntryInput (seed 2 true) (List.replicate 1024 (u 258))) =
      .ok (linkedEntryNext (seed 2 true) (List.replicate 1024 (u 258))) := by
  exact ⟨(linked_entry_prefix _ _ _ (by decide) (by decide) 0).1,
    (linked_entry_prefix _ _ _ (by simp only [List.length_replicate];decide) (by decide) 0).1⟩

/-- Prefix funding is not enough for the next opcode; short prefix fuel refuses. -/
theorem continuation_and_fuel_refusals :
    EVM.X 4 #[] (linkedEntryInput (seed 2 false) words) = .error .OutOfGass ∧
    Assembly.driverSteps 2 2 #[] (linkedEntryInput (seed 2 false) words) = .error .OutOfFuel := by
  constructor
  · have entryRun := (linked_entry_prefix #[] (seed 2 false) words (by decide) (by decide) 1).2
    refine entryRun.trans ?_
    conv_lhs => rw [Assembly.X_unfold]
    rfl
  · rfl

theorem complete_ordered_observations :
    (linkedEntryNext (seed 2 false) words).stack = [u 0,u 258,u 513] ∧
    (linkedEntryNext (seed 2 false) words).stack ≠ [u 0,u 513,u 258] ∧
    (linkedEntryNext (seed 2 false) words).pc = u 2 ∧
    (linkedEntryNext (seed 2 false) words).pc ≠ u 3 ∧
    (linkedEntryNext (seed 2 false) words).execLength = 43 ∧
    (linkedEntryNext (seed 2 false) words).executionEnv.code.data.toList =
      [0x5b,0x5b,0x15,0x7f] ++ List.replicate 31 0 ++ [0x48,0x57,0x5b,0x7f] ++
        List.replicate 32 0 ++ [0x56,0x5b,0x00] ∧
    (linkedEntryNext (seed 2 false) words).memory.data.toList = [0xaa,0xbb] ++ List.replicate 30 0 ∧
    (linkedEntryNext (seed 2 false) words).returnData.data.toList = [0xcc,0xdd] ∧
    (linkedEntryNext (seed 2 false) words).returnData.data.toList ≠ [] ∧
    (linkedEntryNext (seed 2 false) words).H_return.data.toList = [0xee,0xff] ∧
    (linkedEntryNext (seed 2 false) words).executionEnv.calldata.data.toList = [0x11,0x22,0x33] ∧
    (linkedEntryNext (seed 2 false) words).accountMap = accounts ∧
    (linkedEntryNext (seed 2 false) words).σ₀ = accounts ∧
    (linkedEntryNext (seed 2 false) words).substate = (seed 2 false).substate := by
  exact ⟨rfl,by decide,rfl,by decide,rfl,rfl,rfl,rfl,by decide,rfl,rfl,rfl,rfl,rfl⟩

#print axioms both_permissions
#print axioms legal_capacity_boundaries
#print axioms continuation_and_fuel_refusals
#print axioms complete_ordered_observations
end SolidityBridge.RoadmapV15.P10.LinkedEntryControls
