import SolidityBridge.RoadmapV15.P10.NonbranchTables
import SolidityBridge.RoadmapV15.P10.WordPushFixtures
import SolidityBridge.RoadmapV15.P10.JumpMemberConsumer

/-! Arbitrary-table and populated caller controls; a real fetched JUMPI shows
why branch opcodes are excluded. No table is asserted to equal opaque D_J. -/
namespace SolidityBridge.RoadmapV15.P10.NonbranchTableControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures

/-- Both permissions, arbitrary tables, nonzero words and distinct caller tail. -/
theorem arbitrary_table_client (valid : Array UInt256) (perm : Bool) (w : Scalar.Word) :
    Assembly.driverSteps 1 2 valid (input 10 perm w spill) = .ok (expected perm w spill) ∧
    EVM.X 2 valid (input 10 perm w spill) = EVM.X 1 valid (expected perm w spill) := by
  have h := (word_push_table_agreement valid (seed 10 perm) before after w spill
    (by decide) (by change 3 ≤ 10;decide) (by decide) 0).2
  simpa only [input,expected,seed,before,after,u,wordPushInput,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

/-- Duplicate, unrelated and empty destination arrays all admit this PUSH. -/
theorem populated_tables :
    Assembly.driverSteps 1 2 #[u 72,u 72,u 73] (input 10 false 72 spill) =
      .ok (expected false 72 spill) ∧
    Assembly.driverSteps 1 2 #[u 0] (input 10 true (BitVec.ofNat 256 (2^256-1)) spill) =
      .ok (expected true (BitVec.ofNat 256 (2^256-1)) spill) ∧
    Assembly.driverSteps 1 2 #[] (input 10 false 0 spill) = .ok (expected false 0 spill) := by
  exact ⟨(arbitrary_table_client _ _ _).1,(arbitrary_table_client _ _ _).1,
    (arbitrary_table_client _ _ _).1⟩

/-- Full legal input refuses a push; low gas and low fuel keep their ordering. -/
theorem refusal_order :
    Assembly.driverSteps 1 2 #[u 73] (input 2 false 72 (List.replicate 1024 258)) = .error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[u 73] (input 3 false 72 (List.replicate 1024 258)) = .error .StackOverflow ∧
    Assembly.driverSteps 1 1 #[u 73] (input 0 false 72 spill) = .error .OutOfFuel := by
  have full : Assembly.driverSteps 1 2 #[u 73]
      (input 3 false 72 (List.replicate 1024 258)) = .error .StackOverflow := by
    change Assembly.driverSteps 1 2 #[u 73]
      (wordPushInput (seed 3 false) before after 72 (List.replicate 1024 258)) = _
    rw [word_push_checked_tables #[u 73] #[] _ _ _ _ _ (by decide) 2]
    exact (word_push_full_stack (seed 3 false) before after 72 (List.replicate 1024 258)
      (by decide) (by decide) (by simp only [List.length_replicate]) 0).1
  exact ⟨rfl,full,rfl⟩

def branch : EVM.State :=
  (jumpMemberSite (⟨seed 10 false,[],[],by decide⟩ : Site .JUMPI) (u 72) (u 1) [u 258,u 513]).state

/-- Real fetched branch behavior changes with the table, so its exclusion matters. -/
theorem branch_counterexample :
    Assembly.driverSteps 1 2 #[u 72] branch =
      .ok {Assembly.chargedPrepare branch 10 with pc := u 72,stack := [u 258,u 513]} ∧
    Assembly.driverSteps 1 2 #[u 73] branch = .error .BadJumpDestination ∧
    Assembly.driverGate #[u 72] branch .JUMPI ≠ Assembly.driverGate #[u 73] branch .JUMPI := by
  refine ⟨rfl,rfl,?_⟩
  have accepted : Assembly.driverGate #[u 72] branch .JUMPI = .ok (branch,10) := by rfl
  have refused : Assembly.driverGate #[u 73] branch .JUMPI = .error .BadJumpDestination := by rfl
  rw [accepted,refused]
  intro h
  cases h

/-- Complete ordered buffers and account observations of the same successful State. -/
theorem ordered_observations :
    (expected false 72 spill).stack = [u 72,u 258,u 513] ∧
    (expected false 72 spill).stack ≠ [u 258,u 72,u 513] ∧
    (expected false 72 spill).executionEnv.code.data.toList =
      [0x60,0x7f,0x50,0x7f] ++ List.replicate 31 0 ++ [0x48,0x00] ∧
    (expected false 72 spill).pc = u 36 ∧
    (expected false 72 spill).gasAvailable = u 7 ∧
    (expected false 72 spill).execLength = 42 ∧
    (expected false 72 spill).memory.data.toList = [0xaa,0xbb] ++ List.replicate 30 0 ∧
    (expected false 72 spill).returnData.data.toList = [0xcc,0xdd] ∧
    (expected false 72 spill).H_return.data.toList = [0xee,0xff] ∧
    (expected false 72 spill).executionEnv.calldata.data.toList = [0x11,0x22,0x33] ∧
    (expected false 72 spill).accountMap = accounts ∧
    (expected false 72 spill).σ₀ = accounts ∧
    (expected false 72 spill).substate = (seed 10 false).substate := by
  exact ⟨rfl,by decide,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms arbitrary_table_client
#print axioms populated_tables
#print axioms refusal_order
#print axioms branch_counterexample
#print axioms ordered_observations
end SolidityBridge.RoadmapV15.P10.NonbranchTableControls
