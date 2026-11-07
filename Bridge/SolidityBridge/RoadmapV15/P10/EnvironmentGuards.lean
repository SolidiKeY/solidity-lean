import SolidityBridge.RoadmapV15.P10.EnvironmentSelection

/-! Exact gas/stack/fuel classification for the five admitted environment
selections. Counted-prefix short fuel and actual X short fuel differ explicitly.
No source, consensus, world or rollback adequacy is inferred. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
theorem environment_gate_result (k : EnvKey) (s : EVM.State) (valid : Array UInt256) :
    Assembly.driverGate valid s (DecoderAgreement.referenceOp (environmentOp k)) =
      if s.gasAvailable.toNat < environmentCost k then .error .OutOfGass
      else if 1024 < s.stack.length+1 then .error .StackOverflow
      else .ok (s,environmentCost k) := by
  have expansion : EVM.memoryExpansionCost s (DecoderAgreement.referenceOp (environmentOp k)) = 0 := by
    cases k <;> simp only [environmentOp,DecoderAgreement.referenceOp,EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have cost : EVM.C' s (DecoderAgreement.referenceOp (environmentOp k)) = environmentCost k := by cases k <;> rfl
  have delta : EVM.δ (DecoderAgreement.referenceOp (environmentOp k)) = some 0 := by cases k <;> rfl
  have alpha : EVM.α (DecoderAgreement.referenceOp (environmentOp k)) = some 1 := by cases k <;> rfl
  have charge : s.gasAvailable-UInt256.ofNat 0=s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0)=s.gasAvailable
    rw [sub_zero]
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [cost,delta,alpha,Option.getD_some,if_neg (Nat.not_lt_zero _),Nat.sub_zero]
  cases k <;> cases s.executionEnv.perm <;> rfl

theorem environment_driver_result (k : EnvKey) (site : Site (environmentOp k)) (fuel : Nat) :
    let next := (Assembly.chargedPrepare site.state (environmentCost k)).replaceStackAndIncrPC
      (environmentWord site.state.toState k::site.state.stack)
    Assembly.driverSteps 1 (fuel+2) #[] site.state =
      if site.state.gasAvailable.toNat < environmentCost k then .error .OutOfGass
      else if 1024 < site.state.stack.length+1 then .error .StackOverflow
      else .ok next := by
  by_cases gas : site.state.gasAvailable.toNat < environmentCost k
  · simp only [Assembly.driverSteps,DecoderAgreement.decode_all,Option.option,bind,Except.bind]
    rw [environment_gate_result]
    simp only [if_pos gas]
  · by_cases full : 1024 < site.state.stack.length+1
    · simp only [Assembly.driverSteps,DecoderAgreement.decode_all,Option.option,bind,Except.bind]
      rw [environment_gate_result]
      simp only [if_neg gas,if_pos full]
    · simp only [if_neg gas,if_neg full]
      exact (environment_fetched k site fuel (Nat.le_of_not_gt gas) (Nat.le_of_not_gt full)).1
theorem environment_short_fuel (k : EnvKey) (site : Site (environmentOp k)) :
    Assembly.driverSteps 1 0 #[] site.state = .error .OutOfFuel ∧
    Assembly.driverSteps 1 1 #[] site.state = .error .OutOfFuel ∧
    EVM.X 0 #[] site.state = .error .OutOfFuel ∧
    EVM.X 1 #[] site.state =
      (if site.state.gasAvailable.toNat < environmentCost k then .error .OutOfGass
       else if 1024 < site.state.stack.length+1 then .error .StackOverflow
       else .error .OutOfFuel) := by
  refine ⟨rfl,rfl,rfl,?_⟩
  rw [Assembly.X_unfold 0,DecoderAgreement.decode_all]
  simp only [Option.getD_some]
  rw [environment_gate_result]
  by_cases gas : site.state.gasAvailable.toNat < environmentCost k
  · simp only [if_pos gas]
  · by_cases full : 1024 < site.state.stack.length+1
    · simp only [if_neg gas,if_pos full]
    · simp only [if_neg gas,if_neg full]
      rfl
theorem environment_x_refusals (k : EnvKey) (site : Site (environmentOp k)) (fuel : Nat) :
    (site.state.gasAvailable.toNat < environmentCost k →
      EVM.X (fuel+2) #[] site.state = .error .OutOfGass) ∧
    (environmentCost k ≤ site.state.gasAvailable.toNat →
      1024 < site.state.stack.length+1 →
      EVM.X (fuel+2) #[] site.state = .error .StackOverflow) := by
  rw [Assembly.X_unfold (fuel+1),DecoderAgreement.decode_all]
  simp only [Option.getD_some]
  rw [environment_gate_result]
  constructor
  · intro gas
    simp only [if_pos gas]
  · intro gas full
    simp only [if_neg (Nat.not_lt_of_ge gas),if_pos full]
#print axioms environment_gate_result
#print axioms environment_driver_result
#print axioms environment_short_fuel
#print axioms environment_x_refusals
end SolidityBridge.RoadmapV15.P10
