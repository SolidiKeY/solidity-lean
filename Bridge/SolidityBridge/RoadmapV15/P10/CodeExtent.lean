import SolidityBridge.RoadmapV15.P10.DecoderAgreement

/-! Native fetched code-size observation. This does not extend G31 admission. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

private theorem code_extent_gate (s : EVM.State)
    (gas : 2 ≤ s.gasAvailable.toNat) (room : s.stack.length+1 ≤ 1024) :
    Assembly.driverGate #[] s (DecoderAgreement.referenceOp .CODESIZE) = .ok (s,2) := by
  have expansion : EVM.memoryExpansionCost s (DecoderAgreement.referenceOp .CODESIZE) = 0 := by
    simp only [DecoderAgreement.referenceOp,EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have cost : EVM.C' s (DecoderAgreement.referenceOp .CODESIZE) = 2 := by
    rfl
  have delta : EVM.δ (DecoderAgreement.referenceOp .CODESIZE) = some 0 := by
    rfl
  have alpha : EVM.α (DecoderAgreement.referenceOp .CODESIZE) = some 1 := by
    rfl
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [cost,delta,alpha,Option.getD_some,if_neg (Nat.not_lt_zero _),
    if_neg (Nat.not_lt_of_ge gas),Nat.sub_zero,if_neg (Nat.not_lt_of_ge room)]
  cases s.executionEnv.perm <;> rfl

private theorem code_extent_checked (site : Site .CODESIZE) (fuel : Nat)
    (gas : 2 ≤ site.state.gasAvailable.toNat) (room : site.state.stack.length+1 ≤ 1024)
    (next : EVM.State)
    (step : EVM.step (fuel+1) 2 (some (DecoderAgreement.referenceOp .CODESIZE,none)) site.state = .ok next) :
    Assembly.driverSteps 1 (fuel+2) #[] site.state = .ok next ∧
    EVM.X (fuel+2) #[] site.state = EVM.X (fuel+1) #[] next := by
  have gate := code_extent_gate site.state gas room
  have decoded := DecoderAgreement.decode_all site
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · apply Assembly.X_continue fuel #[] site.state site.state next
      (DecoderAgreement.referenceOp .CODESIZE,none) 2 decoded gate step
    unfold Assembly.NonhaltingOpcode <;> decide

/-- CODESIZE observes the complete encoded code buffer, including suffix bytes,
with the actual charge and unchanged caller/account/memory components. No source
frame, allocator, execution-origin or source-admission premise is introduced. -/
theorem codesize_agreement (site : Site .CODESIZE) (fuel : Nat)
    (gas : 2 ≤ site.state.gasAvailable.toNat) (room : site.state.stack.length+1 ≤ 1024) :
    let next := (Assembly.chargedPrepare site.state 2).replaceStackAndIncrPC
      (UInt256.ofNat site.state.executionEnv.code.size :: site.state.stack)
    Assembly.driverSteps 1 (fuel+2) #[] site.state = .ok next ∧
    EVM.X (fuel+2) #[] site.state = EVM.X (fuel+1) #[] next := by
  apply code_extent_checked site fuel gas room
  rfl

#print axioms codesize_agreement
end SolidityBridge.RoadmapV15.P10
