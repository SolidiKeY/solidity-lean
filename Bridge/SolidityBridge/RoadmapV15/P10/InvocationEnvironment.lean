import SolidityBridge.RoadmapV15.P10.DecoderAgreement

/-! Charged fetched invocation observations over the actual pinned driver.
The existing raw environment adapter is read only. No new machine, source
frame relation, CALL origin or Osaka approval is supplied. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

private theorem invocation_gate (op : Backend.Op) (s : EVM.State)
    (allowed : op = .ADDRESS ∨ op = .CALLER ∨ op = .CALLVALUE)
    (gas : 2 ≤ s.gasAvailable.toNat) (room : s.stack.length+1 ≤ 1024) :
    Assembly.driverGate #[] s (DecoderAgreement.referenceOp op) = .ok (s,2) := by
  have expansion : EVM.memoryExpansionCost s (DecoderAgreement.referenceOp op) = 0 := by
    rcases allowed with rfl|rfl|rfl <;>
      simp only [DecoderAgreement.referenceOp,EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have cost : EVM.C' s (DecoderAgreement.referenceOp op) = 2 := by
    rcases allowed with rfl|rfl|rfl <;> rfl
  have delta : EVM.δ (DecoderAgreement.referenceOp op) = some 0 := by
    rcases allowed with rfl|rfl|rfl <;> rfl
  have alpha : EVM.α (DecoderAgreement.referenceOp op) = some 1 := by
    rcases allowed with rfl|rfl|rfl <;> rfl
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [cost,delta,alpha,Option.getD_some,if_neg (Nat.not_lt_zero _),
    if_neg (Nat.not_lt_of_ge gas),Nat.sub_zero,if_neg (Nat.not_lt_of_ge room)]
  rcases allowed with rfl|rfl|rfl <;> cases s.executionEnv.perm <;> rfl

private theorem invocation_checked {op : Backend.Op} (site : Site op)
    (allowed : op = .ADDRESS ∨ op = .CALLER ∨ op = .CALLVALUE) (fuel : Nat)
    (gas : 2 ≤ site.state.gasAvailable.toNat) (room : site.state.stack.length+1 ≤ 1024)
    (next : EVM.State)
    (step : EVM.step (fuel+1) 2 (some (DecoderAgreement.referenceOp op,none)) site.state = .ok next) :
    Assembly.driverSteps 1 (fuel+2) #[] site.state = .ok next ∧
    EVM.X (fuel+2) #[] site.state = EVM.X (fuel+1) #[] next := by
  have gate := invocation_gate op site.state allowed gas room
  have decoded := DecoderAgreement.decode_all site
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · apply Assembly.X_continue fuel #[] site.state site.state next
      (DecoderAgreement.referenceOp op,none) 2 decoded gate step
    rcases allowed with rfl|rfl|rfl <;> unfold Assembly.NonhaltingOpcode <;> decide

/-- ADDRESS observes the code owner; it is distinct from caller and origin. -/
theorem address_fetched (site : Site .ADDRESS) (fuel : Nat)
    (gas : 2 ≤ site.state.gasAvailable.toNat) (room : site.state.stack.length+1 ≤ 1024) :
    let next := (Assembly.chargedPrepare site.state 2).replaceStackAndIncrPC
      (UInt256.ofNat site.state.executionEnv.codeOwner.val :: site.state.stack)
    Assembly.driverSteps 1 (fuel+2) #[] site.state = .ok next ∧
    EVM.X (fuel+2) #[] site.state = EVM.X (fuel+1) #[] next := by
  apply invocation_checked site (Or.inl rfl) fuel gas room
  rfl

/-- CALLER observes source, not the transaction sender used by ORIGIN. -/
theorem caller_fetched (site : Site .CALLER) (fuel : Nat)
    (gas : 2 ≤ site.state.gasAvailable.toNat) (room : site.state.stack.length+1 ≤ 1024) :
    let next := (Assembly.chargedPrepare site.state 2).replaceStackAndIncrPC
      (UInt256.ofNat site.state.executionEnv.source.val :: site.state.stack)
    Assembly.driverSteps 1 (fuel+2) #[] site.state = .ok next ∧
    EVM.X (fuel+2) #[] site.state = EVM.X (fuel+1) #[] next := by
  apply invocation_checked site (Or.inr (Or.inl rfl)) fuel gas room
  rfl

/-- CALLVALUE observes the exact native word, with no permission/value premise. -/
theorem callvalue_fetched (site : Site .CALLVALUE) (fuel : Nat)
    (gas : 2 ≤ site.state.gasAvailable.toNat) (room : site.state.stack.length+1 ≤ 1024) :
    let next := (Assembly.chargedPrepare site.state 2).replaceStackAndIncrPC
      (site.state.executionEnv.weiValue :: site.state.stack)
    Assembly.driverSteps 1 (fuel+2) #[] site.state = .ok next ∧
    EVM.X (fuel+2) #[] site.state = EVM.X (fuel+1) #[] next := by
  apply invocation_checked site (Or.inr (Or.inr rfl)) fuel gas room
  rfl

/-- info: 'SolidityBridge.RoadmapV15.P10.address_fetched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms address_fetched
/-- info: 'SolidityBridge.RoadmapV15.P10.caller_fetched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms caller_fetched
/-- info: 'SolidityBridge.RoadmapV15.P10.callvalue_fetched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms callvalue_fetched
end SolidityBridge.RoadmapV15.P10
