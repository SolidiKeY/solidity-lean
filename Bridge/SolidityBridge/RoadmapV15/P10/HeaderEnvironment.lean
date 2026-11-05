import SolidityBridge.RoadmapV15.P10.DecoderAgreement

/-! Charged fetched block-time and own-balance observations over the actual pinned driver.
The existing raw environment adapter is read only. No new machine, source
frame relation, CALL origin or Osaka approval is supplied. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

private theorem header_gate (op : Backend.Op) (s : EVM.State)
    (allowed : op = .TIMESTAMP ∨ op = .SELFBALANCE)
    (chargeCost : Nat) (costEq : EVM.C' s (DecoderAgreement.referenceOp op) = chargeCost)
    (gas : chargeCost ≤ s.gasAvailable.toNat) (room : s.stack.length+1 ≤ 1024) :
    Assembly.driverGate #[] s (DecoderAgreement.referenceOp op) = .ok (s,chargeCost) := by
  have expansion : EVM.memoryExpansionCost s (DecoderAgreement.referenceOp op) = 0 := by
    rcases allowed with rfl|rfl <;>
      simp only [DecoderAgreement.referenceOp,EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have delta : EVM.δ (DecoderAgreement.referenceOp op) = some 0 := by
    rcases allowed with rfl|rfl <;> rfl
  have alpha : EVM.α (DecoderAgreement.referenceOp op) = some 1 := by
    rcases allowed with rfl|rfl <;> rfl
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [costEq,delta,alpha,Option.getD_some,if_neg (Nat.not_lt_zero _),
    if_neg (Nat.not_lt_of_ge gas),Nat.sub_zero,if_neg (Nat.not_lt_of_ge room)]
  rcases allowed with rfl|rfl <;> cases s.executionEnv.perm <;> rfl

private theorem header_checked {op : Backend.Op} (site : Site op)
    (allowed : op = .TIMESTAMP ∨ op = .SELFBALANCE) (fuel chargeCost : Nat)
    (costEq : EVM.C' site.state (DecoderAgreement.referenceOp op) = chargeCost)
    (gas : chargeCost ≤ site.state.gasAvailable.toNat) (room : site.state.stack.length+1 ≤ 1024)
    (next : EVM.State)
    (step : EVM.step (fuel+1) chargeCost (some (DecoderAgreement.referenceOp op,none)) site.state = .ok next) :
    Assembly.driverSteps 1 (fuel+2) #[] site.state = .ok next ∧
    EVM.X (fuel+2) #[] site.state = EVM.X (fuel+1) #[] next := by
  have gate := header_gate op site.state allowed chargeCost costEq gas room
  have decoded := DecoderAgreement.decode_all site
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · apply Assembly.X_continue fuel #[] site.state site.state next
      (DecoderAgreement.referenceOp op,none) chargeCost decoded gate step
    rcases allowed with rfl|rfl <;> unfold Assembly.NonhaltingOpcode <;> decide

/-- TIMESTAMP reads the current header Nat modulo the actual 256-bit word. -/
theorem timestamp_fetched (site : Site .TIMESTAMP) (fuel : Nat)
    (gas : 2 ≤ site.state.gasAvailable.toNat) (room : site.state.stack.length+1 ≤ 1024) :
    let next := (Assembly.chargedPrepare site.state 2).replaceStackAndIncrPC
      (UInt256.ofNat site.state.executionEnv.header.timestamp :: site.state.stack)
    Assembly.driverSteps 1 (fuel+2) #[] site.state = .ok next ∧
    EVM.X (fuel+2) #[] site.state = EVM.X (fuel+1) #[] next := by
  apply header_checked site (Or.inl rfl) fuel 2 rfl gas room
  rfl

/-- SELFBALANCE reads the actual code-owner account, including absent-account
zero. No warmth, caller/origin identity or invented independent balance input. -/
theorem selfbalance_fetched (site : Site .SELFBALANCE) (fuel : Nat)
    (gas : 5 ≤ site.state.gasAvailable.toNat) (room : site.state.stack.length+1 ≤ 1024) :
    let next := (Assembly.chargedPrepare site.state 5).replaceStackAndIncrPC
      (EvmYul.State.selfbalance site.state.toState :: site.state.stack)
    Assembly.driverSteps 1 (fuel+2) #[] site.state = .ok next ∧
    EVM.X (fuel+2) #[] site.state = EVM.X (fuel+1) #[] next := by
  apply header_checked site (Or.inr rfl) fuel 5 rfl gas room
  rfl

#print axioms timestamp_fetched
#print axioms selfbalance_fetched
end SolidityBridge.RoadmapV15.P10
