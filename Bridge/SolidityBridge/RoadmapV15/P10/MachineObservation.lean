import SolidityBridge.RoadmapV15.P10.DecoderAgreement

/-! Actual fetched numeric machine observations, without a second machine or
Scalar extension. These instructions lie outside Scalar.numericStep's slice.
No P1/source-frame premise is needed for native whole-State laws. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

private theorem observation_gate (op : Backend.Op) (s : EVM.State)
    (allowed : op = .PC ∨ op = .GAS ∨ op = .MSIZE)
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

private theorem observation_checked {op : Backend.Op} (site : Site op)
    (allowed : op = .PC ∨ op = .GAS ∨ op = .MSIZE) (fuel : Nat)
    (gas : 2 ≤ site.state.gasAvailable.toNat) (room : site.state.stack.length+1 ≤ 1024)
    (next : EVM.State)
    (step : EVM.step (fuel+1) 2 (some (DecoderAgreement.referenceOp op,none)) site.state = .ok next) :
    Assembly.driverSteps 1 (fuel+2) #[] site.state = .ok next ∧
    EVM.X (fuel+2) #[] site.state = EVM.X (fuel+1) #[] next := by
  have gate := observation_gate op site.state allowed gas room
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

/-- PC observes the current instruction address, before incrementing it. -/
theorem pc_agreement (site : Site .PC) (fuel : Nat)
    (gas : 2 ≤ site.state.gasAvailable.toNat) (room : site.state.stack.length+1 ≤ 1024) :
    let next := (Assembly.chargedPrepare site.state 2).replaceStackAndIncrPC
      (site.state.pc :: site.state.stack)
    Assembly.driverSteps 1 (fuel+2) #[] site.state = .ok next ∧
    EVM.X (fuel+2) #[] site.state = EVM.X (fuel+1) #[] next := by
  apply observation_checked site (Or.inl rfl) fuel gas room
  rfl

/-- GAS observes the remaining gas AFTER the actual charge, with the same
whole State. It is not the source resource-abstraction theorem. -/
theorem gas_agreement (site : Site .GAS) (fuel : Nat)
    (gas : 2 ≤ site.state.gasAvailable.toNat) (room : site.state.stack.length+1 ≤ 1024) :
    let charged := Assembly.chargedPrepare site.state 2
    let next := charged.replaceStackAndIncrPC (charged.gasAvailable :: site.state.stack)
    Assembly.driverSteps 1 (fuel+2) #[] site.state = .ok next ∧
    EVM.X (fuel+2) #[] site.state = EVM.X (fuel+1) #[] next := by
  apply observation_checked site (Or.inr (Or.inl rfl)) fuel gas room
  rfl

/-- MSIZE observes activeWords*32 in the native word arithmetic, not the
resident ByteArray's size. No allocator/padding witness is assumed. -/
theorem msize_agreement (site : Site .MSIZE) (fuel : Nat)
    (gas : 2 ≤ site.state.gasAvailable.toNat) (room : site.state.stack.length+1 ≤ 1024) :
    let next := (Assembly.chargedPrepare site.state 2).replaceStackAndIncrPC
      ((site.state.activeWords * UInt256.ofNat 32) :: site.state.stack)
    Assembly.driverSteps 1 (fuel+2) #[] site.state = .ok next ∧
    EVM.X (fuel+2) #[] site.state = EVM.X (fuel+1) #[] next := by
  apply observation_checked site (Or.inr (Or.inr rfl)) fuel gas room
  rfl

#print axioms pc_agreement
#print axioms gas_agreement
#print axioms msize_agreement
end SolidityBridge.RoadmapV15.P10
