import SolidityBridge.RoadmapV15.P10.DecoderAgreement
import Solidity.Source.State

/-! Native fetched calldata extent and an explicit source-input byte installation.
Decoded objects and payload bytes remain distinct; no ABI relation is invented. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

private theorem calldata_extent_gate (s : EVM.State)
    (gas : 2 ≤ s.gasAvailable.toNat) (room : s.stack.length+1 ≤ 1024) :
    Assembly.driverGate #[] s (DecoderAgreement.referenceOp .CALLDATASIZE) = .ok (s,2) := by
  have expansion : EVM.memoryExpansionCost s (DecoderAgreement.referenceOp .CALLDATASIZE) = 0 := by
    simp only [DecoderAgreement.referenceOp,EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have cost : EVM.C' s (DecoderAgreement.referenceOp .CALLDATASIZE) = 2 := by
    rfl
  have delta : EVM.δ (DecoderAgreement.referenceOp .CALLDATASIZE) = some 0 := by
    rfl
  have alpha : EVM.α (DecoderAgreement.referenceOp .CALLDATASIZE) = some 1 := by
    rfl
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [cost,delta,alpha,Option.getD_some,if_neg (Nat.not_lt_zero _),
    if_neg (Nat.not_lt_of_ge gas),Nat.sub_zero,if_neg (Nat.not_lt_of_ge room)]
  cases s.executionEnv.perm <;> rfl

private theorem calldata_extent_checked (site : Site .CALLDATASIZE) (fuel : Nat)
    (gas : 2 ≤ site.state.gasAvailable.toNat) (room : site.state.stack.length+1 ≤ 1024)
    (next : EVM.State)
    (step : EVM.step (fuel+1) 2 (some (DecoderAgreement.referenceOp .CALLDATASIZE,none)) site.state = .ok next) :
    Assembly.driverSteps 1 (fuel+2) #[] site.state = .ok next ∧
    EVM.X (fuel+2) #[] site.state = EVM.X (fuel+1) #[] next := by
  have gate := calldata_extent_gate site.state gas room
  have decoded := DecoderAgreement.decode_all site
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · apply Assembly.X_continue fuel #[] site.state site.state next
      (DecoderAgreement.referenceOp .CALLDATASIZE,none) 2 decoded gate step
    unfold Assembly.NonhaltingOpcode <;> decide

/-- Actual whole-buffer CALLDATASIZE with exact charge and whole-State/X result.
This is independent of ABI decoding, source expressions and memory allocation. -/
theorem calldatasize_agreement (site : Site .CALLDATASIZE) (fuel : Nat)
    (gas : 2 ≤ site.state.gasAvailable.toNat) (room : site.state.stack.length+1 ≤ 1024) :
    let next := (Assembly.chargedPrepare site.state 2).replaceStackAndIncrPC
      (UInt256.ofNat site.state.executionEnv.calldata.size :: site.state.stack)
    Assembly.driverSteps 1 (fuel+2) #[] site.state = .ok next ∧
    EVM.X (fuel+2) #[] site.state = EVM.X (fuel+1) #[] next := by
  apply calldata_extent_checked site fuel gas room
  rfl

/-- Install precisely the existing immutable source payload bytes in a native
site. This constructor does not relate decoded objects or prove source lowering. -/
def calldataSite {D : Source.Layout} (site : Site .CALLDATASIZE) (c : Source.Calldata D) :
    Site .CALLDATASIZE :=
  {site with seed := {site.seed with executionEnv :=
    {site.seed.executionEnv with calldata := ⟨c.input.toArray⟩}}}

theorem calldataSite_bytes {D : Source.Layout} (site : Site .CALLDATASIZE) (c : Source.Calldata D) :
    (calldataSite site c).state.executionEnv.calldata.data.toList = c.input := by
  exact List.toList_toArray

/-- Constructor-based transport from the published source input field. No
source/object-size equality is assumed: byte length is derived after installation. -/
theorem calldatasize_source_input {D : Source.Layout} (site : Site .CALLDATASIZE)
    (c : Source.Calldata D) (fuel : Nat) (gas : 2 ≤ site.seed.gasAvailable.toNat)
    (room : site.seed.stack.length+1 ≤ 1024) :
    let start := (calldataSite site c).state
    let next := (Assembly.chargedPrepare start 2).replaceStackAndIncrPC
      (UInt256.ofNat c.input.length :: start.stack)
    Assembly.driverSteps 1 (fuel+2) #[] start = .ok next ∧
      EVM.X (fuel+2) #[] start = EVM.X (fuel+1) #[] next := by
  have h := calldatasize_agreement (calldataSite site c) fuel gas room
  have size : (calldataSite site c).state.executionEnv.calldata.size = c.input.length := by
    change c.input.toArray.size = c.input.length
    exact List.size_toArray
  dsimp only at h ⊢
  rw [size] at h
  exact h

#print axioms calldatasize_agreement
#print axioms calldataSite_bytes
#print axioms calldatasize_source_input
end SolidityBridge.RoadmapV15.P10
