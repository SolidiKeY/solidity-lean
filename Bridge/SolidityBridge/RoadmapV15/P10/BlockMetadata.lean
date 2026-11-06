import SolidityBridge.RoadmapV15.P10.DecoderAgreement
import Solidity.Backend.Environment.Frames

/-! Charged fetched block-metadata observations over the actual pinned driver.
The existing raw environment adapter is read only. No new machine, source
frame relation, CALL origin or Osaka approval is supplied. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

private theorem metadata_gate (valid : Array UInt256) (op : Backend.Op) (s : EVM.State)
    (allowed : op = .COINBASE ∨ op = .NUMBER ∨ op = .PREVRANDAO ∨ op = .GASLIMIT ∨ op = .BASEFEE)
    (gas : 2 ≤ s.gasAvailable.toNat) (room : s.stack.length+1 ≤ 1024) :
    Assembly.driverGate valid s (DecoderAgreement.referenceOp op) = .ok (s,2) := by
  have expansion : EVM.memoryExpansionCost s (DecoderAgreement.referenceOp op) = 0 := by
    rcases allowed with rfl|rfl|rfl|rfl|rfl <;>
      simp only [DecoderAgreement.referenceOp,EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have cost : EVM.C' s (DecoderAgreement.referenceOp op) = 2 := by
    rcases allowed with rfl|rfl|rfl|rfl|rfl <;> rfl
  have delta : EVM.δ (DecoderAgreement.referenceOp op) = some 0 := by
    rcases allowed with rfl|rfl|rfl|rfl|rfl <;> rfl
  have alpha : EVM.α (DecoderAgreement.referenceOp op) = some 1 := by
    rcases allowed with rfl|rfl|rfl|rfl|rfl <;> rfl
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [cost,delta,alpha,Option.getD_some,if_neg (Nat.not_lt_zero _),
    if_neg (Nat.not_lt_of_ge gas),Nat.sub_zero,if_neg (Nat.not_lt_of_ge room)]
  rcases allowed with rfl|rfl|rfl|rfl|rfl <;> cases s.executionEnv.perm <;> rfl

private theorem metadata_checked {op : Backend.Op} (valid : Array UInt256) (site : Site op)
    (allowed : op = .COINBASE ∨ op = .NUMBER ∨ op = .PREVRANDAO ∨ op = .GASLIMIT ∨ op = .BASEFEE) (fuel : Nat)
    (gas : 2 ≤ site.state.gasAvailable.toNat) (room : site.state.stack.length+1 ≤ 1024)
    (next : EVM.State)
    (step : EVM.step (fuel+1) 2 (some (DecoderAgreement.referenceOp op,none)) site.state = .ok next) :
    Assembly.driverSteps 1 (fuel+2) valid site.state = .ok next ∧
    EVM.X (fuel+2) valid site.state = EVM.X (fuel+1) valid next := by
  have gate := metadata_gate valid op site.state allowed gas room
  have decoded := DecoderAgreement.decode_all site
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · apply Assembly.X_continue fuel valid site.state site.state next
      (DecoderAgreement.referenceOp op,none) 2 decoded gate step
    rcases allowed with rfl|rfl|rfl|rfl|rfl <;> unfold Assembly.NonhaltingOpcode <;> decide

theorem coinbase_fetched (valid : Array UInt256) (site : Site .COINBASE) (fuel : Nat)
    (gas : 2 ≤ site.state.gasAvailable.toNat) (room : site.state.stack.length+1 ≤ 1024) :
    let next := (Assembly.chargedPrepare site.state 2).replaceStackAndIncrPC
      (UInt256.ofNat site.state.executionEnv.header.beneficiary.val :: site.state.stack)
    Assembly.driverSteps 1 (fuel+2) valid site.state = .ok next ∧
    EVM.X (fuel+2) valid site.state = EVM.X (fuel+1) valid next := by
  apply metadata_checked valid site (Or.inl rfl) fuel gas room
  rfl

theorem number_fetched (valid : Array UInt256) (site : Site .NUMBER) (fuel : Nat)
    (gas : 2 ≤ site.state.gasAvailable.toNat) (room : site.state.stack.length+1 ≤ 1024) :
    let next := (Assembly.chargedPrepare site.state 2).replaceStackAndIncrPC
      (UInt256.ofNat site.state.executionEnv.header.number :: site.state.stack)
    Assembly.driverSteps 1 (fuel+2) valid site.state = .ok next ∧
    EVM.X (fuel+2) valid site.state = EVM.X (fuel+1) valid next := by
  apply metadata_checked valid site (Or.inr (Or.inl rfl)) fuel gas room
  rfl

theorem prevrandao_fetched (valid : Array UInt256) (site : Site .PREVRANDAO) (fuel : Nat)
    (gas : 2 ≤ site.state.gasAvailable.toNat) (room : site.state.stack.length+1 ≤ 1024) :
    let next := (Assembly.chargedPrepare site.state 2).replaceStackAndIncrPC
      (site.state.executionEnv.header.prevRandao :: site.state.stack)
    Assembly.driverSteps 1 (fuel+2) valid site.state = .ok next ∧
    EVM.X (fuel+2) valid site.state = EVM.X (fuel+1) valid next := by
  apply metadata_checked valid site (Or.inr (Or.inr (Or.inl rfl))) fuel gas room
  rfl

theorem gaslimit_fetched (valid : Array UInt256) (site : Site .GASLIMIT) (fuel : Nat)
    (gas : 2 ≤ site.state.gasAvailable.toNat) (room : site.state.stack.length+1 ≤ 1024) :
    let next := (Assembly.chargedPrepare site.state 2).replaceStackAndIncrPC
      (UInt256.ofNat site.state.executionEnv.header.gasLimit :: site.state.stack)
    Assembly.driverSteps 1 (fuel+2) valid site.state = .ok next ∧
    EVM.X (fuel+2) valid site.state = EVM.X (fuel+1) valid next := by
  apply metadata_checked valid site (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) fuel gas room
  rfl

theorem basefee_fetched (valid : Array UInt256) (site : Site .BASEFEE) (fuel : Nat)
    (gas : 2 ≤ site.state.gasAvailable.toNat) (room : site.state.stack.length+1 ≤ 1024) :
    let next := (Assembly.chargedPrepare site.state 2).replaceStackAndIncrPC
      (UInt256.ofNat site.state.executionEnv.header.baseFeePerGas :: site.state.stack)
    Assembly.driverSteps 1 (fuel+2) valid site.state = .ok next ∧
    EVM.X (fuel+2) valid site.state = EVM.X (fuel+1) valid next := by
  apply metadata_checked valid site (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) fuel gas room
  rfl

/-- These native reads do not extend the existing six-opcode source slice. -/
theorem metadata_source_refusal (op : Backend.Op)
    (allowed : op = .COINBASE ∨ op = .NUMBER ∨ op = .PREVRANDAO ∨ op = .GASLIMIT ∨ op = .BASEFEE)
    (frame : Backend.Environment.Frame) (tail : List Backend.Environment.Word) :
    Backend.Environment.admittedOp op = false ∧ Backend.Environment.step frame (.op op) tail = none := by
  rcases allowed with rfl|rfl|rfl|rfl|rfl <;> exact ⟨rfl,rfl⟩

#print axioms coinbase_fetched
#print axioms number_fetched
#print axioms prevrandao_fetched
#print axioms gaslimit_fetched
#print axioms basefee_fetched
#print axioms metadata_source_refusal
end SolidityBridge.RoadmapV15.P10
