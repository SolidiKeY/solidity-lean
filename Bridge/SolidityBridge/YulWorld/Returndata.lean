import SolidityBridge.RoadmapV15.P10.ReturnCopyBounds
import Solidity.Yul.World.Raw

/-! VY4 consumer of the real frozen P10 charged RETURNDATACOPY step.
Successful gate and stack facts are exact target prerequisites, not source,
compiler-origin, resource abstraction or transaction adequacy. -/
namespace SolidityBridge.YulWorld.Returndata
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open SolidityBridge.RoadmapV15.P10

/-- Actual successful charged input at this exact emitted opcode site. -/
structure CopyInput (site : Site .RETURNDATACOPY) (valid : Array UInt256) where
  charged : EVM.State
  cost : Nat
  tail : Stack UInt256
  destination : UInt256
  source : UInt256
  length : UInt256
  gate : Assembly.driverGate valid site.state .RETURNDATACOPY = .ok (charged,cost)
  operands : charged.stack.pop3 = some (tail,destination,source,length)

/-- The existing reference transform; no new memory or world semantics. -/
def CopyInput.next {site valid} (input : CopyInput site valid) : EVM.State :=
  ({Assembly.chargedPrepare input.charged input.cost with
    toMachineState := (Assembly.chargedPrepare input.charged input.cost).toMachineState.returndatacopy
      input.destination input.source input.length}).replaceStackAndIncrPC input.tail

/-- Full bytes of the actual target last-return buffer; caller/source origin
remains a downstream correspondence obligation. EIP-211 bounds are strict. -/
def CopyInput.window {site valid} (input : CopyInput site valid) : Option Solidity.Roadmap.Bytes :=
  Solidity.Yul.World.returnWindow site.state.returnData.data.toList input.source.toNat input.length.toNat

/-- Inverse of the actual ordered gate. No resource, range or charge-success
fact is installed as an axiom or inferred from a requested execution result. -/
theorem accepted_bounds (valid : Array UInt256) (s charged : EVM.State) (cost : Nat)
    (accepted : Assembly.driverGate valid s .RETURNDATACOPY = .ok (charged,cost)) :
    (s.stack.getD 1 ⟨0⟩).toNat + (s.stack.getD 2 ⟨0⟩).toNat ≤ s.returnData.size ∧
      charged = returnCopyCharged s := by
  rw [return_copy_gate_classification] at accepted
  split_ifs at accepted; try cases accepted
  exact ⟨by omega,rfl⟩

theorem pop3_shape (stack tail : Stack UInt256) (destination source length : UInt256)
    (pop : stack.pop3 = some (tail,destination,source,length)) :
    stack = destination :: source :: length :: tail := by
  cases stack with
  | nil => cases pop
  | cons a rest =>
    cases rest with
    | nil => cases pop
    | cons b rest =>
      cases rest with
      | nil => cases pop
      | cons c rest =>
        simp only [Stack.pop3,Option.some.injEq,Prod.mk.injEq] at pop
        rcases pop with ⟨rfl,rfl,rfl,rfl⟩
        rfl

/-- Copy-source bounds are derived from the actual gate and operand pop,
not requested separately as an adequacy assumption. -/
theorem CopyInput.source_bound {site valid} (input : CopyInput site valid) :
    input.source.toNat + input.length.toNat ≤ site.state.returnData.size := by
  have facts := accepted_bounds valid site.state input.charged input.cost input.gate
  have operands := input.operands
  rw [facts.2] at operands
  have shape := pop3_shape site.state.stack input.tail input.destination input.source input.length operands
  have bound := facts.1
  rw [shape] at bound
  exact bound

/-- Exact copy-source bytes, including strict exact-end zero-length behavior.
This is a window/read agreement, not a destination-memory framing claim. -/
theorem CopyInput.window_admitted {site valid} (input : CopyInput site valid) :
    input.window = some ((site.state.returnData.data.toList.drop input.source.toNat).take input.length.toNat) := by
  unfold CopyInput.window Solidity.Yul.World.returnWindow
  rw [if_pos (by simpa only [Array.length_toList,ByteArray.size] using input.source_bound)]

/-- Full native successor and its copy-source window. The memory expression
is the actual reference write, not a byte-readback/padding correctness claim.
Neither compiler/source-frame origin nor universal world adequacy is inferred. -/
theorem CopyInput.agreement {site valid} (input : CopyInput site valid) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) valid site.state = .ok input.next ∧
    input.next.toState = site.state.toState ∧
    input.next.returnData = site.state.returnData ∧
    input.next.H_return = site.state.H_return ∧
    input.next.memory = ByteArray.write site.state.returnData input.source.toNat
      site.state.memory input.destination.toNat input.length.toNat ∧
    input.window = some ((site.state.returnData.data.toList.drop input.source.toNat).take input.length.toNat) := by
  have charge := (accepted_bounds valid site.state input.charged input.cost input.gate).2
  refine ⟨?_,?_,?_,?_,?_,input.window_admitted⟩
  · rw [FrozenV1.api.charged.checked_return_copy site valid fuel,input.gate]
    dsimp only
    rw [input.operands]
    rfl
  all_goals
    unfold CopyInput.next
    rw [charge]
    rfl

/-- A rejected window becomes the native range exception only after both
ordered gas checks. No Solidity revert or adapter-None equation is asserted. -/
theorem rejected_window (site : Site .RETURNDATACOPY) (valid : Array UInt256) (fuel : Nat)
    (destination source length : UInt256) (tail : Stack UInt256)
    (stack : site.state.stack = destination :: source :: length :: tail)
    (firstGas : EVM.memoryExpansionCost site.state .RETURNDATACOPY ≤ site.state.gasAvailable.toNat)
    (secondGas : EVM.C' (returnCopyCharged site.state) .RETURNDATACOPY ≤
      (returnCopyCharged site.state).gasAvailable.toNat)
    (rejected : Solidity.Yul.World.returnWindow site.state.returnData.data.toList source.toNat length.toNat = none) :
    Assembly.driverSteps 1 (fuel+2) valid site.state = .error .InvalidMemoryAccess ∧
    EVM.X (fuel+2) valid site.state = .error .InvalidMemoryAccess := by
  have outside := (Solidity.Yul.World.returnWindow_none_iff _ _ _).mp rejected
  have native : site.state.returnData.size <
      (site.state.stack.getD 1 ⟨0⟩).toNat + (site.state.stack.getD 2 ⟨0⟩).toNat := by
    rw [stack]
    simpa only [Array.length_toList,ByteArray.size] using outside
  exact (return_copy_range_refusal site valid fuel firstGas secondGas
    (by rw [stack]; simp only [List.length_cons]; omega) native).2

end SolidityBridge.YulWorld.Returndata
