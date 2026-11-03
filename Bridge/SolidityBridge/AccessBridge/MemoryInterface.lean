import SolidityBridge.AccessBridge.Interface
import Solidity.Yul.Adapters.P6ByteMemory

/-! Memory access signatures over the existing P6 frame and pinned EVM.
No reserved-capacity restriction, replacement memory or execution semantics is
introduced. The byte image covers every address, including exterior zeros.
Charged contracts retain the actual expansion charge and every gate failure.
P6 MLOAD payload and store/copy image preservation are separate, still-open
obligations. Only MSIZE has a P6 payload field in this partial interface. -/
namespace SolidityBridge.AccessBridge
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open Solidity.Evm.TryByteImage

/-- Initial physical byte/active-word representation of the existing frame.
Word fit bounds the observed active byte extent, not reserved capacity or
admitted calldata. It prevents UInt256 MSIZE multiplication from wrapping. -/
structure FrameImage {C : Contract} {Γ : Ctx} (frame : FrameMem C Γ)
    (native : EvmYul.MachineState) : Prop where
  bytes : ∀ address : Nat,
    native.memory.data.toList[address]?.getD 0 =
      MemoryOps.Physical.frameBytes frame address
  active : native.activeWords.toNat = frame.highWaterWords
  wordFit : 32 * frame.highWaterWords < UInt256.size

/-- Exact primitive access obligations, before any compiler/world adequacy.
No successful-step or sufficient-gas premise suppresses refusal branches. -/
structure MemoryAccessCertificate : Prop where
  size_payload : ∀ {C : Contract} {Γ : Ctx} (frame : FrameMem C Γ)
      (native : EvmYul.MachineState), FrameImage frame native →
    native.msize.toNat = 32 * frame.highWaterWords
  size_charged : ∀ (site : RoadmapV15.P10.Site .MSIZE)
      (valid : Array UInt256) (fuel : Nat),
    Assembly.driverSteps 1 (fuel+2) valid site.state =
      match Assembly.driverGate valid site.state .MSIZE with
      | .error error => .error error
      | .ok (charged,cost) =>
        let prepared := Assembly.chargedPrepare charged cost
        .ok (prepared.replaceStackAndIncrPC (prepared.toMachineState.msize :: charged.stack))
  load_charged : ∀ (site : RoadmapV15.P10.Site .MLOAD)
      (valid : Array UInt256) (fuel : Nat),
    Assembly.driverSteps 1 (fuel+2) valid site.state =
      match Assembly.driverGate valid site.state .MLOAD with
      | .error error => .error error
      | .ok (charged,cost) =>
        match charged.stack.pop with
        | none => .error .StackUnderflow
        | some (tail,address) =>
          let prepared := Assembly.chargedPrepare charged cost
          let (value,memory) := prepared.toMachineState.mload address
          .ok (({prepared with toMachineState := memory} : EVM.State).replaceStackAndIncrPC
            (value :: tail))
  store_charged : ∀ (site : RoadmapV15.P10.Site .MSTORE)
      (valid : Array UInt256) (fuel : Nat),
    Assembly.driverSteps 1 (fuel+2) valid site.state =
      match Assembly.driverGate valid site.state .MSTORE with
      | .error error => .error error
      | .ok (charged,cost) =>
        match charged.stack.pop2 with
        | none => .error .StackUnderflow
        | some (tail,address,value) =>
          let prepared := Assembly.chargedPrepare charged cost
          .ok (({prepared with toMachineState := prepared.toMachineState.mstore address value} :
            EVM.State).replaceStackAndIncrPC tail)
  store8_charged : ∀ (site : RoadmapV15.P10.Site .MSTORE8)
      (valid : Array UInt256) (fuel : Nat),
    Assembly.driverSteps 1 (fuel+2) valid site.state =
      match Assembly.driverGate valid site.state .MSTORE8 with
      | .error error => .error error
      | .ok (charged,cost) =>
        match charged.stack.pop2 with
        | none => .error .StackUnderflow
        | some (tail,address,value) =>
          let prepared := Assembly.chargedPrepare charged cost
          .ok (({prepared with toMachineState := prepared.toMachineState.mstore8 address value} :
            EVM.State).replaceStackAndIncrPC tail)
  copy_charged : ∀ (site : RoadmapV15.P10.Site .CALLDATACOPY)
      (valid : Array UInt256) (fuel : Nat),
    Assembly.driverSteps 1 (fuel+2) valid site.state =
      match Assembly.driverGate valid site.state .CALLDATACOPY with
      | .error error => .error error
      | .ok (charged,cost) =>
        match charged.stack.pop3 with
        | none => .error .StackUnderflow
        | some (tail,destination,source,length) =>
          let prepared := Assembly.chargedPrepare charged cost
          .ok (({prepared with toSharedState := (prepared.toSharedState.calldatacopy
            destination source length)} : EVM.State).replaceStackAndIncrPC tail)
  continuation : ∀ (op : Backend.Op),
    op ∈ [.MSIZE,.MLOAD,.MSTORE,.MSTORE8,.CALLDATACOPY] →
    ∀ (site : RoadmapV15.P10.Site op) (valid : Array UInt256) (fuel : Nat),
    EVM.X (fuel+2) valid site.state =
      match Assembly.driverSteps 1 (fuel+2) valid site.state with
      | .error error => .error error
      | .ok next => EVM.X (fuel+1) valid next
  budget_zero : ∀ (op : Backend.Op) (site : RoadmapV15.P10.Site op) (valid : Array UInt256),
    Assembly.driverSteps 1 0 valid site.state = .error .OutOfFuel
  budget_one : ∀ (op : Backend.Op) (site : RoadmapV15.P10.Site op) (valid : Array UInt256),
    Assembly.driverSteps 1 1 valid site.state = .error .OutOfFuel

end SolidityBridge.AccessBridge
