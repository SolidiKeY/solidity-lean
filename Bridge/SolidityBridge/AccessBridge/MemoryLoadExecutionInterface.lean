import SolidityBridge.AccessBridge.MemoryLoadExtentInterface

/-! Additive charged MLOAD/P6 linkage. The inherited contracts retain every
original gate failure and budget. Success is derived from the actual gate,
not supplied as a run or a desired poststate. -/
namespace SolidityBridge.AccessBridge
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open Solidity.Evm.TryByteImage

structure MemoryLoadExecutionCertificate : Prop
    extends MemoryAccessCertificate, MemoryLoadExtentCertificate, MemoryLoadCertificate where
  success : ∀ {C : Contract} {Γ : Ctx} (frame : FrameMem C Γ)
    (site : RoadmapV15.P10.Site .MLOAD) (span : ByteSpan frame.capacity)
    (offset : UInt256) (tail : List UInt256),
    offset.toNat=span.offset.val.toNat → span.length.val.toNat=32 →
    FrameImage frame site.state.toMachineState → site.state.stack=offset::tail →
    ∀ (valid : Array UInt256) (fuel : Nat) (charged : EVM.State) (cost : Nat),
    Assembly.driverGate valid site.state .MLOAD=.ok (charged,cost) →
    ∃ (reached : EVM.State) (value : UInt256),
      Assembly.driverSteps 1 (fuel+2) valid site.state=.ok reached ∧
      reached.stack=value::tail ∧
      value.toNat=ofBytesBE (Environment.readMemory (MemoryOps.Physical.frameBytes frame)
        offset.toNat 32) ∧
      reached.memory=site.state.memory ∧
      (FrameImage (Yul.Adapters.P6ByteMemory.touch frame span) reached.toMachineState ↔
        32*(Yul.Adapters.P6ByteMemory.touch frame span).highWaterWords<UInt256.size)

end SolidityBridge.AccessBridge
