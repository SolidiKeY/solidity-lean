import SolidityBridge.AccessBridge.MemoryInterface
import SolidityBridge.RoadmapV15.P10.MachineObservation

/-! Fetched MSIZE/P6 composition from an initial frame image. Inherited
contracts retain all failure branches; success does not assume a run. -/
namespace SolidityBridge.AccessBridge
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open Solidity.Evm.TryByteImage
structure MemorySizeExecutionCertificate : Prop extends MemoryAccessCertificate where
  success : ∀ {C : Contract} {Γ : Ctx} (frame : FrameMem C Γ)
    (site : RoadmapV15.P10.Site .MSIZE), FrameImage frame site.state.toMachineState →
    ∀ (fuel : Nat), 2≤site.state.gasAvailable.toNat → site.state.stack.length+1≤1024 →
    ∃ (reached : EVM.State) (value : UInt256),
      Assembly.driverSteps 1 (fuel+2) #[] site.state=.ok reached ∧
      EVM.X (fuel+2) #[] site.state=EVM.X (fuel+1) #[] reached ∧
      reached.stack=value::site.state.stack ∧ value.toNat=32*frame.highWaterWords ∧
      reached.memory=site.state.memory ∧ FrameImage frame reached.toMachineState ∧
      reached.gasAvailable=site.state.gasAvailable-UInt256.ofNat 2 ∧
      reached.pc=site.state.pc+UInt256.ofNat 1 ∧ reached.execLength=site.state.execLength+1
end SolidityBridge.AccessBridge
