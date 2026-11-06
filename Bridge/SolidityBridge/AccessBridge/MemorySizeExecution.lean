import SolidityBridge.AccessBridge.MemorySizeExecutionInterface
import SolidityBridge.AccessBridge.MemoryCharged

/-! Exact MSIZE observation of the existing P6 byte frame, reusing P10's
actual charged fetched execution and preserving its entire frame image. -/
namespace SolidityBridge.AccessBridge.MemorySizeExecution
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open Solidity.Evm.TryByteImage

theorem success {C : Contract} {Γ : Ctx} (frame : FrameMem C Γ)
    (site : RoadmapV15.P10.Site .MSIZE) (image : FrameImage frame site.state.toMachineState)
    (fuel : Nat) (gas : 2≤site.state.gasAvailable.toNat)
    (room : site.state.stack.length+1≤1024) :
    ∃ (reached : EVM.State) (value : UInt256),
      Assembly.driverSteps 1 (fuel+2) #[] site.state=.ok reached ∧
      EVM.X (fuel+2) #[] site.state=EVM.X (fuel+1) #[] reached ∧
      reached.stack=value::site.state.stack ∧ value.toNat=32*frame.highWaterWords ∧
      reached.memory=site.state.memory ∧ FrameImage frame reached.toMachineState ∧
      reached.gasAvailable=site.state.gasAvailable-UInt256.ofNat 2 ∧
      reached.pc=site.state.pc+UInt256.ofNat 1 ∧ reached.execLength=site.state.execLength+1 := by
  let value : UInt256 := site.state.toMachineState.msize
  let reached : EVM.State := (Assembly.chargedPrepare site.state 2).replaceStackAndIncrPC
    (value::site.state.stack)
  have execution := RoadmapV15.P10.msize_agreement site fuel gas room
  refine ⟨reached,value,execution.1,execution.2,rfl,?_,rfl,?_,rfl,rfl,rfl⟩
  · exact MemoryCharged.size_payload frame site.state.toMachineState image
  · exact ⟨image.bytes,image.active,image.wordFit⟩

def certificate : MemorySizeExecutionCertificate where
  toMemoryAccessCertificate := MemoryCharged.certificate
  success := success

/-- info: 'SolidityBridge.AccessBridge.MemorySizeExecution.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms success
/-- info: 'SolidityBridge.AccessBridge.MemorySizeExecution.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end SolidityBridge.AccessBridge.MemorySizeExecution
