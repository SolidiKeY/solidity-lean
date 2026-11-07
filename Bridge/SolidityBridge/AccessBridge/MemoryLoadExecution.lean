import SolidityBridge.AccessBridge.MemoryLoadExecutionInterface
import SolidityBridge.AccessBridge.MemoryLoadExtent
import SolidityBridge.AccessBridge.MemoryCharged

namespace SolidityBridge.AccessBridge.MemoryLoadExecution
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open Solidity.Evm.TryByteImage

private theorem gate_preserves (valid : Array UInt256) (initial charged : EVM.State)
    (cost : Nat) (gate : Assembly.driverGate valid initial .MLOAD=.ok (charged,cost)) :
    charged.memory=initial.memory ∧ charged.activeWords=initial.activeWords ∧
    charged.stack=initial.stack := by
  change ((let expansion := EVM.memoryExpansionCost initial .MLOAD
    if initial.gasAvailable.toNat<expansion then .error .OutOfGass else
    let paid := {initial with gasAvailable := initial.gasAvailable-UInt256.ofNat expansion}
    if paid.gasAvailable.toNat<3 then .error .OutOfGass else
    if paid.stack.length<1 then .error .StackUnderflow else
    if paid.stack.length-1+1>1024 then .error .StackOverflow else
    if (¬paid.executionEnv.perm) ∧ (false : Bool) then .error .StaticModeViolation else
    .ok (paid,3)) : Except EVM.ExecutionException (EVM.State × Nat))=
      .ok (charged,cost) at gate
  dsimp only at gate
  split at gate
  · contradiction
  · split at gate
    · contradiction
    · split at gate
      · contradiction
      · split at gate
        · contradiction
        · split at gate
          · contradiction
          · cases gate
            exact ⟨rfl,rfl,rfl⟩

theorem success : ∀ {C : Contract} {Γ : Ctx} (frame : FrameMem C Γ)
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
        32*(Yul.Adapters.P6ByteMemory.touch frame span).highWaterWords<UInt256.size) := by
  intro C Γ frame site span offset tail same length image stack valid fuel charged cost gate
  obtain ⟨memory,active,saved⟩ := gate_preserves valid site.state charged cost gate
  let prepared : EVM.State := Assembly.chargedPrepare charged cost
  have preparedImage : FrameImage frame prepared.toMachineState := by
    refine ⟨?_,?_,image.wordFit⟩
    · intro address
      change charged.memory.data.toList[address]?.getD 0=_
      rw [memory]
      exact image.bytes address
    · change charged.activeWords.toNat=frame.highWaterWords
      rw [active]
      exact image.active
  let loaded : UInt256 × EvmYul.MachineState := prepared.toMachineState.mload offset
  let reached : EVM.State :=
    ({prepared with toMachineState := loaded.2} : EVM.State).replaceStackAndIncrPC
      (loaded.1::tail)
  refine ⟨reached,loaded.1,?_,rfl,?_,?_,?_⟩
  · rw [MemoryCharged.load_charged,gate]
    dsimp only
    rw [saved,stack]
    rfl
  · exact MemoryLoad.payload frame prepared.toMachineState offset preparedImage
  · change loaded.2.memory=site.state.memory
    exact (MemoryLoad.unchanged_bytes prepared.toMachineState offset).trans memory
  · exact MemoryLoadExtent.post_image frame prepared.toMachineState span offset same length preparedImage

def certificate : MemoryLoadExecutionCertificate where
  toMemoryAccessCertificate := MemoryCharged.certificate
  toMemoryLoadExtentCertificate := MemoryLoadExtent.certificate
  toMemoryLoadCertificate := MemoryLoad.certificate
  success := success

/-- info: 'SolidityBridge.AccessBridge.MemoryLoadExecution.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms success
/-- info: 'SolidityBridge.AccessBridge.MemoryLoadExecution.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end SolidityBridge.AccessBridge.MemoryLoadExecution
