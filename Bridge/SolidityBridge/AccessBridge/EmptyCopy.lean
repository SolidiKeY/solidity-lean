import SolidityBridge.AccessBridge.EmptyCopyInterface
import SolidityBridge.AccessBridge.MemoryCharged

/-! Actual zero-length copy: no bytes or active words change for any offset.
The charged driver, gate and continuation are the existing pinned ones. -/
namespace SolidityBridge.AccessBridge.EmptyCopy
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

private theorem cast (value : UInt256) : UInt256.ofNat value.toNat=value := by
  cases value with
  | mk value =>
    change UInt256.mk (Fin.ofNat UInt256.size value.val)=UInt256.mk value
    exact congrArg UInt256.mk (Fin.ext (Nat.mod_eq_of_lt value.isLt))

theorem payload (native : EvmYul.SharedState .EVM) (destination source : UInt256) :
    native.calldatacopy destination source (UInt256.ofNat 0)=native := by
  change {native with memory := native.memory,activeWords := UInt256.ofNat native.activeWords.toNat}=native
  rw [cast]

private theorem gate (state : EVM.State) (destination source : UInt256) (tail : List UInt256)
    (stack : state.stack=destination::source::UInt256.ofNat 0::tail) (valid : Array UInt256)
    (gas : 3≤state.gasAvailable.toNat) (room : tail.length+3≤1024) :
    Assembly.driverGate valid state .CALLDATACOPY=.ok (state,3) := by
  have expansion : EVM.memoryExpansionCost state .CALLDATACOPY=0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',stack]
    change EVM.Cₘ (UInt256.ofNat state.activeWords.toNat)-EVM.Cₘ state.activeWords=0
    rw [cast,Nat.sub_self]
  have cost : EVM.C' state .CALLDATACOPY=3 := by
    cases state with
    | mk shared pc words count =>
      cases shared with
      | mk parent machine =>
        cases parent
        change words=destination::source::UInt256.ofNat 0::tail at stack
        change 3+3*((words[2]!.toNat+31)/32)=3
        rw [stack]
        simp only [List.getElem!_cons_succ,List.getElem!_cons_zero]
        rfl
  have charge : state.gasAvailable-UInt256.ofNat 0=state.gasAvailable := by
    change UInt256.mk (state.gasAvailable.val-0)=state.gasAvailable
    rw [sub_zero]
  have enough : 3≤state.stack.length := by rw [stack]; simp only [List.length_cons];omega
  have postRoom : state.stack.length-3+0≤1024 := by rw [stack];simp only [List.length_cons];omega
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [cost,EVM.δ,EVM.α,Option.getD_some,if_neg (Nat.not_lt_zero _),
    if_neg (Nat.not_lt_of_ge gas),if_neg (Nat.not_lt_of_ge enough),
    if_neg (Nat.not_lt_of_ge postRoom)]
  cases state.executionEnv.perm <;> rfl

theorem success (site : RoadmapV15.P10.Site .CALLDATACOPY) (destination source : UInt256)
    (tail : List UInt256) (stack : site.state.stack=destination::source::UInt256.ofNat 0::tail)
    (valid : Array UInt256) (fuel : Nat) (gas : 3≤site.state.gasAvailable.toNat)
    (room : tail.length+3≤1024) :
    let reached := (Assembly.chargedPrepare site.state 3).replaceStackAndIncrPC tail
    Assembly.driverSteps 1 (fuel+2) valid site.state=.ok reached ∧
    EVM.X (fuel+2) valid site.state=EVM.X (fuel+1) valid reached := by
  have admitted := gate site.state destination source tail stack valid gas room
  have execution : Assembly.driverSteps 1 (fuel+2) valid site.state=
      .ok ((Assembly.chargedPrepare site.state 3).replaceStackAndIncrPC tail) := by
    rw [MemoryCharged.copy_charged,admitted]
    dsimp only
    rw [stack]
    change (Except.ok (({Assembly.chargedPrepare site.state 3 with toSharedState :=
      (Assembly.chargedPrepare site.state 3).toSharedState.calldatacopy destination source (UInt256.ofNat 0)} :
        EVM.State).replaceStackAndIncrPC tail) : Except EVM.ExecutionException EVM.State)=_
    rw [payload]
  refine ⟨execution,?_⟩
  rw [MemoryCharged.continuation .CALLDATACOPY (by decide),execution]

theorem post_image {C : Contract} {Γ : Ctx} (frame : Solidity.Evm.TryByteImage.FrameMem C Γ)
    (native : EVM.State) (tail : List UInt256)
    (image : FrameImage frame native.toMachineState) :
    FrameImage frame ((Assembly.chargedPrepare native 3).replaceStackAndIncrPC tail).toMachineState :=
  ⟨image.bytes,image.active,image.wordFit⟩

theorem empty_touch_image {C : Contract} {Γ : Ctx} (frame : Solidity.Evm.TryByteImage.FrameMem C Γ)
    (native : EVM.State) (tail : List UInt256) (span : Solidity.Evm.TryByteImage.ByteSpan frame.capacity)
    (empty : span.length.val.toNat=0) (image : FrameImage frame native.toMachineState) :
    FrameImage (Yul.Adapters.P6ByteMemory.touch frame span)
      ((Assembly.chargedPrepare native 3).replaceStackAndIncrPC tail).toMachineState := by
  simp only [Yul.Adapters.P6ByteMemory.touch,dif_pos empty]
  exact post_image frame native tail image

def certificate : EmptyCopyCertificate where
  toMemoryAccessCertificate := MemoryCharged.certificate
  success := success

/-- info: 'SolidityBridge.AccessBridge.EmptyCopy.payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms payload
/-- info: 'SolidityBridge.AccessBridge.EmptyCopy.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms success
/-- info: 'SolidityBridge.AccessBridge.EmptyCopy.post_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms post_image
/-- info: 'SolidityBridge.AccessBridge.EmptyCopy.empty_touch_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_touch_image
/-- info: 'SolidityBridge.AccessBridge.EmptyCopy.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end SolidityBridge.AccessBridge.EmptyCopy
