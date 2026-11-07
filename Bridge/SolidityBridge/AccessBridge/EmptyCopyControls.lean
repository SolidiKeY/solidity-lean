import SolidityBridge.AccessBridge.EmptyCopy

/-! Inhabited P6 copy, extreme offsets and protected dirty bytes. Zero length
is a family case, not a replacement claim for nonzero native writes. -/
namespace SolidityBridge.AccessBridge.EmptyCopyControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open Solidity.Evm.TryByteImage
private def u (n : Nat) : UInt256 := .ofNat n
private def tail : List UInt256 := [u 258,u 513]
private def destination : UInt256 := u (2^64)
private def source : UInt256 := u (UInt256.size-1)
private def site : RoadmapV15.P10.Site .CALLDATACOPY :=
  ⟨{(default : EVM.State) with
    activeWords := u 2,gasAvailable := u 9,stack := destination::source::u 0::tail},[],[.op .STOP],by decide⟩
private def reached : EVM.State := (Assembly.chargedPrepare site.state 3).replaceStackAndIncrPC tail
private def C : Contract := {vars := []}
private def frame (pipeline : Pipeline) : FrameMem C [] where
  st := State.init C
  key := ⟨3,1,pipeline,7,lenU 1 (by decide),lenU 2 (by decide),lenU 4 (by decide)⟩
  scalar := by intro R i; cases i
  capacity := 96
  aligned := ⟨3,rfl⟩
  data := fun _ => 0
  highWaterWords := 2
  resident := by decide
  zeroAbove := by intro i high; rfl

theorem extreme_execution : Assembly.driverSteps 1 2 #[] site.state=.ok reached ∧
    EVM.X 2 #[] site.state=EVM.X 1 #[] reached :=
  EmptyCopy.success site destination source tail rfl #[] 0 (by decide) (by decide)

theorem accounting : reached.gasAvailable.toNat=6 ∧ reached.activeWords.toNat=2 ∧
    reached.stack=tail ∧ reached.memory=site.state.memory ∧ reached.pc.toNat=1 := by decide

theorem initial_image (pipeline : Pipeline) : FrameImage (frame pipeline) site.state.toMachineState := by
  refine ⟨?_,rfl,by change 64<UInt256.size;decide⟩
  intro address
  change 0=(if h : address<96 then (0 : UInt8) else 0)
  split <;> rfl

theorem reached_image (pipeline : Pipeline) : FrameImage (frame pipeline) reached.toMachineState :=
  EmptyCopy.post_image _ _ tail (initial_image pipeline)

private def dirty : RoadmapV15.P10.Site .CALLDATACOPY :=
  {site with seed := {site.seed with memory := ⟨#[0xaa,0xbb]⟩}}

theorem dirty_execution :
    Assembly.driverSteps 1 2 #[] dirty.state=
      .ok ((Assembly.chargedPrepare dirty.state 3).replaceStackAndIncrPC tail) :=
  (EmptyCopy.success dirty destination source tail rfl #[] 0 (by decide) (by decide)).1

private def lowGas : RoadmapV15.P10.Site .CALLDATACOPY :=
  {site with seed := {site.seed with gasAvailable := u 2}}

theorem gas_refusal : Assembly.driverSteps 1 2 #[] lowGas.state=.error .OutOfGass := by
  rw [MemoryCharged.copy_charged]
  rfl

theorem short_fuel : Assembly.driverSteps 1 1 #[] site.state=.error .OutOfFuel :=
  MemoryCharged.budget_one .CALLDATACOPY site #[]

/-- info: 'SolidityBridge.AccessBridge.EmptyCopyControls.extreme_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms extreme_execution
/-- info: 'SolidityBridge.AccessBridge.EmptyCopyControls.accounting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accounting
/-- info: 'SolidityBridge.AccessBridge.EmptyCopyControls.initial_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms initial_image
/-- info: 'SolidityBridge.AccessBridge.EmptyCopyControls.reached_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reached_image
/-- info: 'SolidityBridge.AccessBridge.EmptyCopyControls.dirty_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dirty_execution
/-- info: 'SolidityBridge.AccessBridge.EmptyCopyControls.gas_refusal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gas_refusal
/-- info: 'SolidityBridge.AccessBridge.EmptyCopyControls.short_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_fuel
end SolidityBridge.AccessBridge.EmptyCopyControls
