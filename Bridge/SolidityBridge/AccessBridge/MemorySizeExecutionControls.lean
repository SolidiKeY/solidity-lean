import SolidityBridge.AccessBridge.MemorySizeExecution

/-! Inhabited either-pipeline frame, unbounded reserve and negative observation
controls. No reserved-capacity restriction or replacement interpreter. -/
namespace SolidityBridge.AccessBridge.MemorySizeExecutionControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open Solidity.Evm.TryByteImage
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
private def site : RoadmapV15.P10.Site .MSIZE :=
  ⟨{(default : EVM.State) with
    activeWords := UInt256.ofNat 2,gasAvailable := UInt256.ofNat 9
    stack := [UInt256.ofNat 258,UInt256.ofNat 513]},[],[.op .STOP],by decide⟩

theorem initial_image (pipeline : Pipeline) : FrameImage (frame pipeline) site.state.toMachineState := by
  refine ⟨?_,rfl,by change 64<UInt256.size; decide⟩
  intro address
  change 0=(if h : address<96 then (0 : UInt8) else 0)
  split <;> rfl

theorem fetched_size (pipeline : Pipeline) :
    ∃ (reached : EVM.State) (value : UInt256),
      Assembly.driverSteps 1 2 #[] site.state=.ok reached ∧ value.toNat=64 ∧
      reached.stack=value::[UInt256.ofNat 258,UInt256.ofNat 513] ∧
      FrameImage (frame pipeline) reached.toMachineState ∧ reached.gasAvailable.toNat=7 := by
  obtain ⟨reached,value,run,continuation,stack,payload,memory,image,gas,pc,count⟩ :=
    MemorySizeExecution.success (frame pipeline) site (initial_image pipeline) 0 (by decide) (by decide)
  refine ⟨reached,value,run,payload,stack,image,?_⟩
  rw [gas]
  decide

theorem arbitrary_reserve (pipeline : Pipeline) (words : Nat) :
    ∃ (reached : EVM.State) (value : UInt256),
      Assembly.driverSteps 1 2 #[] site.state=.ok reached ∧ value.toNat=64 ∧
      FrameImage (expandZero (frame pipeline) words) reached.toMachineState := by
  have image : FrameImage (expandZero (frame pipeline) words) site.state.toMachineState :=
    MemoryCharged.reserve _ _ (initial_image pipeline) words
  obtain ⟨reached,value,run,continuation,stack,payload,memory,post,gas,pc,count⟩ :=
    MemorySizeExecution.success _ site image 0 (by decide) (by decide)
  exact ⟨reached,value,run,payload,post⟩

theorem wrong_active (pipeline : Pipeline) :
    ¬FrameImage (frame pipeline) {site.state.toMachineState with activeWords := UInt256.ofNat 1} := by
  intro image
  have different : (1 : Nat)=2 := image.active
  cases different

theorem short_fuel : Assembly.driverSteps 1 1 #[] site.state=.error .OutOfFuel :=
  MemoryCharged.budget_one .MSIZE site #[]

/-- info: 'SolidityBridge.AccessBridge.MemorySizeExecutionControls.initial_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms initial_image
/-- info: 'SolidityBridge.AccessBridge.MemorySizeExecutionControls.fetched_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fetched_size
/-- info: 'SolidityBridge.AccessBridge.MemorySizeExecutionControls.arbitrary_reserve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms arbitrary_reserve
/-- info: 'SolidityBridge.AccessBridge.MemorySizeExecutionControls.wrong_active' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_active
/-- info: 'SolidityBridge.AccessBridge.MemorySizeExecutionControls.short_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_fuel
end SolidityBridge.AccessBridge.MemorySizeExecutionControls
