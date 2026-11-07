import SolidityBridge.AccessBridge.MemoryLoadExecution

/-! Actual existing P6/native images for full and physically clipped backing.
The same ordered bytes cross a word boundary; both zero guards and large
native offsets are exercised without admission or capacity restrictions. -/
namespace SolidityBridge.AccessBridge.MemoryLoadControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open Solidity.Evm.TryByteImage
private def u (n : Nat) : UInt256 := .ofNat n
private def C : Contract := {vars := []}
private def frame (pipeline : Pipeline) : FrameMem C [] where
  st := State.init C
  key := ⟨3,1,pipeline,7,lenU 1 (by decide),lenU 2 (by decide),lenU 4 (by decide)⟩
  scalar := by intro R i; cases i
  capacity := 96
  aligned := ⟨3,rfl⟩
  data := fun i => if i.val=31 then 0x12 else if i.val=32 then 0x34 else 0
  highWaterWords := 2
  resident := by decide
  zeroAbove := by
    intro i high
    rw [if_neg (by omega : i.val ≠ 31), if_neg (by omega : i.val ≠ 32)]
private def full (pipeline : Pipeline) : EvmYul.MachineState :=
  MemoryLoad.installed (frame pipeline) default

theorem full_image (pipeline : Pipeline) : FrameImage (frame pipeline) (full pipeline) :=
  MemoryLoad.installed_image _ _ (by change 64 < UInt256.size; decide +kernel)

private def clipped : EvmYul.MachineState :=
  {(default : EvmYul.MachineState) with
    activeWords := u 2
    memory := ⟨(List.replicate 31 (0 : UInt8) ++ [0x12,0x34]).toArray⟩}

theorem clipped_image (pipeline : Pipeline) : FrameImage (frame pipeline) clipped := by
  refine ⟨?_,rfl,by change 64 < UInt256.size; decide +kernel⟩
  intro address
  change (List.replicate 31 (0 : UInt8) ++ [0x12,0x34])[address]?.getD 0 =
    MemoryOps.Physical.frameBytes (frame pipeline) address
  by_cases front : address < 31
  · rw [List.getElem?_append_left (by simpa only [List.length_replicate] using front),
      List.getElem?_replicate_of_lt front]
    change (0 : UInt8) = (if h : address<96 then
      (if address=31 then 0x12 else if address=32 then 0x34 else 0) else 0)
    rw [dif_pos (by omega), if_neg (by omega), if_neg (by omega)]
  · by_cases first : address = 31
    · subst address
      change (List.replicate 31 (0 : UInt8) ++ [0x12,0x34])[31]?.getD 0 = 0x12
      decide +kernel
    · by_cases second : address = 32
      · subst address
        change (List.replicate 31 (0 : UInt8) ++ [0x12,0x34])[32]?.getD 0 = 0x34
        decide +kernel
      · rw [List.getElem?_eq_none (by
          simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil]
          omega)]
        change (0 : UInt8) = (if h : address<96 then
          (if address=31 then 0x12 else if address=32 then 0x34 else 0) else 0)
        split
        · rfl
        · rfl

private def Outcomes (native : EvmYul.MachineState) : Prop :=
  (native.mload (u 31)).1.toNat = 0x1234 * 256^30 ∧
  (native.mload (u 32)).1.toNat = 0x34 * 256^31 ∧
  (native.mload (u 33)).1.toNat = 0 ∧
  (native.mload (u 63)).1.toNat = 0 ∧
  (native.mload (u 64)).1.toNat = 0 ∧
  (native.mload (u 96)).1.toNat = 0 ∧
  (native.mload (u (2^64))).1.toNat = 0

private def pattern : Environment.Memory := fun address =>
  if address<96 then (if address=31 then 0x12 else if address=32 then 0x34 else 0) else 0

private theorem values (pipeline : Pipeline) (native : EvmYul.MachineState)
    (image : FrameImage (frame pipeline) native) : Outcomes native := by
  have agreement : ∀ offset : UInt256, (native.mload offset).1.toNat =
      ofBytesBE (Environment.readMemory (MemoryOps.Physical.frameBytes (frame pipeline)) offset.toNat 32) :=
    fun offset => MemoryLoad.payload _ _ offset image
  have physical : MemoryOps.Physical.frameBytes (frame pipeline) = pattern := by
    funext address
    rfl
  simp only [Outcomes,agreement,physical,Environment.readMemory]
  decide +kernel

theorem full_values (pipeline : Pipeline) : Outcomes (full pipeline) :=
  values pipeline _ (full_image pipeline)

theorem clipped_values (pipeline : Pipeline) : Outcomes clipped :=
  values pipeline _ (clipped_image pipeline)

theorem endian_refused (pipeline : Pipeline) :
    (clipped.mload (u 31)).1.toNat ≠ 0x3412 := by
  rw [(clipped_values pipeline).1]
  decide +kernel

theorem unchanged (pipeline : Pipeline) (offset : UInt256) :
    ((full pipeline).mload offset).2.memory = (full pipeline).memory :=
  MemoryLoad.unchanged_bytes _ _

/-- info: 'SolidityBridge.AccessBridge.MemoryLoadControls.full_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms full_image
/-- info: 'SolidityBridge.AccessBridge.MemoryLoadControls.clipped_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms clipped_image
/-- info: 'SolidityBridge.AccessBridge.MemoryLoadControls.full_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms full_values
/-- info: 'SolidityBridge.AccessBridge.MemoryLoadControls.clipped_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms clipped_values
/-- info: 'SolidityBridge.AccessBridge.MemoryLoadControls.endian_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms endian_refused
/-- info: 'SolidityBridge.AccessBridge.MemoryLoadControls.unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unchanged

private def savedTail : List UInt256 := [u 258,u 513]
private def chargedSite (pipeline : Pipeline) (gas : Nat) :
    RoadmapV15.P10.Site .MLOAD where
  seed := {(default : EVM.State) with
    toMachineState := {(full pipeline) with gasAvailable := u gas}
    stack := u 31::savedTail,execLength := 41}
  before := []
  after := []
  pcFits := by decide
private def chargedSpan (pipeline : Pipeline) : ByteSpan (frame pipeline).capacity where
  offset := lenU 31 (by decide)
  length := lenU 32 (by decide)
  fits := Or.inr (by change 31+32≤96;decide)

theorem charged_initial (pipeline : Pipeline) (gas : Nat) :
    FrameImage (frame pipeline) (chargedSite pipeline gas).state.toMachineState :=
  ⟨(full_image pipeline).bytes,(full_image pipeline).active,(full_image pipeline).wordFit⟩

/-- An actual nonzero ordered load, with both saved tail words and the reached
P6 image, at the exact gas boundary. No decoded value or run is a premise. -/
theorem charged_nonzero (pipeline : Pipeline) (fuel : Nat) :
    ∃ (reached : EVM.State) (value : UInt256),
      Assembly.driverSteps 1 (fuel+2) #[] (chargedSite pipeline 3).state=.ok reached ∧
      reached.stack=value::savedTail ∧ value.toNat=0x1234*256^30 ∧
      FrameImage (Yul.Adapters.P6ByteMemory.touch (frame pipeline) (chargedSpan pipeline))
        reached.toMachineState := by
  obtain ⟨reached,value,run,stack,payload,memory,post⟩ :=
    MemoryLoadExecution.success (frame pipeline) (chargedSite pipeline 3)
      (chargedSpan pipeline) (u 31) savedTail rfl rfl (charged_initial pipeline 3) rfl
      #[] fuel (chargedSite pipeline 3).state 3 (by cases pipeline <;> rfl)
  have read : value.toNat=((full pipeline).mload (u 31)).1.toNat :=
    payload.trans (MemoryLoad.payload _ _ _ (full_image pipeline)).symm
  refine ⟨reached,value,run,stack,read.trans (full_values pipeline).1,post.mpr ?_⟩
  change 32*max 2 ((31+32+31)/32)<UInt256.size
  decide

theorem charged_underfunded (pipeline : Pipeline) :
    FrameImage (frame pipeline) (chargedSite pipeline 2).state.toMachineState ∧
    Assembly.driverSteps 1 2 #[] (chargedSite pipeline 2).state=.error .OutOfGass := by
  refine ⟨charged_initial pipeline 2,?_⟩
  rw [MemoryCharged.load_charged]
  cases pipeline <;> rfl

/-- info: 'SolidityBridge.AccessBridge.MemoryLoadControls.charged_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms charged_initial
/-- info: 'SolidityBridge.AccessBridge.MemoryLoadControls.charged_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms charged_nonzero
/-- info: 'SolidityBridge.AccessBridge.MemoryLoadControls.charged_underfunded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms charged_underfunded
end SolidityBridge.AccessBridge.MemoryLoadControls
