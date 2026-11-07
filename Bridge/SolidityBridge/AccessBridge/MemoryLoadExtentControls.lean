import SolidityBridge.AccessBridge.MemoryLoadExtent

/-! Logical initial images in either pipeline, a genuine active expansion and
a fitting aligned endpoint whose raw post-active image violates wordFit.
No native allocation, charged success or Source reachability is asserted. -/
namespace SolidityBridge.AccessBridge.MemoryLoadExtentControls
open Solidity Solidity.Backend EvmYul
open Solidity.Evm.TryByteImage
private def C : Contract := {vars := []}
private def frame (pipeline : Pipeline) (words : Nat) : FrameMem C [] where
  st := State.init C
  key := ⟨3,1,pipeline,7,lenU 1 (by decide),lenU 2 (by decide),lenU 4 (by decide)⟩
  scalar := by intro R i; cases i
  capacity := words*32
  aligned := ⟨words,rfl⟩
  data := fun _ => 0
  highWaterWords := 0
  resident := by omega
  zeroAbove := by intro i high; rfl
private def native : EvmYul.MachineState := default

theorem initial_image (pipeline : Pipeline) (words : Nat) :
    FrameImage (frame pipeline words) native := by
  refine ⟨?_,rfl,by change 32*0<UInt256.size;decide⟩
  intro address
  change (([] : List UInt8)[address]?.getD 0)=_
  simp only [List.getElem?_nil,Option.getD_none]
  unfold MemoryOps.Physical.frameBytes frame
  split <;> rfl

private def smallSpan (pipeline : Pipeline) : ByteSpan (frame pipeline 3).capacity where
  offset := lenU 31 (by decide)
  length := lenU 32 (by decide)
  fits := Or.inr (by change 31+32≤3*32;decide)

theorem expansion (pipeline : Pipeline) :
    FrameImage (Yul.Adapters.P6ByteMemory.touch (frame pipeline 3) (smallSpan pipeline))
      (native.mload (.ofNat 31)).2 ∧
    (native.mload (.ofNat 31)).2.activeWords.toNat=2 ∧
    (native.mload (.ofNat 31)).2.memory=native.memory := by
  refine ⟨?_,rfl,MemoryLoad.unchanged_bytes _ _⟩
  apply (MemoryLoadExtent.post_image _ _ _ _ rfl rfl (initial_image pipeline 3)).mpr
  change 32*max 0 ((31+32+31)/32)<UInt256.size
  decide

private def endSpan (pipeline : Pipeline) :
    ByteSpan (frame pipeline (UInt256.size/32)).capacity where
  offset := lenU (UInt256.size-32) (by change UInt256.size-32<2^256;decide)
  length := lenU 32 (by decide)
  fits := Or.inr (by change (UInt256.size-32)+32≤(UInt256.size/32)*32;decide)

theorem endpoint_not_image (pipeline : Pipeline) :
    ¬FrameImage
      (Yul.Adapters.P6ByteMemory.touch (frame pipeline (UInt256.size/32)) (endSpan pipeline))
      (native.mload (.ofNat (UInt256.size-32))).2 := by
  intro post
  have fit := (MemoryLoadExtent.post_image _ _ _ _ rfl rfl
    (initial_image pipeline (UInt256.size/32))).mp post
  have bad : ¬32*(Yul.Adapters.P6ByteMemory.touch
      (frame pipeline (UInt256.size/32)) (endSpan pipeline)).highWaterWords<UInt256.size := by
    change ¬32*max 0 (((UInt256.size-32)+32+31)/32)<UInt256.size
    decide
  exact bad fit

/-- info: 'SolidityBridge.AccessBridge.MemoryLoadExtentControls.initial_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms initial_image
/-- info: 'SolidityBridge.AccessBridge.MemoryLoadExtentControls.expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms expansion
/-- info: 'SolidityBridge.AccessBridge.MemoryLoadExtentControls.endpoint_not_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms endpoint_not_image
end SolidityBridge.AccessBridge.MemoryLoadExtentControls
