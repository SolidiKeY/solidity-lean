import Solidity.Yul.Adapters.RawPhysicalCalldata
import Solidity.Yul.Adapters.RawPhysicalInventoryControls

/-! Real Fr.cd supplies word2. Raw physical decoding preserves it while the
actual typed bool calldata decoder refuses it and uint8 accepts it. Padding,
maximum source offsets, static reads and unchanged Source carriers remain exact.
These are kernel controls, not compiler CALLDATACOPY evidence. -/
namespace Solidity.Yul.Adapters.RawPhysicalCalldata.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open RawPhysicalInventory RawPhysicalInventory.Controls

def frame : Source.Fr :=
  {this:=1,sender:=2,value:=0,static:=true,contract:="RawInput",checked:=true,depth:=0,cd:=Source.wordBytes (word 2)}
def start : Environment.Word := lenU 0 (by decide)
def wordArea (pipeline : Pipeline) : ByteSpan (stored pipeline).capacity :=
  ⟨lenU 33 (by decide),lenU 32 (by decide),Or.inr (by change 33+32≤192;decide)⟩
def wideArea (pipeline : Pipeline) : ByteSpan (stored pipeline).capacity :=
  ⟨lenU 33 (by decide),lenU 36 (by decide),Or.inr (by change 33+36≤192;decide)⟩
def copied (pipeline : Pipeline) := P6Inputs.copyCalldata (stored pipeline) frame start (wordArea pipeline)
def updated (pipeline : Pipeline) := decode 33 clean (frameBytes (copied pipeline))

theorem whole (pipeline : Pipeline) :
    ∃ nextRoom : 33+32*wordCellCount (localExternalTypes ctx)≤(copied pipeline).highWaterWords*32,
      frameOf 33 (updated pipeline) (copied pipeline) nextRoom=copied pipeline ∧
      (updated pipeline).clean=clean.clean ∧ (updated pipeline).world=clean.world := by
  first | omega | decide | skip
  obtain ⟨nextRoom,identity,locals,world,_⟩ := transport 33 clean (stored pipeline) (room pipeline) frame start (wordArea pipeline)
  exact ⟨nextRoom,identity,locals,world⟩

theorem input_word : Source.cdWordAt frame 0=2 := by decide +kernel

theorem raw_word_two (pipeline : Pipeline) : RawFrame.view (updated pipeline) flag=word 2 := by
  first | omega | decide | skip
  have raw := copied_raw_word 33 clean (stored pipeline) frame start (wordArea pipeline) rfl flag rfl
  change RawFrame.view (updated pipeline) flag=Source.toWord (Source.cdWordAt frame 0) at raw
  rw [input_word] at raw
  exact raw

theorem bool_refusal :
    (Source.readLoc (E:=E) (Γ:=ctx.tys) frame (τ:=.bool) (.cd 0)).run (clean.clean,clean.world)=
      (.error (.revert []),(clean.clean,clean.world)) := by
  first | omega | decide | skip
  change (Source.EM.lift (Source.decodeWord E.layout (Source.cdWordAt frame 0) .bool)).run (clean.clean,clean.world)=_
  rw [input_word]
  rfl

theorem uint8_success :
    (Source.readLoc (E:=E) (Γ:=ctx.tys) frame (τ:=.int Source.IntTy.u8) (.cd 0)).run (clean.clean,clean.world)=
      (.ok (.int 2 (by decide)),(clean.clean,clean.world)) := by
  first | omega | decide | skip
  change (Source.EM.lift (Source.decodeWord E.layout (Source.cdWordAt frame 0) (.int Source.IntTy.u8))).run (clean.clean,clean.world)=_
  rw [input_word]
  rfl

theorem right_padding (pipeline : Pipeline) :
    Environment.readMemory (frameBytes (P6Inputs.copyCalldata (stored pipeline) frame start (wideArea pipeline))) 33 36=
      Source.wordBytes (word 2)++[0,0,0,0] := by
  first | omega | decide | skip
  have copied := P6Inputs.copy_readback (stored pipeline) frame start (wideArea pipeline)
  have padding : P6Inputs.callBytes frame 0 36=Source.wordBytes (word 2)++[0,0,0,0] := by decide +kernel
  exact copied.trans padding

theorem largest_source_word : Source.cdWordAt frame (2^256-1)=0 := by decide +kernel

theorem maximum_offset (pipeline : Pipeline) :
    RawFrame.view (decode 33 clean (frameBytes (P6Inputs.copyCalldata (stored pipeline) frame
      (lenU (2^256-1) (by decide)) (wordArea pipeline)))) flag=word 0 := by
  first | omega | decide | skip
  have raw := copied_raw_word 33 clean (stored pipeline) frame (lenU (2^256-1) (by decide)) (wordArea pipeline) rfl flag rfl
  change _=Source.toWord (Source.cdWordAt frame (2^256-1)) at raw
  rw [largest_source_word] at raw
  exact raw

theorem exterior (pipeline : Pipeline) : frameBytes (copied pipeline) 191=0xa5 := by
  first | omega | decide | skip
  dsimp only [copied]
  rw [P6Inputs.copy_outside _ _ _ _ 191 (Or.inr (by change 33+32≤191;decide))]
  exact (nonaligned_and_padding pipeline).2.2.2.2.2.2.1

theorem wrong_offset_and_padding :
    P6Inputs.callBytes frame 1 32≠P6Inputs.callBytes frame 0 32 ∧
    P6Inputs.callBytes frame 0 36≠[0,0,0,0]++Source.wordBytes (word 2) := by decide +kernel
end Solidity.Yul.Adapters.RawPhysicalCalldata.Controls
