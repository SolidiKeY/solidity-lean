import Solidity.Yul.Adapters.RawPhysicalAnyImage
import Solidity.Yul.Adapters.RawPhysicalInventoryControls

/-! Actual snapshot copying overlaps and crosses the bool/u8 cell boundary.
Every raw word is refreshed from the same reached frame, without an initial
canonical-value premise. A forward-overwrite negative loses an old source byte;
empty-copy offsets retain the existing zero-length behavior. -/
namespace Solidity.Yul.Adapters.RawPhysicalAnyImage.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open RawPhysicalInventory RawPhysicalInventory.Controls

def source (pipeline : Pipeline) : ByteSpan (stored pipeline).capacity :=
  ⟨lenU 33 (by decide),lenU 33 (by decide),Or.inr (by change 33+33≤192;decide)⟩
def destination (pipeline : Pipeline) : ByteSpan (stored pipeline).capacity :=
  ⟨lenU 34 (by decide),lenU 33 (by decide),Or.inr (by change 34+33≤192;decide)⟩
def copied (pipeline : Pipeline) := P6ByteMemory.copySnapshot (stored pipeline) (source pipeline) (destination pipeline) rfl
def updated (pipeline : Pipeline) := decode 33 clean (frameBytes (copied pipeline))

theorem whole_roundtrip (pipeline : Pipeline) :
    ∃ nextRoom : 33+32*wordCellCount (localExternalTypes ctx)≤(copied pipeline).highWaterWords*32,
      frameOf 33 (updated pipeline) (copied pipeline) nextRoom=copied pipeline ∧
      (updated pipeline).clean=clean.clean ∧ (updated pipeline).world=clean.world := by
  obtain ⟨nextRoom,identity,fields,world,_⟩ :=
    copy_transport 33 clean (stored pipeline) (room pipeline) (source pipeline) (destination pipeline) rfl
  exact ⟨nextRoom,identity,fields,world⟩

theorem source_payload (pipeline : Pipeline) :
    Environment.readMemory (encode 33 dirty (frameBytes (image pipeline))) 33 33=
      List.replicate 31 0++[2,0] := by
  cases pipeline <;> decide +kernel

theorem raw_snapshot (pipeline : Pipeline) :
    frameBytes (copied pipeline)=Environment.writeBytes
      (encode 33 dirty (frameBytes (image pipeline))) 34
      (List.replicate 31 0++[2,0]) := by
  have actual := P6ByteMemory.copy_image (stored pipeline) (source pipeline) (destination pipeline) rfl
  rw [show frameBytes (stored pipeline)=encode 33 dirty (frameBytes (image pipeline)) from frame_bytes _ _ _ _] at actual
  change frameBytes (copied pipeline)=Environment.writeBytes
    (encode 33 dirty (frameBytes (image pipeline))) 34
    (Environment.readMemory (encode 33 dirty (frameBytes (image pipeline))) 33 33) at actual
  rw [source_payload pipeline] at actual
  exact actual

theorem crossing_words (pipeline : Pipeline) :
    RawFrame.view (updated pipeline) flag=word 0 ∧
    RawFrame.view (updated pipeline) small=word (2*2^248+257) ∧
    RawFrame.view (updated pipeline) selector=word (2^255+85) := by
  dsimp only [updated]
  rw [raw_snapshot]
  cases pipeline <;> decide +kernel

theorem observed_bytes (pipeline : Pipeline) :
    frameBytes (copied pipeline) 64=0 ∧ frameBytes (copied pipeline) 65=2 ∧
    frameBytes (copied pipeline) 66=0 ∧ frameBytes (copied pipeline) 191=0xa5 ∧
    frameBytes (copied pipeline) 192=0 := by
  rw [raw_snapshot]
  cases pipeline <;> decide +kernel

/-- Two wrong forward writes demonstrate why the source must be a snapshot. -/
def wrong (pipeline : Pipeline) : Views.ByteView :=
  let erased := Environment.writeByte (frameBytes (stored pipeline)) 64 0
  Environment.writeByte erased 65 (erased 64)
theorem wrong_chronology (pipeline : Pipeline) : wrong pipeline 65≠frameBytes (copied pipeline) 65 := by
  have right := (observed_bytes pipeline).2.1
  rw [right]
  change (0 : UInt8)≠2
  decide

def emptyArea (pipeline : Pipeline) : ByteSpan (stored pipeline).capacity :=
  ⟨lenU (2^256-1) (by decide),lenU 0 (by decide),Or.inl rfl⟩
theorem empty_copy (pipeline : Pipeline) :
    P6ByteMemory.copySnapshot (stored pipeline) (emptyArea pipeline) (emptyArea pipeline) rfl=stored pipeline :=
  P6ByteMemory.copy_empty _ _ _ _ rfl

/-- Arbitrary exterior bytes are preserved even when no cell was initially
encoded. This is raw-word representation, not a canonical Source-value image. -/
theorem arbitrary_map (memory : Views.ByteView) : encode 33 (decode 33 clean memory) memory=memory :=
  encode_decode 33 clean memory
end Solidity.Yul.Adapters.RawPhysicalAnyImage.Controls
