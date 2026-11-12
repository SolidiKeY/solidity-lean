import Solidity.Yul.Adapters.RawPhysicalReturndata
import Solidity.Yul.Adapters.RawPhysicalInventoryControls
import Solidity.Source.StateExamples

/-! Strict returndata controls use a real typed world state and the existing
four-cell physical fixture. A byte at an interior position changes without
cleaning the dirty bool word. Empty source windows still check their offset.
These seeded kernel controls do not establish compiler CALL correspondence. -/
namespace Solidity.Yul.Adapters.RawPhysicalReturndata.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open RawPhysicalInventory RawPhysicalInventory.Controls
open Source.StateExamples

def entry : World.Effects D₀ LW LW := ⟨s₀,[],[17,255,51]⟩
def source : Solidity.Roadmap.Word := ⟨1,by decide⟩
def area (pipeline : Pipeline) : ByteSpan (stored pipeline).capacity :=
  ⟨lenU 34 (by decide),lenU 1 (by decide),Or.inr (by change 34+1≤192;decide)⟩
def window (pipeline : Pipeline) :
    World.returnWindow entry.returndata source.val (area pipeline).length.val.toNat=some [255] := rfl
def reached (pipeline : Pipeline) := copy (stored pipeline) (area pipeline) entry source [255] (window pipeline)
def updated (pipeline : Pipeline) := decode 33 clean (frameBytes (reached pipeline))

theorem full_transport (pipeline : Pipeline) :
    ∃ nextRoom : 33+32*wordCellCount (localExternalTypes ctx)≤(reached pipeline).highWaterWords*32,
      frameOf 33 (updated pipeline) (reached pipeline) nextRoom=reached pipeline ∧
      (updated pipeline).clean=clean.clean ∧ (updated pipeline).world=clean.world ∧
      World.copyReturndata World.TargetMemory.port entry (frameBytes (stored pipeline))
        (P6ByteMemory.wireWord (area pipeline).offset) source (P6ByteMemory.wireWord (area pipeline).length)=
        some (frameBytes (reached pipeline)) ∧
      (reached pipeline).st=(stored pipeline).st ∧ (reached pipeline).key=(stored pipeline).key :=
  transport 33 clean (stored pipeline) (room pipeline) (area pipeline) entry source [255]
    (window pipeline) (by change 34+1≤2^256;decide)

theorem exact_image (pipeline : Pipeline) :
    frameBytes (reached pipeline)=Environment.writeBytes (frameBytes (stored pipeline)) 34 [255] :=
  P6ByteMemory.write_image _ _ _ _

theorem byte_and_padding (pipeline : Pipeline) :
    frameBytes (reached pipeline) 34=255 ∧ frameBytes (reached pipeline) 32=0xa5 ∧
    frameBytes (reached pipeline) 191=0xa5 ∧ frameBytes (reached pipeline) 192=0 := by
  rw [exact_image]
  cases pipeline <;> decide +kernel

theorem raw_dirty_word (pipeline : Pipeline) :
    RawFrame.view (updated pipeline) flag=word (255*2^240+2) ∧
    RawFrame.view (updated pipeline) small=word 257 := by
  have views := RawPhysicalInterior.decode_view 33 dirty (frameBytes (image pipeline)) flag
    ⟨1,by decide⟩ 255
  have changed : RawFrame.view (updated pipeline)=
      RawFrame.view (RawFrame.write dirty flag
        (RawPhysicalInterior.wordAfter (RawFrame.view dirty flag) ⟨1,by decide⟩ 255)) := by
    change RawFrame.view (decode 33 clean (frameBytes (reached pipeline)))=_
    rw [exact_image]
    change RawFrame.view (decode 33 dirty (Views.saveByte (frameBytes (stored pipeline)) 34 255))=_
    dsimp only [stored]
    rw [frame_bytes]
    exact views
  rw [changed]
  refine ⟨?_,rfl⟩
  rw [RawFrame.read_write]
  decide

theorem no_cleaning : word (255*2^240+2)≠word 1 := by decide

theorem empty_boundary :
    World.returnWindow entry.returndata 3 0=some [] ∧
    World.returnWindow entry.returndata 4 0=none ∧
    World.returnWindow entry.returndata 2 2=none := by decide

/-- Invalid zero-size source bounds do not become a successful physical no-op. -/
theorem invalid_empty (pipeline : Pipeline) :
    World.copyReturndata World.TargetMemory.port entry (frameBytes (stored pipeline))
      ⟨34,by decide⟩ ⟨4,by decide⟩ ⟨0,by decide⟩=none :=
  World.copyReturndata_bounds _ _ _ _ _ _ (by decide)

/-- A valid empty window leaves the physical frame, including metadata, exact. -/
theorem valid_empty (pipeline : Pipeline) :
    copy (stored pipeline) ⟨lenU 34 (by decide),lenU 0 (by decide),Or.inl rfl⟩ entry
      ⟨3,by decide⟩ [] rfl=stored pipeline :=
  P6ByteMemory.write_empty _ _ _ _ rfl
end Solidity.Yul.Adapters.RawPhysicalReturndata.Controls
