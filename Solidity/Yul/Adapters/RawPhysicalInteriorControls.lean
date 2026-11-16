import Solidity.Yul.Adapters.RawPhysicalInterior
import Solidity.Yul.Adapters.RawPhysicalInventoryControls

/-! A high byte of a bool's raw 32-byte word changes through actual MSTORE8.
The low byte, other cells and padding survive; input511 truncates to255 but
resulting words are not canonically cleaned. Endian and byte-bound negatives
separate this operation from a low-byte/local readback policy. -/
namespace Solidity.Yul.Adapters.RawPhysicalInterior.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Views RawPhysicalInventory RawPhysicalInventory.Controls

def index : Fin 32 := ⟨0,by decide⟩
def address : Environment.Word := lenU 33 (by decide)
def input : Environment.Word := lenU 511 (by decide)
def fit (pipeline : Pipeline) : address.val.toNat+1≤(stored pipeline).capacity := by
  change 33+1≤192
  decide
def reached (pipeline : Pipeline) := P6ByteMemory.store8 (stored pipeline) address input (fit pipeline)
def updated := RawFrame.write dirty flag (wordAfter (RawFrame.view dirty flag) index 0xff)

theorem whole_and_target (pipeline : Pipeline) (tail : List Environment.Word) :
    encode 33 updated (frameBytes (reached pipeline))=frameBytes (reached pipeline) ∧
    RawFrame.view (decode 33 dirty (frameBytes (reached pipeline)))=RawFrame.view updated ∧
    (reached pipeline).st=(image pipeline).st ∧ (reached pipeline).key=(image pipeline).key ∧
    Environment.dataStep (.op .MSTORE8) ⟨address::input::tail,frameBytes (stored pipeline)⟩=
      some ⟨tail,frameBytes (reached pipeline)⟩ :=
  store8 33 dirty (image pipeline) (room pipeline) flag index address input rfl (fit pipeline) tail

theorem high_byte_numeric : wordAfter (word 2) index 0xff=word (255*2^248+2) := by decide

theorem raw_words (pipeline : Pipeline) :
    RawFrame.view (decode 33 dirty (frameBytes (reached pipeline))) flag=word (255*2^248+2) ∧
    RawFrame.view (decode 33 dirty (frameBytes (reached pipeline))) small=word 257 ∧
    RawFrame.view (decode 33 dirty (frameBytes (reached pipeline))) selector=word (2^255+85) := by
  rw [(whole_and_target pipeline []).2.1]
  refine ⟨?_,rfl,rfl⟩
  exact (RawFrame.read_write dirty flag _).trans high_byte_numeric

theorem source_fields : updated.clean=dirty.clean ∧ updated.world=dirty.world := ⟨rfl,rfl⟩

theorem raw_padding (pipeline : Pipeline) : frameBytes (reached pipeline) 191=0xa5 := by
  dsimp only [reached]
  rw [P6ByteMemory.store8_view]
  change saveByte (frameBytes (stored pipeline)) 33 0xff 191=0xa5
  rw [find_saveByte_other _ _ (by decide)]
  exact (nonaligned_and_padding pipeline).2.2.2.2.2.2.1

theorem endian_negative : wordAfter (word 2) index 0xff≠wordAfter (word 2) ⟨31,by decide⟩ 0xff := by decide

theorem no_byte32 : ¬∃ i : Fin 32,i.val=32 := by decide

/-- MSTORE8 input truncation does not replace the raw word with255. -/
theorem no_word_cleaning : wordAfter (word 2) index 0xff≠word 255 := by decide
end Solidity.Yul.Adapters.RawPhysicalInterior.Controls
