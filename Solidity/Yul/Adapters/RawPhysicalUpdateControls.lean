import Solidity.Yul.Adapters.RawPhysicalUpdate
import Solidity.Yul.Adapters.RawPhysicalInventoryControls

/-! An actual nonaligned word store updates a low-width local with a full dirty
256-bit word. Other cells, external-function fields and padding survive. A
wrong-cell coordinate cannot satisfy the update's explicit placement guard. -/
namespace Solidity.Yul.Adapters.RawPhysicalUpdate.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open RawPhysicalInventory RawPhysicalInventory.Controls

def value := word (2^256-1)
def updated := RawFrame.write dirty small value
def area (pipeline : Pipeline) : WordSpan (stored pipeline).capacity :=
  ⟨lenU 65 (by decide),by change 65+32≤192;decide⟩
def reached (pipeline : Pipeline) := RawPhysical.store (stored pipeline) (area pipeline) updated small

theorem whole_and_target (pipeline : Pipeline) (tail : List Environment.Word) :
    encode 33 updated (frameBytes (reached pipeline))=frameBytes (reached pipeline) ∧
    RawFrame.view (decode 33 dirty (frameBytes (reached pipeline)))=RawFrame.view updated ∧
    (reached pipeline).st=(image pipeline).st ∧ (reached pipeline).key=(image pipeline).key ∧
    Environment.cryptoStep (.op .MSTORE)
      ⟨(area pipeline).offset::lenU value.val value.isLt::tail,frameBytes (stored pipeline)⟩=
      some ⟨tail,frameBytes (reached pipeline)⟩ :=
  store 33 dirty (image pipeline) (room pipeline) small value (area pipeline) rfl tail

theorem actual_word_bits (pipeline : Pipeline) :
    RawFrame.view (decode 33 dirty (frameBytes (reached pipeline))) small=value ∧
    RawFrame.view (decode 33 dirty (frameBytes (reached pipeline))) flag=word 2 ∧
    RawFrame.view (decode 33 dirty (frameBytes (reached pipeline))) address=word (2^256-1) ∧
    RawFrame.view (decode 33 dirty (frameBytes (reached pipeline))) selector=word (2^255+85) := by
  first | omega | decide | skip
  rw [(whole_and_target pipeline []).2.1]
  exact ⟨RawFrame.read_write dirty small value,rfl,rfl,rfl⟩

theorem source_carriers : updated.clean=dirty.clean ∧ updated.world=dirty.world := ⟨rfl,rfl⟩

theorem padding_kept (pipeline : Pipeline) : frameBytes (reached pipeline) 191=0xa5 := by
  first | omega | decide | skip
  dsimp only [reached]
  rw [RawPhysical.store_image]
  have outside : 65+32≤191 := by decide
  have unchanged := Environment.writeBytes_frame (Source.wordBytes (RawFrame.view updated small)) 65 191
    (frameBytes (stored pipeline)) (Or.inr (by rw [Source.wordBytes_length];exact outside))
  change Environment.writeBytes (frameBytes (stored pipeline)) 65 (Source.wordBytes (RawFrame.view updated small)) 191=0xa5
  rw [unchanged]
  exact (nonaligned_and_padding pipeline).2.2.2.2.2.2.1

/-- Two fields of one external-function local have different actual regions. -/
theorem function_fields_separate : offset 33 address+32≤offset 33 selector := by
  first | (simp only;done) | decide | omega | rfl

def wrongArea (pipeline : Pipeline) : WordSpan (stored pipeline).capacity :=
  ⟨lenU 33 (by decide),by change 33+32≤192;decide⟩
theorem wrong_coordinates (pipeline : Pipeline) :
    (wrongArea pipeline).offset.val.toNat≠offset 33 small := by
  first | (simp only;done) | decide | omega | rfl | skip
  change (33 : Nat)≠65
  decide

/-- Real repeated raw writes retain the latest full word and preserve the
independent function-selector overlay. No low-width cleaning is inserted. -/
theorem repeated_same_cell : RawFrame.view (RawFrame.write updated small (word 257)) small=word 257 ∧
    RawFrame.view (RawFrame.write updated small (word 257)) selector=word (2^255+85) := by
  first | omega | decide
end Solidity.Yul.Adapters.RawPhysicalUpdate.Controls
