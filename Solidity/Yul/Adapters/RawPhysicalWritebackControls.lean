import Solidity.Yul.Adapters.RawPhysicalWriteback
import Solidity.Yul.Adapters.RawPhysicalInventoryControls

/-! Whole finite-frame identity with dirty raw cells and nonzero padding.
Equal decoded word views do not determine residual bytes: rebuilding from a
zero residual is observably different and is not unchanged writeback. -/
namespace Solidity.Yul.Adapters.RawPhysicalWriteback.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open RawPhysicalInventory RawPhysicalInventory.Controls

theorem whole_frame_identity (pipeline : Pipeline) :
    frameOf 33 (restored pipeline) (stored pipeline) (room pipeline)=stored pipeline := by
  first | omega | decide | skip
  exact frame_unchanged 33 dirty (image pipeline) (room pipeline)

theorem tail_outside (cell : WordCell (localExternalTypes ctx)) :
    191<offset 33 cell ∨ offset 33 cell+32≤191 := by
  first | omega | decide | skip
  have bound := cell.slot.isLt
  change cell.slot.val<4 at bound
  unfold RawPhysicalInventory.offset
  omega

def zeroImage := encode 33 dirty (fun _=>0)
def paddedImage := encode 33 dirty (fun _=>0xa5)

theorem same_view_different_padding :
    RawFrame.view (decode 33 clean zeroImage)=RawFrame.view (decode 33 clean paddedImage) ∧
      zeroImage 191≠paddedImage 191 := by
  first | omega | decide | skip
  have zero : zeroImage 191=0 := residual 33 dirty (fun _=>0) 191 tail_outside
  have padded : paddedImage 191=0xa5 := residual 33 dirty (fun _=>0xa5) 191 tail_outside
  refine ⟨?_,?_⟩
  · exact (view_roundtrip 33 dirty (fun _=>0)).trans (view_roundtrip 33 dirty (fun _=>0xa5)).symm
  · rw [zero,padded]
    decide

theorem unchanged_map :
    encode 33 (decode 33 clean paddedImage) paddedImage=paddedImage := by
  first | omega | decide | skip
  exact unchanged 33 dirty (fun _=>0xa5)

/-- Even a correct raw word snapshot cannot justify erasing the complement. -/
theorem erased_padding_negative :
    encode 33 (decode 33 clean paddedImage) (fun _=>0)≠paddedImage := by
  first | omega | decide | skip
  intro same
  have zero := residual 33 (decode 33 clean paddedImage) (fun _=>0) 191 tail_outside
  have padded := residual 33 dirty (fun _=>0xa5) 191 tail_outside
  have byte := congrFun same 191
  rw [zero] at byte
  have bad : (0 : UInt8)=0xa5 := byte.trans padded
  exact (by decide : (0 : UInt8)≠0xa5) bad

/-- Unchanged physical writeback is valid for both pipeline frames and still
leaves the actual dirty bool/u8 words for explicit readback. -/
theorem raw_bits_still_dirty (pipeline : Pipeline) :
    RawFrame.view (restored pipeline) flag=word 2 ∧ RawFrame.view (restored pipeline) small=word 257 ∧
      RawCoherent.coherent (restored pipeline)=false :=
  ⟨(all_four pipeline).1,(all_four pipeline).2.1,dirty_not_cleaned pipeline⟩
end Solidity.Yul.Adapters.RawPhysicalWriteback.Controls
