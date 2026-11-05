import Solidity.Yul.Views.PackedCellUpdate
import Solidity.Yul.Views.RetainedLiveCoverageControls

/-! Actual typed Source write of a retained packed payload preserves the same
complete raw complement and unrelated logical cells. Kernel seeds only. -/
namespace Solidity.Yul.Views.Controls
open PackedCellUpdate

def pcuPath := rlcHeader.element agFixed account 0
def pcuValue := rlcHeader.elementValue agFixed account 0 42
def pcuRun := (Source.setCell packedStepFrame pcuPath.path (some pcuValue)).run rccRun.1.2

theorem pcu_view : finiteView (rccImage.snapshot rhRaw0)
    (pcuRun.2.2.ex.world.accounts account).storage (raw pcuPath pcuValue rhRaw0) :=
  source_view packedStepFrame rccRun.1.2 _ pcuPath rlc_payload ((packedSeparationCheck_iff _).mp (rai_separated .legacy)) rhRaw0 rcc_view pcuValue rfl rfl

theorem pcu_reencode : finiteEncode (rccImage.snapshot rhRaw0)
    (pcuRun.2.2.ex.world.accounts account).storage (packedMask (rccImage.snapshot rhRaw0) rhRaw0)=
      some (raw pcuPath pcuValue rhRaw0) :=
  source_reencode packedStepFrame rccRun.1.2 _ pcuPath rlc_payload ((packedSeparationCheck_iff _).mp (rai_separated .legacy)) rhRaw0 rcc_view pcuValue rfl rfl

theorem pcu_padding : packedMask (rccImage.snapshot rhRaw0) (raw pcuPath pcuValue rhRaw0)=
    packedMask (rccImage.snapshot rhRaw0) rhRaw0 := complement _ _ rlc_payload _ _

theorem pcu_raw_word : raw pcuPath pcuValue rhRaw0 2000=(⟨42+2^240,by decide⟩ : Roadmap.Word) := by decide

theorem pcu_read : (Source.readLoc packedStepFrame (.stor ((agInner 1).go (.index 0)))).run pcuRun.2=
    (.ok (Source.intWrap rcU16 42),pcuRun.2) := rfl

theorem pcu_neighbor : (Source.readLoc packedStepFrame (.stor ((agInner 0).go (.index 1)))).run pcuRun.2=
    (.ok (Source.intWrap rcU16 88),pcuRun.2) := rfl

theorem pcu_static : (Source.setCell {packedStepFrame with static:=true} pcuPath.path (some pcuValue)).run rccRun.1.2=
    (.error (.revert []),rccRun.1.2) := rfl

/-- Replacing the full slot by42 would erase a real unowned high byte. -/
theorem pcu_not_whole_slot : raw pcuPath pcuValue rhRaw0 2000≠42 := by
  rw [pcu_raw_word]
  decide
end Solidity.Yul.Views.Controls
