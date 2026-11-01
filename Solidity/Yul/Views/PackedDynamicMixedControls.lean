import Solidity.Yul.Views.PackedDynamicNegativeControls
import Solidity.Yul.Views.PackedDynamicCompatibility

namespace Solidity.Yul.Views.Controls

def pdMixedRaw := saveSlot pdRaw18 2 11

theorem pd_yfill_ready : (pdRegrow.following? rfl 2 11).isSome := by
  apply pdRegrow.following_ready rfl
  · rw [pd_regrow_next]; decide
  · rw [pd_regrow_next]; decide

@[irreducible]
def pdYFill : PackedOwnershipPlan packedStepFrame pdLayout pdFixed 2 11 pdRegrow.step.1.2 pdRegrow.step.2 :=
  (pdRegrow.following? rfl 2 11).get pd_yfill_ready

theorem pd_mixed_next : pdYFill.nextRaw = pdMixedRaw :=
  (congrArg (fun m => saveSlot m 2 11) (pdRegrow.following_raw pdYFill rfl)).trans (congrArg (fun m => saveSlot m 2 11) pd_regrow_next)

theorem pd_mixed_map : finiteEncode pdYFill.next (pdYFill.step.1.2.2.ex.world.accounts account).storage
    (fun q => pdYFill.step.2.cells (complementKey false account q)) = some pdMixedRaw :=
  (pdYFill.reencode rfl).trans (congrArg some pd_mixed_next)

theorem pd_u24_live_padding : pdYFill.step.2.cells (complementKey false account 2000) =
    ⟨0xaabb000000000000000000000000000000000000000000000000000000000000,by decide⟩ := by
  have mask := congrFun (pdYFill.complement rfl) 2000
  change _ = packedMask (pdLayout.unsignedSnapshot pdFixed pdYFill.nextRaw) pdYFill.nextRaw 2000 at mask
  rw [pd_mixed_next] at mask
  exact mask

theorem pd_u24_actual_read :
    (Source.readLoc (E := pdEnv) packedStepFrame (Source.Loc.stor (τ := .int pdU24) ⟨pdName "ys",[.index 9]⟩)).run pdYFill.step.1.2 =
      (.ok (.int 16777215 (by decide)),pdYFill.step.1.2) := by
  have member : pdY.element pdFixed account 9 ∈ pdYFill.next := by
    change _ ∈ pdLayout.unsignedSnapshot pdFixed pdYFill.nextRaw
    rw [pd_mixed_next]
    exact pdLayout.unsigned_element_member pdFixed pdMixedRaw pdYEntry 9 (by decide)
  have view := pdYFill.view rfl (pdY.element pdFixed account 9) member
  have bank := pdLayout.unsigned_bank_agreement pdFixed pdYFill.nextRaw _ member
  have read := pdY.read_element packedStepFrame pdYFill.step.1.2 pdFixed 9 pdYFill.nextRaw bank view
  rw [pd_mixed_next] at read
  exact read

theorem pd_mixed_MemOK : Source.MemOK pdEnv pdState.2.heap.ty pdYFill.step.1.2 := pdYFill.MemOK _ pd_regrow_MemOK

end Solidity.Yul.Views.Controls
