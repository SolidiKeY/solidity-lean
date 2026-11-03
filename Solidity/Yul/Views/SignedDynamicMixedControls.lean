import Solidity.Yul.Views.SignedDynamicNegativeControls
import Solidity.Yul.Views.IntDynamicCompatibility

namespace Solidity.Yul.Views.Controls

def sdMixedRaw := saveSlot sdRaw18 2 11

theorem sd_yfill_ready : (sdRegrow.following? rfl 2 11).isSome := by
  apply sdRegrow.following_ready rfl
  · rw [sd_regrow_next]; decide
  · rw [sd_regrow_next]; decide

@[irreducible]
def sdYFill : IntOwnershipPlan packedStepFrame sdLayout sdFixed 2 11 sdRegrow.step.1.2 sdRegrow.step.2 :=
  (sdRegrow.following? rfl 2 11).get sd_yfill_ready

theorem sd_mixed_next : sdYFill.nextRaw = sdMixedRaw :=
  (congrArg (fun m => saveSlot m 2 11) (sdRegrow.following_raw sdYFill rfl)).trans (congrArg (fun m => saveSlot m 2 11) sd_regrow_next)

theorem sd_mixed_map : finiteEncode sdYFill.next (sdYFill.step.1.2.2.ex.world.accounts account).storage
    (fun q => sdYFill.step.2.cells (complementKey false account q)) = some sdMixedRaw :=
  (sdYFill.reencode rfl).trans (congrArg some sd_mixed_next)

theorem sd_i24_live_padding : sdYFill.step.2.cells (complementKey false account 2000) =
    ⟨0xaabb000000000000000000000000000000000000000000000000000000000000,by decide⟩ := by
  have mask := congrFun (sdYFill.complement rfl) 2000
  change _ = packedMask (sdLayout.integerSnapshot sdFixed sdYFill.nextRaw) sdYFill.nextRaw 2000 at mask
  rw [sd_mixed_next] at mask
  exact mask

theorem sd_i24_actual_read :
    (Source.readLoc (E := sdEnv) packedStepFrame (Source.Loc.stor (τ := .int sdI24) ⟨sdName "ys",[.index 9]⟩)).run sdYFill.step.1.2 =
      (.ok (.int (-8388608) (by decide)),sdYFill.step.1.2) := by
  have member : sdY.element sdFixed account 9 ∈ sdYFill.next := by
    change _ ∈ sdLayout.integerSnapshot sdFixed sdYFill.nextRaw
    rw [sd_mixed_next]
    exact sdLayout.integer_element_member sdFixed sdMixedRaw sdYEntry 9 (by decide)
  have view := sdYFill.view rfl (sdY.element sdFixed account 9) member
  have bank := sdLayout.integer_bank_agreement sdFixed sdYFill.nextRaw _ member
  have read := sdY.read_element packedStepFrame sdYFill.step.1.2 sdFixed 9 sdYFill.nextRaw bank view
  rw [sd_mixed_next] at read
  exact read

theorem sd_mixed_MemOK : Source.MemOK sdEnv sdState.2.heap.ty sdYFill.step.1.2 := sdYFill.MemOK _ sd_regrow_MemOK

end Solidity.Yul.Views.Controls
