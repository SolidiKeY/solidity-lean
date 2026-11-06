import Solidity.Yul.Views.SignedDynamicBoundaryControls

namespace Solidity.Yul.Views.Controls

def sdCrossWord : Roadmap.Word := ⟨0x0000eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0000ffff80007fff,by decide⟩
def sdCrossRaw := saveSlot sdMixedRaw 1000 sdCrossWord

theorem sd_cross_ready : (sdYFill.following? rfl 1000 sdCrossWord).isSome := by
  apply sdYFill.following_ready rfl
  · rw [sd_mixed_next]; decide
  · rw [sd_mixed_next]; decide

@[irreducible]
def sdCross : IntOwnershipPlan packedStepFrame sdLayout sdFixed 1000 sdCrossWord sdYFill.step.1.2 sdYFill.step.2 :=
  (sdYFill.following? rfl 1000 sdCrossWord).get sd_cross_ready

theorem sd_cross_next : sdCross.nextRaw = sdCrossRaw :=
  (congrArg (fun m => saveSlot m 1000 sdCrossWord) (sdYFill.following_raw sdCross rfl)).trans (congrArg (fun m => saveSlot m 1000 sdCrossWord) sd_mixed_next)

theorem sd_cross_full_map : finiteEncode sdCross.next (sdCross.step.1.2.2.ex.world.accounts account).storage
    (fun q => sdCross.step.2.cells (complementKey false account q)) = some sdCrossRaw :=
  (sdCross.reencode rfl).trans (congrArg some sd_cross_next)

theorem sd_cross_read (i : Nat) (bound : i<18) :
    (Source.readLoc (E := sdEnv) packedStepFrame (Source.Loc.stor (τ := .int sdI16) ⟨sdName "xs",[.index i]⟩)).run sdCross.step.1.2 =
      (.ok ((sdX.element_type i) ▸ sdX.elementValue sdFixed account i (sdCrossRaw (sdX.element sdFixed account i).slot)),sdCross.step.1.2) := by
  have member : sdX.element sdFixed account i ∈ sdCross.next := by
    change _ ∈ sdLayout.integerSnapshot sdFixed sdCross.nextRaw
    rw [sd_cross_next]
    exact sdLayout.integer_element_member sdFixed sdCrossRaw sdXEntry i bound
  have view := sdCross.view rfl (sdX.element sdFixed account i) member
  have bank := sdLayout.integer_bank_agreement sdFixed sdCross.nextRaw _ member
  have read := sdX.read_element packedStepFrame sdCross.step.1.2 sdFixed i sdCross.nextRaw bank view
  rw [sd_cross_next] at read
  exact read

theorem sd_min_to_max_source :
    (Source.readLoc (E := sdEnv) packedStepFrame (Source.Loc.stor (τ := .int sdI16) ⟨sdName "xs",[.index 0]⟩)).run sdCross.step.1.2 =
      (.ok (.int 32767 (by decide)),sdCross.step.1.2) := sd_cross_read 0 (by decide)

theorem sd_max_to_min_source :
    (Source.readLoc (E := sdEnv) packedStepFrame (Source.Loc.stor (τ := .int sdI16) ⟨sdName "xs",[.index 1]⟩)).run sdCross.step.1.2 =
      (.ok (.int (-32768) (by decide)),sdCross.step.1.2) := sd_cross_read 1 (by decide)

theorem sd_cross_MemOK : Source.MemOK sdEnv sdState.2.heap.ty sdCross.step.1.2 := sdCross.MemOK _ sd_mixed_MemOK

end Solidity.Yul.Views.Controls
