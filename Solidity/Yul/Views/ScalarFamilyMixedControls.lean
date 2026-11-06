import Solidity.Yul.Views.ScalarFamilyFrameControls
import Solidity.Yul.Views.ScalarDynamicValues

namespace Solidity.Yul.Views.Controls

def sfMixedY := saveSlot sfRaw34 2 12
theorem sfyfill_ready : (sfRegrow.following? rfl 2 12).isSome := by
  apply sfRegrow.following_ready rfl
  · rw [sf_regrow_next]; decide
  · rw [sf_regrow_next]; decide
@[irreducible]
def sfYFill : ScalarOwnershipPlan packedStepFrame sfLayout sfFixed 2 12 sfRegrow.step.1.2 sfRegrow.step.2 :=
  (sfRegrow.following? rfl 2 12).get sfyfill_ready

theorem sfyfill_next : sfYFill.nextRaw = sfMixedY :=
  (congrArg (fun m => saveSlot m 2 12) (sfRegrow.following_raw sfYFill rfl)).trans (congrArg (fun m => saveSlot m 2 12) sf_regrow_next)

theorem sfyfill_whole_map : finiteEncode sfYFill.next (sfYFill.step.1.2.2.ex.world.accounts account).storage
    (fun q => sfYFill.step.2.cells (complementKey false account q)) = some sfMixedY :=
  (sfYFill.reencode rfl).trans (congrArg some sfyfill_next)

def sfMixedRaw := saveSlot sfMixedY 3 3
theorem sfzfill_ready : (sfYFill.following? rfl 3 3).isSome := by
  apply sfYFill.following_ready rfl
  · rw [sfyfill_next]; decide
  · rw [sfyfill_next]; decide
@[irreducible]
def sfZFill : ScalarOwnershipPlan packedStepFrame sfLayout sfFixed 3 3 sfYFill.step.1.2 sfYFill.step.2 :=
  (sfYFill.following? rfl 3 3).get sfzfill_ready

theorem sfzfill_next : sfZFill.nextRaw = sfMixedRaw :=
  (congrArg (fun m => saveSlot m 3 3) (sfYFill.following_raw sfZFill rfl)).trans (congrArg (fun m => saveSlot m 3 3) sfyfill_next)

theorem sfzfill_whole_map : finiteEncode sfZFill.next (sfZFill.step.1.2.2.ex.world.accounts account).storage
    (fun q => sfZFill.step.2.cells (complementKey false account q)) = some sfMixedRaw :=
  (sfZFill.reencode rfl).trans (congrArg some sfzfill_next)

theorem sf_mixed_MemOK : Source.MemOK sfEnv sfState.2.heap.ty sfZFill.step.1.2 :=
  sfZFill.MemOK _ (sfYFill.MemOK _ sf_regrow_MemOK)

theorem sf_mixed_full_endTx : finiteEncode sfZFill.next
    ((companionEndTx sfZFill.after).source.world.accounts account).storage
    (fun q => (companionEndTx sfZFill.after).residual.cells (complementKey false account q)) = some sfMixedRaw :=
  (sfZFill.endTx_reencode rfl).trans (congrArg some sfzfill_next)

/-- Real decoded source value, not an integer surrogate or a supplied inverse. -/
theorem sf_mixed_read (entry : {entry // entry ∈ sfLayout.scalarFamilyTrace}) (i : Nat)
    (bound : i < (sfMixedRaw ((sfLayout.scalarFamilyHeader entry).registration account).slot).val)
    (v : Source.Val sfEnv.layout (sfEnv.cellTy ((sfLayout.scalarFamilyHeader entry).elementPath i)))
    (decoded : ((sfLayout.scalarFamilyHeader entry).element sfFixed account i).codec.decode
      (((sfLayout.scalarFamilyHeader entry).element sfFixed account i).field.findWord
      (sfMixedRaw ((sfLayout.scalarFamilyHeader entry).element sfFixed account i).slot)) = some v) :
    (Source.readLoc packedStepFrame (Source.Loc.stor (τ := entry.val.2.1.ty)
      ((sfLayout.scalarFamilyHeader entry).elementPath i))).run sfZFill.step.1.2 =
      (.ok (((sfLayout.scalarFamilyHeader entry).element_type i) ▸ v),sfZFill.step.1.2) := by
  let h := sfLayout.scalarFamilyHeader entry
  have member : h.element sfFixed account i ∈ sfZFill.next := by
    change _ ∈ sfLayout.scalarFamilySnapshot sfFixed sfZFill.nextRaw
    rw [sfzfill_next]
    exact sfLayout.scalarFamily_element_member sfFixed sfMixedRaw entry i bound
  have view := sfZFill.view rfl (h.element sfFixed account i) member
  have bank := sfLayout.scalarFamily_bank_agreement sfFixed sfZFill.nextRaw _ member
  rw [sfzfill_next] at view
  exact h.read_decoded packedStepFrame sfZFill.step.1.2 sfFixed i sfMixedRaw v decoded bank view

theorem sf_actual_bool_tail :
    (Source.readLoc (E := sfEnv) packedStepFrame (Source.Loc.stor (τ := .bool) ⟨sfName "xs",[.index 33]⟩)).run sfZFill.step.1.2 =
      (.ok (.bool true),sfZFill.step.1.2) := sf_mixed_read sfXEntry 33 (by decide) (.bool true) rfl

theorem sf_actual_bytes_payload :
    (Source.readLoc (E := sfEnv) packedStepFrame (Source.Loc.stor (τ := sfBytes.ty) ⟨sfName "ys",[.index 0]⟩)).run sfZFill.step.1.2 =
      (.ok (.fixedBytes [1,2,3] rfl),sfZFill.step.1.2) := sf_mixed_read sfYEntry 0 (by decide) (.fixedBytes [1,2,3] rfl) rfl

theorem sf_actual_address :
    (Source.readLoc (E := sfEnv) packedStepFrame (Source.Loc.stor (τ := .address false) ⟨sfName "zs",[.index 0]⟩)).run sfZFill.step.1.2 =
      (.ok (.address ⟨0x1234,by decide⟩),sfZFill.step.1.2) := sf_mixed_read sfZEntry 0 (by decide) (.address ⟨0x1234,by decide⟩) rfl

end Solidity.Yul.Views.Controls
