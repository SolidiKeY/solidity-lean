import Solidity.Yul.Views.ScalarFamilyControls

namespace Solidity.Yul.Views.Controls

def sfRaw33 := saveSlot sfRaw 0 33
def sfRaw1 := saveSlot sfRaw33 0 1
def sfRaw0 := saveSlot sfRaw1 0 0
def sfRaw34 := saveSlot sfRaw0 0 34

theorem sf_fill_next : sfFill.nextRaw = sfRaw33 := congrArg (fun m => saveSlot m 0 33) sf_fill_raw

theorem sf_fill_fresh : prepareScalarOwnership? packedStepFrame sfLayout sfFixed 0 33 sfState sfResidual = some sfFill := sfFill.prepare_eq

theorem sf_shrink_ready : (sfFill.following? rfl 0 1).isSome := by
  apply sfFill.following_ready rfl
  · rw [sf_fill_next]; decide
  · rw [sf_fill_next]; decide

@[irreducible]
def sfShrink : ScalarOwnershipPlan packedStepFrame sfLayout sfFixed 0 1 sfFill.step.1.2 sfFill.step.2 :=
  (sfFill.following? rfl 0 1).get sf_shrink_ready

theorem sf_shrink_next : sfShrink.nextRaw = sfRaw1 :=
  (congrArg (fun m => saveSlot m 0 1) (sfFill.following_raw sfShrink rfl)).trans (congrArg (fun m => saveSlot m 0 1) sf_fill_next)

theorem sf_shrink_map : finiteEncode sfShrink.next (sfShrink.step.1.2.2.ex.world.accounts account).storage
    (fun q => sfShrink.step.2.cells (complementKey false account q)) = some sfRaw1 :=
  (sfShrink.reencode rfl).trans (congrArg some sf_shrink_next)

theorem sf_zero_ready : (sfShrink.following? rfl 0 0).isSome := by
  apply sfShrink.following_ready rfl
  · rw [sf_shrink_next]; decide
  · rw [sf_shrink_next]; decide

@[irreducible]
def sfZero : ScalarOwnershipPlan packedStepFrame sfLayout sfFixed 0 0 sfShrink.step.1.2 sfShrink.step.2 :=
  (sfShrink.following? rfl 0 0).get sf_zero_ready

theorem sf_zero_next : sfZero.nextRaw = sfRaw0 :=
  (congrArg (fun m => saveSlot m 0 0) (sfShrink.following_raw sfZero rfl)).trans (congrArg (fun m => saveSlot m 0 0) sf_shrink_next)

theorem sf_zero_map : finiteEncode sfZero.next (sfZero.step.1.2.2.ex.world.accounts account).storage
    (fun q => sfZero.step.2.cells (complementKey false account q)) = some sfRaw0 :=
  (sfZero.reencode rfl).trans (congrArg some sf_zero_next)

theorem sf_regrow_ready : (sfZero.following? rfl 0 34).isSome := by
  apply sfZero.following_ready rfl
  · rw [sf_zero_next]; decide
  · rw [sf_zero_next]; decide

@[irreducible]
def sfRegrow : ScalarOwnershipPlan packedStepFrame sfLayout sfFixed 0 34 sfZero.step.1.2 sfZero.step.2 :=
  (sfZero.following? rfl 0 34).get sf_regrow_ready

theorem sf_regrow_next : sfRegrow.nextRaw = sfRaw34 :=
  (congrArg (fun m => saveSlot m 0 34) (sfZero.following_raw sfRegrow rfl)).trans (congrArg (fun m => saveSlot m 0 34) sf_zero_next)

theorem sf_regrow_map : finiteEncode sfRegrow.next (sfRegrow.step.1.2.2.ex.world.accounts account).storage
    (fun q => sfRegrow.step.2.cells (complementKey false account q)) = some sfRaw34 :=
  (sfRegrow.reencode rfl).trans (congrArg some sf_regrow_next)

theorem sf_actual_batch : runScalarOwnership? packedStepFrame sfLayout sfFixed [(0,33),(0,1),(0,0),(0,34)] sfState sfResidual =
    (some (.ok ()),sfRegrow.step.1.2,sfRegrow.step.2) := by
  rw [sfFill.batch_nonstatic _ rfl,sfShrink.batch_nonstatic _ rfl,sfZero.batch_nonstatic _ rfl,sfRegrow.batch_nonstatic _ rfl]
  rfl

theorem sf_length34 : (Source.readLen (E := sfEnv) packedStepFrame (sfPath "xs")).run sfRegrow.step.1.2 =
    (.ok 34,sfRegrow.step.1.2) := sfRegrow.header_readLen rfl sfXEntry rfl

theorem sf_real_child_rollback : companionRollback (companionEnter sfFill.after account account 0 [] false) sfShrink.after = sfFill.after :=
  sfFill.child_rollback sfShrink rfl

theorem sf_child_commit_outer_rollback : companionRollback (companionEnter sfFill.before account account 0 [] false)
    (companionCommit (companionEnter sfFill.after account account 0 [] false) sfShrink.after) = sfFill.before :=
  sfFill.committed_child_outer_rollback sfShrink rfl

theorem sf_failed_static_after_prefix : sfShrink.asStatic.step = ((.error (.revert []),sfFill.step.1.2),sfFill.step.2) :=
  sfShrink.static_preserves_both

theorem sf_every_H (H : Source.HeapTy) (ok : Source.MemOK sfEnv H sfState) : Source.MemOK sfEnv H sfRegrow.step.1.2 :=
  sfRegrow.MemOK H (sfZero.MemOK H (sfShrink.MemOK H (sfFill.MemOK H ok)))

end Solidity.Yul.Views.Controls
