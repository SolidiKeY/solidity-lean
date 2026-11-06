import Solidity.Yul.Views.PackedDynamicControls

namespace Solidity.Yul.Views.Controls

def pdRaw17 := saveSlot pdRaw 0 17
def pdRaw1 := saveSlot pdRaw17 0 1
def pdRaw0 := saveSlot pdRaw1 0 0
def pdRaw18 := saveSlot pdRaw0 0 18

theorem pd_fill_next : pdFill.nextRaw = pdRaw17 := congrArg (fun m => saveSlot m 0 17) pd_fill_raw

theorem pd_fill_fresh : preparePackedOwnership? packedStepFrame pdLayout pdFixed 0 17 pdState pdResidual = some pdFill := pdFill.prepare_eq

theorem pd_shrink_ready : (pdFill.following? rfl 0 1).isSome := by
  apply pdFill.following_ready rfl
  · rw [pd_fill_next]; decide
  · rw [pd_fill_next]; decide

@[irreducible]
def pdShrink : PackedOwnershipPlan packedStepFrame pdLayout pdFixed 0 1 pdFill.step.1.2 pdFill.step.2 :=
  (pdFill.following? rfl 0 1).get pd_shrink_ready

theorem pd_shrink_next : pdShrink.nextRaw = pdRaw1 :=
  (congrArg (fun m => saveSlot m 0 1) (pdFill.following_raw pdShrink rfl)).trans (congrArg (fun m => saveSlot m 0 1) pd_fill_next)

theorem pd_shrink_map : finiteEncode pdShrink.next (pdShrink.step.1.2.2.ex.world.accounts account).storage
    (fun q => pdShrink.step.2.cells (complementKey false account q)) = some pdRaw1 :=
  (pdShrink.reencode rfl).trans (congrArg some pd_shrink_next)

theorem pd_zero_ready : (pdShrink.following? rfl 0 0).isSome := by
  apply pdShrink.following_ready rfl
  · rw [pd_shrink_next]; decide
  · rw [pd_shrink_next]; decide

@[irreducible]
def pdZero : PackedOwnershipPlan packedStepFrame pdLayout pdFixed 0 0 pdShrink.step.1.2 pdShrink.step.2 :=
  (pdShrink.following? rfl 0 0).get pd_zero_ready

theorem pd_zero_next : pdZero.nextRaw = pdRaw0 :=
  (congrArg (fun m => saveSlot m 0 0) (pdShrink.following_raw pdZero rfl)).trans (congrArg (fun m => saveSlot m 0 0) pd_shrink_next)

theorem pd_zero_map : finiteEncode pdZero.next (pdZero.step.1.2.2.ex.world.accounts account).storage
    (fun q => pdZero.step.2.cells (complementKey false account q)) = some pdRaw0 :=
  (pdZero.reencode rfl).trans (congrArg some pd_zero_next)

theorem pd_regrow_ready : (pdZero.following? rfl 0 18).isSome := by
  apply pdZero.following_ready rfl
  · rw [pd_zero_next]; decide
  · rw [pd_zero_next]; decide

@[irreducible]
def pdRegrow : PackedOwnershipPlan packedStepFrame pdLayout pdFixed 0 18 pdZero.step.1.2 pdZero.step.2 :=
  (pdZero.following? rfl 0 18).get pd_regrow_ready

theorem pd_regrow_next : pdRegrow.nextRaw = pdRaw18 :=
  (congrArg (fun m => saveSlot m 0 18) (pdZero.following_raw pdRegrow rfl)).trans (congrArg (fun m => saveSlot m 0 18) pd_zero_next)

theorem pd_regrow_map : finiteEncode pdRegrow.next (pdRegrow.step.1.2.2.ex.world.accounts account).storage
    (fun q => pdRegrow.step.2.cells (complementKey false account q)) = some pdRaw18 :=
  (pdRegrow.reencode rfl).trans (congrArg some pd_regrow_next)

theorem pd_actual_batch : runPackedOwnership? packedStepFrame pdLayout pdFixed [(0,17),(0,1),(0,0),(0,18)] pdState pdResidual =
    (some (.ok ()),pdRegrow.step.1.2,pdRegrow.step.2) := by
  rw [pdFill.batch_nonstatic _ rfl,pdShrink.batch_nonstatic _ rfl,pdZero.batch_nonstatic _ rfl,pdRegrow.batch_nonstatic _ rfl]
  rfl

theorem pd_length18 : (Source.readLen (E := pdEnv) packedStepFrame (pdPath "xs")).run pdRegrow.step.1.2 =
    (.ok 18,pdRegrow.step.1.2) := pdRegrow.header_readLen rfl pdXEntry rfl

theorem pd_real_child_rollback : companionRollback (companionEnter pdFill.after account account 0 [] false) pdShrink.after = pdFill.after :=
  pdFill.child_rollback pdShrink rfl

theorem pd_child_commit_outer_rollback : companionRollback (companionEnter pdFill.before account account 0 [] false)
    (companionCommit (companionEnter pdFill.after account account 0 [] false) pdShrink.after) = pdFill.before :=
  pdFill.committed_child_outer_rollback pdShrink rfl

theorem pd_failed_static_after_prefix : pdShrink.asStatic.step = ((.error (.revert []),pdFill.step.1.2),pdFill.step.2) :=
  pdShrink.static_preserves_both

theorem pd_every_H (H : Source.HeapTy) (ok : Source.MemOK pdEnv H pdState) : Source.MemOK pdEnv H pdRegrow.step.1.2 :=
  pdRegrow.MemOK H (pdZero.MemOK H (pdShrink.MemOK H (pdFill.MemOK H ok)))

end Solidity.Yul.Views.Controls
