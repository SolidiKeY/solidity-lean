import Solidity.Yul.Views.SignedDynamicControls

namespace Solidity.Yul.Views.Controls

def sdRaw17 := saveSlot sdRaw 0 17
def sdRaw1 := saveSlot sdRaw17 0 1
def sdRaw0 := saveSlot sdRaw1 0 0
def sdRaw18 := saveSlot sdRaw0 0 18

theorem sd_fill_next : sdFill.nextRaw = sdRaw17 := congrArg (fun m => saveSlot m 0 17) sd_fill_raw

theorem sd_fill_fresh : prepareIntOwnership? packedStepFrame sdLayout sdFixed 0 17 sdState sdResidual = some sdFill := sdFill.prepare_eq

theorem sd_shrink_ready : (sdFill.following? rfl 0 1).isSome := by
  apply sdFill.following_ready rfl
  · rw [sd_fill_next]; decide
  · rw [sd_fill_next]; decide

@[irreducible]
def sdShrink : IntOwnershipPlan packedStepFrame sdLayout sdFixed 0 1 sdFill.step.1.2 sdFill.step.2 :=
  (sdFill.following? rfl 0 1).get sd_shrink_ready

theorem sd_shrink_next : sdShrink.nextRaw = sdRaw1 :=
  (congrArg (fun m => saveSlot m 0 1) (sdFill.following_raw sdShrink rfl)).trans (congrArg (fun m => saveSlot m 0 1) sd_fill_next)

theorem sd_shrink_map : finiteEncode sdShrink.next (sdShrink.step.1.2.2.ex.world.accounts account).storage
    (fun q => sdShrink.step.2.cells (complementKey false account q)) = some sdRaw1 :=
  (sdShrink.reencode rfl).trans (congrArg some sd_shrink_next)

theorem sd_zero_ready : (sdShrink.following? rfl 0 0).isSome := by
  apply sdShrink.following_ready rfl
  · rw [sd_shrink_next]; decide
  · rw [sd_shrink_next]; decide

@[irreducible]
def sdZero : IntOwnershipPlan packedStepFrame sdLayout sdFixed 0 0 sdShrink.step.1.2 sdShrink.step.2 :=
  (sdShrink.following? rfl 0 0).get sd_zero_ready

theorem sd_zero_next : sdZero.nextRaw = sdRaw0 :=
  (congrArg (fun m => saveSlot m 0 0) (sdShrink.following_raw sdZero rfl)).trans (congrArg (fun m => saveSlot m 0 0) sd_shrink_next)

theorem sd_zero_map : finiteEncode sdZero.next (sdZero.step.1.2.2.ex.world.accounts account).storage
    (fun q => sdZero.step.2.cells (complementKey false account q)) = some sdRaw0 :=
  (sdZero.reencode rfl).trans (congrArg some sd_zero_next)

theorem sd_regrow_ready : (sdZero.following? rfl 0 18).isSome := by
  apply sdZero.following_ready rfl
  · rw [sd_zero_next]; decide
  · rw [sd_zero_next]; decide

@[irreducible]
def sdRegrow : IntOwnershipPlan packedStepFrame sdLayout sdFixed 0 18 sdZero.step.1.2 sdZero.step.2 :=
  (sdZero.following? rfl 0 18).get sd_regrow_ready

theorem sd_regrow_next : sdRegrow.nextRaw = sdRaw18 :=
  (congrArg (fun m => saveSlot m 0 18) (sdZero.following_raw sdRegrow rfl)).trans (congrArg (fun m => saveSlot m 0 18) sd_zero_next)

theorem sd_regrow_map : finiteEncode sdRegrow.next (sdRegrow.step.1.2.2.ex.world.accounts account).storage
    (fun q => sdRegrow.step.2.cells (complementKey false account q)) = some sdRaw18 :=
  (sdRegrow.reencode rfl).trans (congrArg some sd_regrow_next)

theorem sd_actual_batch : runIntOwnership? packedStepFrame sdLayout sdFixed [(0,17),(0,1),(0,0),(0,18)] sdState sdResidual =
    (some (.ok ()),sdRegrow.step.1.2,sdRegrow.step.2) := by
  rw [sdFill.batch_nonstatic _ rfl,sdShrink.batch_nonstatic _ rfl,sdZero.batch_nonstatic _ rfl,sdRegrow.batch_nonstatic _ rfl]
  rfl

theorem sd_length18 : (Source.readLen (E := sdEnv) packedStepFrame (sdPath "xs")).run sdRegrow.step.1.2 =
    (.ok 18,sdRegrow.step.1.2) := sdRegrow.header_readLen rfl sdXEntry rfl

theorem sd_real_child_rollback : companionRollback (companionEnter sdFill.after account account 0 [] false) sdShrink.after = sdFill.after :=
  sdFill.child_rollback sdShrink rfl

theorem sd_child_commit_outer_rollback : companionRollback (companionEnter sdFill.before account account 0 [] false)
    (companionCommit (companionEnter sdFill.after account account 0 [] false) sdShrink.after) = sdFill.before :=
  sdFill.committed_child_outer_rollback sdShrink rfl

theorem sd_failed_static_after_prefix : sdShrink.asStatic.step = ((.error (.revert []),sdFill.step.1.2),sdFill.step.2) :=
  sdShrink.static_preserves_both

theorem sd_every_H (H : Source.HeapTy) (ok : Source.MemOK sdEnv H sdState) : Source.MemOK sdEnv H sdRegrow.step.1.2 :=
  sdRegrow.MemOK H (sdZero.MemOK H (sdShrink.MemOK H (sdFill.MemOK H ok)))

end Solidity.Yul.Views.Controls
