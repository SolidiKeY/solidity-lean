import Solidity.Yul.Views.RetainedAliasReadControls
import Solidity.Yul.Views.RetainedOwnershipFollowing

namespace Solidity.Yul.Views.Controls

theorem rh_next_raw : rhPlan.nextRaw=rhNextRaw := congrArg (fun m => saveSlot m 101 3) rh_raw_input

theorem rh_image2_ready : (prepareRetainedArrayImage? rhLayout agFixed rhHistory 2).isSome := by decide
def rhImage2 := (prepareRetainedArrayImage? rhLayout agFixed rhHistory 2).get rh_image2_ready
def rhRegrowRaw := saveSlot rhNextRaw 0 2
theorem rh_regrow_separated : packedSeparationCheck (rhImage2.snapshot rhRegrowRaw)=true := by decide
theorem rh_regrow_decoded : (finiteAccountWrite? (T := agEnv.lay) account (rhImage2.snapshot rhRegrowRaw) rhRegrowRaw).isSome := by decide

theorem rh_regrow_ready : (rhPlan.following? rfl 0 2).isSome := by
  apply rhPlan.following_ready rfl 0 2 rhImage2 (Option.get_mem rh_image2_ready)
  · rw [rh_next_raw]
    exact rh_regrow_separated
  · rw [rh_next_raw]
    exact rh_regrow_decoded
@[irreducible]
def rhRegrow := (rhPlan.following? rfl 0 2).get rh_regrow_ready

theorem rh_regrow_computed : rhPlan.following? rfl 0 2=some rhRegrow := by
  unfold rhRegrow
  exact Option.get_mem rh_regrow_ready

theorem rh_regrow_source_prepared : prepareRetainedOwnership? packedStepFrame rhLayout agFixed rhHistory 0 2
    rhPlan.step.1.2 rhPlan.step.2=some rhRegrow := rhRegrow.prepare_eq

theorem rh_regrow_raw : rhRegrow.nextRaw=rhRegrowRaw := by
  have same := rhPlan.following_raw rfl 0 2 rhRegrow rh_regrow_computed
  exact (congrArg (fun m => saveSlot m 0 2) same).trans (congrArg (fun m => saveSlot m 0 2) rh_next_raw)

theorem rh_regrow_whole_map : finiteEncode rhRegrow.next (rhRegrow.step.1.2.2.ex.world.accounts account).storage
    (fun q => rhRegrow.step.2.cells (complementKey false account q))=some rhRegrowRaw :=
  (rhRegrow.reencode rfl).trans (congrArg some rh_regrow_raw)

theorem rh_child_rollback_prefix : retainedRollback (retainedEnter rhPlan.after rhHistory account 0 [] false)
    rhRegrow.after (rhHistory++[rhEvent])=(rhPlan.after,rhHistory) := rhPlan.child_rollback rhRegrow rfl [rhEvent]

theorem rh_child_commit_outer_revert : retainedRollback (retainedEnter rhPlan.before rhHistory account 0 [] false)
    (retainedCommit (retainedEnter rhPlan.after rhHistory account 0 [] false) rhRegrow.after (rhHistory++[rhEvent])).1
    (retainedCommit (retainedEnter rhPlan.after rhHistory account 0 [] false) rhRegrow.after (rhHistory++[rhEvent])).2=
      (rhPlan.before,rhHistory) := rhPlan.committed_child_outer_rollback rhRegrow rfl [rhEvent]

theorem rh_static_after_prefix : (rhRegrow.withStatic true).subStep (Source.Locals.nil (D := agEnv.layout))=
    ((.error (.revert []),rhPlan.step.1.2),rhPlan.step.2,rhHistory) := (rhRegrow.withStatic true).sub_static _ rfl

theorem rh_persistent_endTx : (companionEndTx rhRegrow.after).source.world=rhRegrow.after.source.world ∧
    (companionEndTx rhRegrow.after).residual.cells (complementKey false account 1000)=rhRegrow.after.residual.cells (complementKey false account 1000) :=
  companionEndTx_persistent _ _ rfl

theorem rh_transient_endTx : ((companionEndTx rhRegrow.after).source.transient.cells account).read (agInner 0)=
    Source.Val.default agEnv.layout (agEnv.lay account (agInner 0)) ∧
    (companionEndTx rhRegrow.after).residual.cells (complementKey true account 101)=0 ∧
    (companionEndTx rhRegrow.after).source.journal=[] ∧ (companionEndTx rhRegrow.after).residual.journal=[] :=
  companionEndTx_transient _ _ rfl _ _

theorem rh_other_account : rhRegrow.after.source.world.accounts 2=rhPlan.step.1.2.2.ex.world.accounts 2 := rhRegrow.other_account 2 (by decide)
theorem rh_other_bank : rhRegrow.step.2.cells (complementKey true account 101)=rhPlan.step.2.cells (complementKey true account 101) :=
  rhRegrow.other_key _ (Or.inl (by decide))

end Solidity.Yul.Views.Controls
