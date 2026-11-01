import Solidity.Yul.Views.RetainedSourcePrefix

namespace Solidity.Yul.Views.Controls

theorem rh_prefix_journal_present : rhPrefixResidual.journal.length=14 := by
  change (residualRun rhBeforeResidual rhPrefixUpdates).journal.length=14
  rw [residual_journal_run]
  rfl

theorem rh_coupled_next_raw : rhCoupledPlan.nextRaw=rhNextRaw := by unfold rhCoupledPlan; rfl

theorem rh_coupled_regrow_ready : (rhCoupledPlan.following? rfl 0 2).isSome := by
  apply rhCoupledPlan.following_ready rfl 0 2 rhImage2 (Option.get_mem rh_image2_ready)
  · rw [rh_coupled_next_raw]
    exact rh_regrow_separated
  · rw [rh_coupled_next_raw]
    exact rh_regrow_decoded
@[irreducible]
def rhCoupledRegrow := (rhCoupledPlan.following? rfl 0 2).get rh_coupled_regrow_ready

theorem rh_coupled_child_prefix_rollback : retainedRollback (retainedEnter rhCoupledPlan.after rhHistory account 0 [] false)
    rhCoupledRegrow.after (rhHistory++[rhEvent])=(rhCoupledPlan.after,rhHistory) :=
  rhCoupledPlan.child_rollback rhCoupledRegrow rfl [rhEvent]

theorem rh_coupled_child_success_outer_revert : retainedRollback (retainedEnter rhCoupledPlan.before rhHistory account 0 [] false)
    (retainedCommit (retainedEnter rhCoupledPlan.after rhHistory account 0 [] false) rhCoupledRegrow.after (rhHistory++[rhEvent])).1
    (retainedCommit (retainedEnter rhCoupledPlan.after rhHistory account 0 [] false) rhCoupledRegrow.after (rhHistory++[rhEvent])).2=
      (rhCoupledPlan.before,rhHistory) := rhCoupledPlan.committed_child_outer_rollback rhCoupledRegrow rfl [rhEvent]

theorem rh_coupled_static_failure : (rhCoupledRegrow.withStatic true).subStep (Source.Locals.nil (D := agEnv.layout))=
    ((.error (.revert []),rhCoupledPlan.step.1.2),rhCoupledPlan.step.2,rhHistory) := (rhCoupledRegrow.withStatic true).sub_static _ rfl

theorem rh_after_scope_caller_prefix : rhCoupledPlan.before.source=agShrink.2.2.ex ∧ rhCoupledPlan.before.residual=rhPrefixResidual := ⟨rfl,rfl⟩

theorem rh_closed_coupled_source_run : rhClosedCaller.run agApplied.2=
    (.ok (3,agAliases.1),(Source.Locals.nil,rhCoupledPlan.step.1.2.2)) := by
  rw [rh_closed_source_run]
  have same : rhAfterCall.2=rhCoupledPlan.step.1.2.2 := congrArg (fun result => result.2.2) rh_coupled_same_source.symm
  rw [same]

end Solidity.Yul.Views.Controls
