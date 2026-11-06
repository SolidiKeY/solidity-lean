import Solidity.Yul.Views.RetainedCoupledFrameControls

namespace Solidity.Yul.Views.Controls

def rhChildEventState : Source.EMState agEnv [] := (Source.Locals.nil,rhCoupledRegrow.step.1.2.2)

theorem rh_child_outer_length2 : (Source.readLen (E := agEnv) packedStepFrame rhLayout.path).run rhChildEventState=(.ok 2,rhChildEventState) := by
  have header := rhCoupledRegrow.view rfl rhLayout.header List.mem_cons_self
  have read := rhLayout.readLen_view (F := packedStepFrame) rhChildEventState rhCoupledRegrow.nextRaw header
  change (Source.readLen (E := agEnv) packedStepFrame rhLayout.path).run rhChildEventState=
    (.ok (saveSlot rhCoupledRegrow.raw 0 2 rhLayout.header.slot).val,rhChildEventState) at read
  rw [rh_origin,find_saveSlot] at read
  exact read

theorem rh_child_formed1 : (Source.indexLoc (E := agEnv) packedStepFrame
    (Source.Val.storRef (τ := .array .storage (.struct .storage agNode) none) (by rfl) rhLayout.path) 1).run rhChildEventState=
      (.ok (.stor (rhLayout.path.go (.index 1))),rhChildEventState) := rhLayout.indexLoc (F := packedStepFrame) rhChildEventState 2 rh_child_outer_length2 1

def rhEvent1 := recordRetainedIndex rhLayout packedStepFrame rhChildEventState 1 rfl rh_child_formed1

def rhChildFormsAndHalts : Source.EM agEnv [] Unit := do
  let _ ← Source.indexLoc packedStepFrame (Source.Val.storRef (τ := .array .storage (.struct .storage agNode) none) (by rfl) rhLayout.path) 1
  Source.EM.halt (.revert [])

theorem rh_child_new_event_trace : RetainedSourceTrace rhLayout rhChildFormsAndHalts rhChildEventState rhHistory
    (.error (.revert []),rhChildEventState) (rhHistory++[rhEvent1]) := by
  apply RetainedSourceTrace.bindOK (RetainedSourceTrace.index packedStepFrame rhChildEventState rhHistory 1 rfl rh_child_formed1)
  exact RetainedSourceTrace.halt rhChildEventState (rhHistory++[rhEvent1]) (.revert [])

theorem rh_child_halt_restores_caller_locals : RetainedSourceTrace rhLayout
    (Source.EM.sub (Source.Locals.nil (D := agEnv.layout)) rhChildFormsAndHalts)
    (agAliases.1,rhChildEventState.2) rhHistory (.error (.revert []),(agAliases.1,rhChildEventState.2)) (rhHistory++[rhEvent1]) :=
  RetainedSourceTrace.subHalt agAliases.1 rh_child_new_event_trace

theorem rh_child_actual_halt : (Source.EM.sub (Source.Locals.nil (D := agEnv.layout)) rhChildFormsAndHalts).run
    (agAliases.1,rhChildEventState.2)=(.error (.revert []),(agAliases.1,rhChildEventState.2)) := rh_child_halt_restores_caller_locals.actual_run

/-- Formation happens while index1 is live, so no raw ownership rewrite is
needed merely for recording it. After a later shrink it WOULD remain visited. -/
theorem rh_child_record_live_selection : retainedVisitIndices (rhHistory++[rhEvent1]) 2=retainedVisitIndices rhHistory 2 := rfl

theorem rh_child_dormant_selection : retainedVisitIndices (rhHistory++[rhEvent1]) 0=[0,1] ∧ retainedVisitIndices rhHistory 0=[0] := ⟨rfl,rfl⟩

theorem rh_real_child_history_rollback : retainedRollback (retainedEnter rhCoupledPlan.after rhHistory account 0 [] false)
    rhCoupledRegrow.after (rhHistory++[rhEvent1])=(rhCoupledPlan.after,rhHistory) :=
  rhCoupledPlan.child_rollback rhCoupledRegrow rfl [rhEvent1]

theorem rh_commit_keeps_child_event : (retainedCommit (retainedEnter rhCoupledPlan.after rhHistory account 0 [] false)
    rhCoupledRegrow.after (rhHistory++[rhEvent1])).2=rhHistory++[rhEvent1] := rfl

theorem rh_enclosing_revert_restores_original_history : retainedRollback (retainedEnter rhCoupledPlan.before rhHistory account 0 [] false)
    (retainedCommit (retainedEnter rhCoupledPlan.after rhHistory account 0 [] false) rhCoupledRegrow.after (rhHistory++[rhEvent1])).1
    (retainedCommit (retainedEnter rhCoupledPlan.after rhHistory account 0 [] false) rhCoupledRegrow.after (rhHistory++[rhEvent1])).2=
      (rhCoupledPlan.before,rhHistory) := rhCoupledPlan.committed_child_outer_rollback rhCoupledRegrow rfl [rhEvent1]

def rhChildReturnsReference : Source.EM agEnv [] (Source.Val agEnv.layout (.struct .storage agNode)) := do
  let loc ← Source.indexLoc packedStepFrame (Source.Val.storRef (τ := .array .storage (.struct .storage agNode) none) (by rfl) rhLayout.path) 1
  Source.readLoc packedStepFrame loc

theorem rh_child_reference_return_trace : RetainedSourceTrace rhLayout rhChildReturnsReference rhChildEventState rhHistory
    (.ok (Source.Val.storRef (by rfl) (rhLayout.path.go (.index 1))),rhChildEventState) (rhHistory++[rhEvent1]) := by
  apply RetainedSourceTrace.bindOK (RetainedSourceTrace.index packedStepFrame rhChildEventState rhHistory 1 rfl rh_child_formed1)
  exact RetainedSourceTrace.readLoc packedStepFrame rhChildEventState (rhHistory++[rhEvent1]) (.stor (rhLayout.path.go (.index 1)))

theorem rh_child_reference_escapes_sub : RetainedSourceTrace rhLayout
    (Source.EM.sub (Source.Locals.nil (D := agEnv.layout)) rhChildReturnsReference)
    (agAliases.1,rhChildEventState.2) rhHistory
    (.ok ((Source.Val.storRef (by rfl) (rhLayout.path.go (.index 1))),Source.Locals.nil),(agAliases.1,rhChildEventState.2))
    (rhHistory++[rhEvent1]) := RetainedSourceTrace.subOK agAliases.1 rh_child_reference_return_trace

theorem rh_committed_reference_stays_visited : 1 ∈ retainedVisitIndices
    (retainedCommit (retainedEnter rhCoupledPlan.after rhHistory account 0 [] false) rhCoupledRegrow.after (rhHistory++[rhEvent1])).2 0 := by
  change 1 ∈ [0,1]
  exact List.mem_cons_of_mem _ List.mem_cons_self

end Solidity.Yul.Views.Controls
