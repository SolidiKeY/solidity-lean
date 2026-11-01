import Solidity.Yul.Views.RetainedLocationProducers
import Solidity.Yul.Views.RetainedTupleControls

namespace Solidity.Yul.Views.Controls

def rlPath := (agInner 0).go (.index 0)
def rlLoc : Source.Loc agEnv.layout [] (.int rcU16) := .stor rlPath
def rlEmpty : Source.EMState agEnv [] := (.nil,agShrink.2.2)
def rlProduce : Source.EM agEnv [] (Source.Loc agEnv.layout [] (.int rcU16)) :=
  Source.indexLoc packedStepFrame rtAlias 0

theorem rl_actual_location : rlProduce.run rlEmpty=(.ok rlLoc,rlEmpty) := rfl
theorem rl_actual_scalar : (Source.readLoc packedStepFrame rlLoc).run rlEmpty=
    (.ok (Source.intWrap rcU16 77),rlEmpty) := rfl

def rlFirst := captureLocationRun packedStepFrame [] rlProduce rlEmpty
def rlSecond := captureLocationRun packedStepFrame rlFirst.2 rlProduce rlFirst.1.2

theorem rl_two_actual_producers : rlFirst.1=(.ok rlLoc,rlEmpty) ∧ rlSecond.1=(.ok rlLoc,rlEmpty) := ⟨rfl,rfl⟩
theorem rl_two_paths : scopedEntryIndices rhLayout rlSecond.2=[0,0] := rfl
theorem rl_dormant_dedup : capturedVisitIndices rhLayout [] rlSecond.2 0=[0] := rfl
theorem rl_value_only_loses : scopedEntryIndices rhLayout
    (captureValueRun packedStepFrame [] (Source.readLoc packedStepFrame rlLoc) rlEmpty).2=[] := rfl

def rlAfter : Source.Loc agEnv.layout [] (.int rcU16) → Source.EM agEnv [] (Source.RVal agEnv.layout (.int rcU16)) :=
  fun _ => Source.EM.halt (.revert [7,8])

theorem rl_late_error : (captureLocationBindRun packedStepFrame [] rlProduce rlAfter rlEmpty).1=
    (.error (.revert [7,8]),rlEmpty) := rfl
theorem rl_late_keeps : scopedEntryIndices rhLayout
    (captureLocationBindRun packedStepFrame [] rlProduce rlAfter rlEmpty).2=[0] := rfl

theorem rl_saved_caller : scopedEntryIndices rhLayout
    (captureSubLocationRun packedStepFrame [] agAliases.1 Source.Locals.nil rlProduce agShrink.2.2).2=[0,0,0] := rfl

def rlTarget : Source.RLVal agEnv [agAliasTy,agAliasTy] (.int rcU16) :=
  .indexArray (.local .here) (by decide) (.const (Source.Q.ofInt 0)) (by decide)
def rlRhs : Source.RExpr agEnv [agAliasTy,agAliasTy] (.int rcU16) :=
  .indexArray (.local .here) (.const (Source.Q.ofInt 0)) (by decide)

theorem rl_actual_evalLoc (G : Source.Glob agEnv) :
    (Source.evalLoc G packedStepFrame 4 rlTarget).run agShrink.2=
      (.ok (.stor rlPath),agShrink.2) := rfl

theorem rl_assignment_target (G : Source.Glob agEnv) :
    locationScope packedStepFrame (Source.Loc.stor (Γ := [agAliasTy,agAliasTy]) (τ := .int rcU16) rlPath) ∈
      (captureAssignmentRun G packedStepFrame 5 rlTarget rlRhs [] agShrink.2).2 :=
  captureAssignmentRun_target G packedStepFrame 4 rlTarget rlRhs [] agShrink.2 agShrink.2 agShrink.2
    (.val (Source.intWrap rcU16 77)) (.stor rlPath) rfl rfl

theorem rl_actual_assignment_source (G : Source.Glob agEnv) :
    (captureAssignmentRun G packedStepFrame 5 rlTarget rlRhs [] agShrink.2).1=
      (Source.evalE G packedStepFrame 5 (.assign rlTarget rlRhs)).run agShrink.2 :=
  captureAssignmentRun_source G packedStepFrame 5 rlTarget rlRhs [] agShrink.2

theorem rl_wrong_account : scopedEntryIndices rhLayout [⟨⟨2,by decide⟩,[rlPath]⟩]=[] := rfl
theorem rl_wrong_root : entryPathIndex (agName "wrong") rlPath=none := rfl
theorem rl_erased_history : capturedVisitIndices rhLayout [] [] 0 ≠ capturedVisitIndices rhLayout [] rlSecond.2 0 := by decide
theorem rl_local_is_not_path : locationStoragePaths (Source.Loc.local (D := agEnv.layout) (Source.Idx.here (Γ := []) (τ := agAliasTy)))=[] := rfl

theorem rl_visit_compat (n : Nat) : capturedVisitIndices rhLayout [] rlSecond.2 n=capturedVisitIndices rhLayout [] reScopes n := rfl

def rlPlan : CapturedOwnershipPlan packedStepFrame rhLayout agFixed [] rlSecond.2 101 3 agShrink.2 rhPrefixResidual :=
  {oldLength := rePlan.oldLength
   lengthComputed := rePlan.lengthComputed
   oldImage := ⟨rePlan.oldImage.elements,by rw [rl_visit_compat]; exact rePlan.oldImage.computed⟩
   oldImageComputed := CapturedArrayImage.prepared _
   old := rePlan.old
   oldComputed := rePlan.oldComputed
   raw := rePlan.raw
   encoded := rePlan.encoded
   oldChecked := rePlan.oldChecked
   nextImage := ⟨rePlan.nextImage.elements,by rw [rl_visit_compat]; exact rePlan.nextImage.computed⟩
   nextImageComputed := CapturedArrayImage.prepared _
   nextChecked := rePlan.nextChecked
   sourceOp := rePlan.sourceOp
   prepared := rePlan.prepared}

theorem rl_same_actual_source_map : rlPlan.step=rePlan.step := rfl
theorem rl_reencode : finiteEncode rlPlan.next (rlPlan.step.1.2.2.ex.world.accounts account).storage
    (fun q => rlPlan.step.2.cells (complementKey false account q))=some rlPlan.nextRaw := rlPlan.reencode rfl

theorem rl_every_H (H) (ok : Source.MemOK agEnv H agShrink.2) : Source.MemOK agEnv H rlPlan.step.1.2 := rlPlan.MemOK H ok

theorem rl_whole_rollback :
    (companionRollback (companionEnter rlPlan.before account account 0 [] false) rlPlan.after,rlSecond.2)=
      (rlPlan.before,rlSecond.2) := rlPlan.rollback rfl

theorem rl_assignment_value (G : Source.Glob agEnv) :
    (captureAssignmentRun G packedStepFrame 5 rlTarget rlRhs [] agShrink.2).1.1=
      .ok (.val (Source.intWrap rcU16 77)) := rfl

theorem rl_static_assignment (G : Source.Glob agEnv) :
    (captureAssignmentRun G {packedStepFrame with static:=true} 5 rlTarget rlRhs [] agShrink.2).1=
      (.error (.revert []),agShrink.2) := rfl

theorem rl_inc_pre_value (G : Source.Glob agEnv) :
    (captureIncDecRun G packedStepFrame 5 true true rlTarget [] agShrink.2).1.1=
      .ok (.val (Source.intWrap rcU16 78)) := rfl

theorem rl_inc_post_value (G : Source.Glob agEnv) :
    (captureIncDecRun G packedStepFrame 5 true false rlTarget [] agShrink.2).1.1=
      .ok (.val (Source.intWrap rcU16 77)) := rfl

theorem rl_delete_target (G : Source.Glob agEnv) :
    locationScope packedStepFrame (Source.Loc.stor (Γ := [agAliasTy,agAliasTy]) (τ := .int rcU16) rlPath) ∈
      (captureDeleteRun G packedStepFrame 5 rlTarget [] agShrink.2).2 :=
  captureDeleteRun_target G packedStepFrame 4 rlTarget [] agShrink.2 agShrink.2 (.stor rlPath) rfl

theorem rl_static_delete (G : Source.Glob agEnv) :
    (captureDeleteRun G {packedStepFrame with static:=true} 5 rlTarget [] agShrink.2).1=
      (.error (.revert []),agShrink.2) := rfl

/-- At owner horizon1 the RHS times out and no target is observed. This
checks failure capture only; at this horizon evalLoc would also time out. -/
theorem rl_rhs_failure_no_target (G : Source.Glob agEnv) :
    rlPath ∉ (captureAssignmentRun G packedStepFrame 1 rlTarget rlRhs [] agShrink.2).2.flatMap EntryReferenceScope.paths := by
  change rlPath ∉ [agInner 0,agInner 0,agInner 0,agInner 0]
  decide

end Solidity.Yul.Views.Controls
