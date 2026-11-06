import Solidity.Yul.Views.RetainedEntryFrame
import Solidity.Yul.Views.RetainedChildEventControls

namespace Solidity.Yul.Views.Controls

def reScopes : List (EntryReferenceScope agEnv) := [entryLocalScope packedStepFrame agAliases.1]

theorem re_entry_complete : scopedEntryIndices rhLayout reScopes=[0,0] := rfl
theorem re_entry_no_events : capturedVisitIndices rhLayout [] reScopes 0=[0] := rfl
theorem re_missing_entry : capturedVisitIndices rhLayout [] [] 0=[] := rfl
theorem re_foreign_account : scopedEntryIndices rhLayout [⟨⟨2,by decide⟩,[agInner 0]⟩]=[] := rfl
theorem re_wrong_root : entryPathIndex (agName "other") (agInner 0)=none := rfl
theorem re_outer_only : entryPathIndex rhLayout.root rhLayout.path=none := rfl

/-- No successful index event is fabricated from incoming references. The
ordinary child packer computes precisely the same physical child for these
entry values even though the current ancestor length is zero. -/
def reImage : CapturedArrayImage rhLayout agFixed [] reScopes 0 :=
  ⟨rhImage.elements,rhImage.computed⟩

theorem re_snapshot_same : reImage.snapshot rhRaw0=rhImage.snapshot rhRaw0 := rfl

theorem re_visit_compat (n : Nat) : capturedVisitIndices rhLayout [] reScopes n=retainedVisitIndices rhHistory n := by
  change uniqueVisitIndices [] ((List.range n ++ []) ++ [0,0])=uniqueVisitIndices [] (List.range n ++ [0,0])
  rw [List.append_nil]

def rePlan : CapturedOwnershipPlan packedStepFrame rhLayout agFixed [] reScopes 101 3 agShrink.2 rhPrefixResidual :=
  {oldLength := rhCoupledPlan.oldLength
   lengthComputed := rhCoupledPlan.lengthComputed
   oldImage := ⟨rhCoupledPlan.oldImage.elements,by rw [re_visit_compat]; exact rhCoupledPlan.oldImage.computed⟩
   oldImageComputed := CapturedArrayImage.prepared _
   old := rhCoupledPlan.old
   oldComputed := rhCoupledPlan.oldComputed
   raw := rhCoupledPlan.raw
   encoded := rhCoupledPlan.encoded
   oldChecked := rhCoupledPlan.oldChecked
   nextImage := ⟨rhCoupledPlan.nextImage.elements,by rw [re_visit_compat]; exact rhCoupledPlan.nextImage.computed⟩
   nextImageComputed := CapturedArrayImage.prepared _
   nextChecked := rhCoupledPlan.nextChecked
   sourceOp := rhCoupledPlan.sourceOp
   prepared := rhCoupledPlan.prepared}

theorem re_actual_whole_step : rePlan.step=rhCoupledPlan.step := rfl

theorem re_whole_reencode : finiteEncode rePlan.next (rePlan.step.1.2.2.ex.world.accounts account).storage
    (fun q => rePlan.step.2.cells (complementKey false account q))=some rePlan.nextRaw := rePlan.reencode rfl

theorem re_MemOK (H) (ok : Source.MemOK agEnv H agShrink.2) : Source.MemOK agEnv H rePlan.step.1.2 := rePlan.MemOK H ok

def reReturnChild : Source.EM agEnv [] (Source.Val agEnv.layout agAliasTy) :=
  Source.readLoc packedStepFrame (.stor (agInner 0))

theorem re_return_run : reReturnChild.run (Source.Locals.nil,agShrink.2.2)=
    (.ok (Source.Val.storRef (by rfl) (agInner 0)),(Source.Locals.nil,agShrink.2.2)) := rfl

def reCaptured := captureSubValueRun packedStepFrame [] agAliases.1 Source.Locals.nil reReturnChild agShrink.2.2

theorem re_returned_and_suspended : scopedEntryIndices rhLayout reCaptured.2=[0,0,0] := rfl

theorem re_return_dedup : capturedVisitIndices rhLayout [] reCaptured.2 0=[0] := rfl

/-- Caller locals alone retain two aliases on halt; no value is invented as a
successful return, and sub does not itself roll back the actual source store. -/
def reFailed : Source.EM agEnv [] (Source.Val agEnv.layout agAliasTy) := Source.EM.halt (.revert [7])
theorem re_halt_scopes : scopedEntryIndices rhLayout
    (captureSubValueRun packedStepFrame [] agAliases.1 Source.Locals.nil reFailed agShrink.2.2).2=[0,0] := rfl

theorem re_current_locals_only_loses : localStoragePaths (Source.Locals.nil (D := agEnv.layout))=[] ∧
    localStoragePaths agAliases.1=[agInner 0,agInner 0] := ⟨rfl,rfl⟩

def reReadLocal : Source.EM agEnv [agAliasTy,agAliasTy] (Source.Val agEnv.layout agAliasTy) :=
  Source.readLoc packedStepFrame (.local .here)

theorem re_local_producer_total : scopedEntryIndices rhLayout
    (captureValueRun packedStepFrame [] reReadLocal agShrink.2).2=[0,0,0,0,0] := rfl

theorem re_caller_prefix_rollback :
    (companionRollback (companionEnter rePlan.before account account 0 [] false) rePlan.after,reScopes)=(rePlan.before,reScopes) := rePlan.rollback rfl

theorem re_static_preserves : (rePlan.withStatic true).step=((.error (.revert []),agShrink.2),rhPrefixResidual) := by
  exact (rePlan.withStatic true).static rfl

def reUseEscaped : Source.EM agEnv [] Nat := do
  let (alias,_) ← Source.EM.sub Source.Locals.nil reReturnChild
  Source.applyOp packedStepFrame rePlan.sourceOp
  Source.lengthOf packedStepFrame alias

theorem re_use_escaped : reUseEscaped.run (Source.Locals.nil,agShrink.2.2)=
    (.ok 3,(Source.Locals.nil,rePlan.step.1.2.2)) := by
  unfold reUseEscaped
  rw [Source.Hoare.run_bind,actualSub_endpoints,re_return_run]
  change ((Source.applyOp packedStepFrame rePlan.sourceOp) >>= fun _ =>
    Source.lengthOf packedStepFrame (Source.Val.storRef (τ := agAliasTy) (by rfl) (agInner 0))).run
    (Source.Locals.nil,agShrink.2.2)=_
  rw [Source.Hoare.run_bind,actualApplyOp_run]
  change (Source.readLen packedStepFrame (agInner 0)).run (Source.Locals.nil,rePlan.step.1.2.2)=_
  have read := (rhPlan.relocalize (Source.Locals.nil (D := agEnv.layout))).retained_header_read rfl rhFirst rhHeaderEntry
  rw [(rhPlan.relocalize (Source.Locals.nil (D := agEnv.layout))).nonstatic rfl] at read
  rw [rePlan.nonstatic rfl]
  rw [show rePlan.sourceOp=rhPlan.sourceOp from rh_coupled_same_op]
  change (Source.readLen packedStepFrame (agInner 0)).run (Source.Locals.nil,{agShrink.2.2 with ex:=agShrink.2.2.ex.apply rhPlan.sourceOp})=
    (.ok (rhPlan.nextRaw (rhHeader.registration account).slot).val,(Source.Locals.nil,{agShrink.2.2 with ex:=agShrink.2.2.ex.apply rhPlan.sourceOp})) at read
  have raw : rhPlan.nextRaw=saveSlot rhRaw0 101 3 := congrArg (fun m => saveSlot m 101 3) rh_raw_input
  rw [raw] at read
  exact read

def reSequence := captureValueBindRun (ρ := agAliasTy) packedStepFrame [] reReturnChild
  (fun _ => Source.EM.halt (.revert [9])) (Source.Locals.nil,agShrink.2.2)

theorem re_return_survives_late_halt : scopedEntryIndices rhLayout reSequence.2=[0] := rfl

theorem re_wrong_chronology : reSequence.1=(Except.error (.revert [9]),(Source.Locals.nil,agShrink.2.2)) := rfl

end Solidity.Yul.Views.Controls
