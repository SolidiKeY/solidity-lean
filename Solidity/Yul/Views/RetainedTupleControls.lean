import Solidity.Yul.Views.RetainedTupleProducers
import Solidity.Yul.Views.RetainedEntryControls

namespace Solidity.Yul.Views.Controls

def rtAlias : Source.Val agEnv.layout agAliasTy := .storRef (by rfl) (agInner 0)
def rtNested : Source.RVal agEnv.layout (.tuple [agAliasTy,.tuple [agAliasTy]]) :=
  .tuple (.cons (.val rtAlias) (.cons (.tuple (.cons (.val rtAlias) .nil)) .nil))

theorem rt_nested_paths : runtimeStoragePaths rtNested=[agInner 0,agInner 0] := rfl
/-- Existing getV cannot expose these constituents; raw capture must precede it.
This is the REAL owner conversion error, not a new admission refusal. -/
theorem rt_single_val_loses : rtNested.get=Except.error (.stuck "not a plain value") := rfl

def rtArgs : Source.RArgs agEnv [agAliasTy,agAliasTy] [agAliasTy,.tuple [agAliasTy]] :=
  .cons (.local .here) (.cons (.tuple (.cons (.local (.there .here)) .nil)) .nil)

theorem rt_actual_tuple (G : Source.Glob agEnv) : (Source.evalE G packedStepFrame 7 (.tuple rtArgs)).run agShrink.2=
    (.ok rtNested,agShrink.2) := rfl

theorem rt_tuple_capture (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame rtNested ∈ (captureRuntimeRun packedStepFrame []
      (Source.evalE G packedStepFrame 7 (.tuple rtArgs)) agShrink.2).2 :=
  captureRuntimeRun_return _ _ _ _ _ _ (rt_actual_tuple G)

def rtLateArgs : Source.RArgs agEnv [agAliasTy,agAliasTy] [agAliasTy,agAliasTy] :=
  .cons (.local .here) (.cons (.local (.there .here)) .nil)

/-- At owner horizon2, head local succeeds at1 then tail's head times out at0.
The whole tuple returns no value, yet the first reference remains observed. -/
theorem rt_late_halt (G : Source.Glob agEnv) :
    (captureArgumentsRun G packedStepFrame 2 rtLateArgs [] agShrink.2).1=(Except.error .timeout,agShrink.2) := rfl

theorem rt_late_keeps (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame (.val rtAlias) ∈ (captureArgumentsRun G packedStepFrame 2 rtLateArgs [] agShrink.2).2 :=
  captureArgumentsRun_head G packedStepFrame 1 (.local .here) (.cons (.local (.there .here)) .nil) [] agShrink.2 agShrink.2 (.val rtAlias) rfl

def rtScopes : List (EntryReferenceScope agEnv) := [runtimeScope packedStepFrame rtNested]
theorem rt_scope_paths : scopedEntryIndices rhLayout rtScopes=[0,0] := rfl
theorem rt_dedup : capturedVisitIndices rhLayout [] rtScopes 0=[0] := rfl
theorem rt_scope_compat (n : Nat) : capturedVisitIndices rhLayout [] rtScopes n=capturedVisitIndices rhLayout [] reScopes n := rfl

def rtPlan : CapturedOwnershipPlan packedStepFrame rhLayout agFixed [] rtScopes 101 3 agShrink.2 rhPrefixResidual :=
  {oldLength := rePlan.oldLength
   lengthComputed := rePlan.lengthComputed
   oldImage := ⟨rePlan.oldImage.elements,by rw [rt_scope_compat]; exact rePlan.oldImage.computed⟩
   oldImageComputed := CapturedArrayImage.prepared _
   old := rePlan.old
   oldComputed := rePlan.oldComputed
   raw := rePlan.raw
   encoded := rePlan.encoded
   oldChecked := rePlan.oldChecked
   nextImage := ⟨rePlan.nextImage.elements,by rw [rt_scope_compat]; exact rePlan.nextImage.computed⟩
   nextImageComputed := CapturedArrayImage.prepared _
   nextChecked := rePlan.nextChecked
   sourceOp := rePlan.sourceOp
   prepared := rePlan.prepared}

theorem rt_same_source_map : rtPlan.step=rePlan.step := rfl

theorem rt_reencode : finiteEncode rtPlan.next (rtPlan.step.1.2.2.ex.world.accounts account).storage
    (fun q => rtPlan.step.2.cells (complementKey false account q))=some rtPlan.nextRaw := rtPlan.reencode rfl

theorem rt_unselected_account (other : Roadmap.Address) (different : other≠account) :
    (rtPlan.step.1.2.2.ex.world.accounts other)=(agShrink.2.2.ex.world.accounts other) := by
  rw [rt_same_source_map,re_actual_whole_step]
  exact rhCoupledPlan.other_account other different

theorem rt_whole_rollback : (companionRollback (companionEnter rtPlan.before account account 0 [] false) rtPlan.after,rtScopes)=
    (rtPlan.before,rtScopes) := rtPlan.rollback rfl

theorem rt_returns_from_locals : Source.retVals agAliases.1 0 [agAliasTy,agAliasTy]=
    Except.ok (.cons (.val rtAlias) (.cons (.val rtAlias) .nil)) := rfl

theorem rt_return_pack_paths : runtimeStoragePaths (Source.mkRet [agAliasTy,agAliasTy]
    (.cons (.val rtAlias) (.cons (.val rtAlias) .nil)))=[agInner 0,agInner 0] := rfl

theorem rt_dropped_tuple_negative : runtimeStoragePaths rtNested ≠ valueStoragePaths (Source.Val.bool true (D := agEnv.layout)) := by decide

theorem rt_wrong_account : scopedEntryIndices rhLayout [⟨⟨2,by decide⟩,runtimeStoragePaths rtNested⟩]=[] := rfl

end Solidity.Yul.Views.Controls
