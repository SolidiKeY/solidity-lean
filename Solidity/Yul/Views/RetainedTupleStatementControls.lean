import Solidity.Yul.Views.RetainedTupleStatement
import Solidity.Yul.Views.RetainedTupleControls

/-! Actual expression statements discard a nested tuple but retain its dormant
storage references in capture. Late tuple timeout keeps earlier arguments and
prior scopes. Computed duplicate-safe indices connect to existing ownership. -/
namespace Solidity.Yul.Views.Controls

def rsOuter : Source.EMState agEnv [] := (.nil,agShrink.2.2)
def rsScopes (G : Source.Glob agEnv) :=
  (captureTupleStatement G packedStepFrame 8 rtArgs [] agShrink.2.1 rsOuter).2

theorem rs_actual_statement (G : Source.Glob agEnv) :
    (Source.execS G packedStepFrame 8 0 none (R:=[]) (M:=false) (k:=Source.SCtx.body)
      (.expr (.tuple rtArgs)) agShrink.2.1).run rsOuter=(.ok (.normal agShrink.2.1),rsOuter) := rfl

theorem rs_exact_source (G : Source.Glob agEnv) :
    (captureTupleStatement G packedStepFrame 8 rtArgs [] agShrink.2.1 rsOuter).1=
      (.ok (.normal agShrink.2.1),rsOuter) := by
  first | solve | rfl
        | rw [captureTupleStatement_source G packedStepFrame 8 0 none]
          exact rs_actual_statement G

theorem rs_captured_head (G : Source.Glob agEnv) : runtimeScope packedStepFrame (.val rtAlias)∈rsScopes G :=
  captureTupleStatement_head G packedStepFrame 5 (.local .here)
    (.cons (.tuple (.cons (.local (.there .here)) .nil)) .nil) [] agShrink.2.1 rsOuter _ (.val rtAlias) rfl

theorem rs_late_timeout (G : Source.Glob agEnv) :
    (captureTupleStatement G packedStepFrame 4 rtLateArgs [] agShrink.2.1 rsOuter).1=(.error .timeout,rsOuter) := rfl

theorem rs_late_keeps_head (G : Source.Glob agEnv) : runtimeScope packedStepFrame (.val rtAlias)∈
    (captureTupleStatement G packedStepFrame 4 rtLateArgs [] agShrink.2.1 rsOuter).2 :=
  captureTupleStatement_head G packedStepFrame 1 (.local .here) (.cons (.local (.there .here)) .nil)
    [] agShrink.2.1 rsOuter _ (.val rtAlias) rfl

theorem rs_prior_survives (G : Source.Glob agEnv) : runtimeScope packedStepFrame rtNested∈
    (captureTupleStatement G packedStepFrame 4 rtLateArgs [runtimeScope packedStepFrame rtNested]
      agShrink.2.1 rsOuter).2 :=
  captureTupleStatement_prior G packedStepFrame 4 rtLateArgs _ _ _ _ List.mem_cons_self

theorem rs_dedup (G : Source.Glob agEnv) : capturedVisitIndices rhLayout [] (rsScopes G) 0=[0] := rfl

theorem rs_scope_compat (G : Source.Glob agEnv) (n : Nat) :
    capturedVisitIndices rhLayout [] (rsScopes G) n=capturedVisitIndices rhLayout [] reScopes n := by
  simp only [capturedVisitIndices,List.map_nil,List.append_nil]
  change uniqueVisitIndices [] (List.range n++[0,0,0,0,0,0,0,0,0,0,0,0,0,0])=
    uniqueVisitIndices [] (List.range n++[0,0])
  repeat rw [uniqueVisitIndices_duplicate [] (List.range n)]

def rsPlan (G : Source.Glob agEnv) : CapturedOwnershipPlan packedStepFrame rhLayout agFixed [] (rsScopes G)
    101 3 agShrink.2 rhPrefixResidual :=
  {oldLength:=rePlan.oldLength
   lengthComputed:=rePlan.lengthComputed
   oldImage:=⟨rePlan.oldImage.elements,by rw [rs_scope_compat];exact rePlan.oldImage.computed⟩
   oldImageComputed:=CapturedArrayImage.prepared _
   old:=rePlan.old
   oldComputed:=rePlan.oldComputed
   raw:=rePlan.raw
   encoded:=rePlan.encoded
   oldChecked:=rePlan.oldChecked
   nextImage:=⟨rePlan.nextImage.elements,by rw [rs_scope_compat];exact rePlan.nextImage.computed⟩
   nextImageComputed:=CapturedArrayImage.prepared _
   nextChecked:=rePlan.nextChecked
   sourceOp:=rePlan.sourceOp
   prepared:=rePlan.prepared}

theorem rs_source_and_residual (G : Source.Glob agEnv) : (rsPlan G).step=rePlan.step := rfl

theorem rs_single_value_rejects : rtNested.get=.error (.stuck "not a plain value") := rfl

end Solidity.Yul.Views.Controls
