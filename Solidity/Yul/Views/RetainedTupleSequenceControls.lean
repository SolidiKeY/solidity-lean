import Solidity.Yul.Views.RetainedTupleSequence
import Solidity.Yul.Views.RetainedTupleStatementControls

/-! An actual discarded nested tuple precedes an actual owner declaration halt.
Captured arguments/prior scopes survive; the source error and state are exact.
Inherited aliases also remain in locals, so exclusive tuple provenance is not
asserted. Arbitrary recursive tail producers are not instrumented here. -/
namespace Solidity.Yul.Views.Controls

def rssTail : Source.RItems agEnv [] false Source.SCtx.body
    [agAliasTy,agAliasTy] [agAliasTy,agAliasTy,agAliasTy] := .stmt (.declVar agAliasTy) .nil

def rssCapture (G : Source.Glob agEnv) :=
  captureTupleItems G packedStepFrame 9 0 none rtArgs rssTail [] agShrink.2.1 rsOuter

theorem rss_owner_halt (G : Source.Glob agEnv) :
    (Source.execItems G packedStepFrame 9 0 none (.stmt (.expr (.tuple rtArgs)) rssTail) agShrink.2.1).run rsOuter=
      (.error (.stuck "no default value"),rsOuter) := rfl

theorem rss_exact_source (G : Source.Glob agEnv) :
    (rssCapture G).1=(.error (.stuck "no default value"),rsOuter) := by
  first | solve | rfl
        | rw [show (rssCapture G).1=_ from captureTupleItems_source G packedStepFrame 9 0 none rtArgs rssTail [] agShrink.2.1 rsOuter]
          exact rss_owner_halt G

theorem rss_prefix_completed (G : Source.Glob agEnv) :
    (captureTupleStatement G packedStepFrame 8 rtArgs [] agShrink.2.1 rsOuter).1=
      (.ok (.normal agShrink.2.1),rsOuter) := rs_exact_source G

theorem rss_retains_head (G : Source.Glob agEnv) : runtimeScope packedStepFrame (.val rtAlias)∈(rssCapture G).2 :=
  captureTupleItems_head G packedStepFrame 5 0 none (.local .here)
    (.cons (.tuple (.cons (.local (.there .here)) .nil)) .nil) rssTail [] agShrink.2.1 rsOuter _ (.val rtAlias) rfl

theorem rss_no_returned_value (G : Source.Glob agEnv) : (rssCapture G).1.1.toOption=none := by
  rw [rss_exact_source]
  rfl

theorem rss_scope_compat (G : Source.Glob agEnv) (n : Nat) :
    capturedVisitIndices rhLayout [] (rssCapture G).2 n=capturedVisitIndices rhLayout [] reScopes n := by
  change capturedVisitIndices rhLayout [] (rsScopes G) n=_
  exact rs_scope_compat G n

def rssPlan (G : Source.Glob agEnv) : CapturedOwnershipPlan packedStepFrame rhLayout agFixed [] (rssCapture G).2
    101 3 agShrink.2 rhPrefixResidual :=
  {oldLength:=rePlan.oldLength
   lengthComputed:=rePlan.lengthComputed
   oldImage:=⟨rePlan.oldImage.elements,by rw [rss_scope_compat];exact rePlan.oldImage.computed⟩
   oldImageComputed:=CapturedArrayImage.prepared _
   old:=rePlan.old
   oldComputed:=rePlan.oldComputed
   raw:=rePlan.raw
   encoded:=rePlan.encoded
   oldChecked:=rePlan.oldChecked
   nextImage:=⟨rePlan.nextImage.elements,by rw [rss_scope_compat];exact rePlan.nextImage.computed⟩
   nextImageComputed:=CapturedArrayImage.prepared _
   nextChecked:=rePlan.nextChecked
   sourceOp:=rePlan.sourceOp
   prepared:=rePlan.prepared}

theorem rss_coupled_source_residual (G : Source.Glob agEnv) : (rssPlan G).step=rePlan.step := rfl

end Solidity.Yul.Views.Controls
