import Solidity.Yul.Views.RetainedBranchObserver
import Solidity.Yul.Views.RetainedBlockObserverControls

/-! Actual true/false arms, successful context restoration, an unselected
halting arm and guard timeout. Captures are retained from the selected real
tuple observer. Guard intermediates and exclusive provenance are not asserted. -/
namespace Solidity.Yul.Views.Controls

def rbrYes (G : Source.Glob agEnv) :=
  blockStatementObserver G packedStepFrame 9 0 none rboExtendedBody
    (tupleItemsObserver G packedStepFrame 9 0 none rtArgs (.stmt (.declVar .bool) .nil))

def rbrNo (G : Source.Glob agEnv) :=
  blockStatementObserver G packedStepFrame 9 0 none rtcBody
    (tupleItemsObserver G packedStepFrame 9 0 none rtArgs rssTail)

def rbrObserver (G : Source.Glob agEnv)
    (condition : Source.RExpr agEnv [agAliasTy,agAliasTy] .bool) :=
  ifElseStatementObserver G packedStepFrame 10 0 none condition (.block rboExtendedBody) (.block rtcBody)
    (rbrYes G) (rbrNo G)

def rbrCapture (G : Source.Glob agEnv) (flag : Bool) (prior : List (EntryReferenceScope agEnv)) :=
  (rbrObserver G (.bool flag)).observe prior agShrink.2.1 rsOuter

theorem rbr_exact_source (G : Source.Glob agEnv) (flag : Bool) (prior : List (EntryReferenceScope agEnv)) :
    (rbrCapture G flag prior).1=
      (Source.execS G packedStepFrame 11 0 none
        (.ifElse (.bool flag) (.block rboExtendedBody) (.block rtcBody)) agShrink.2.1).run rsOuter :=
  (rbrObserver G (.bool flag)).source prior agShrink.2.1 rsOuter

theorem rbr_true_skips_halt (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rbrCapture G true prior).1=(.ok (.normal agShrink.2.1),rsOuter) := by
  rfl

theorem rbr_false_halts (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rbrCapture G false prior).1=(.error (.stuck "no default value"),rsOuter) := by
  rfl

theorem rbr_selected_scopes (G : Source.Glob agEnv) (flag : Bool) (prior : List (EntryReferenceScope agEnv)) :
    (rbrCapture G flag prior).2=
      if flag then ((rbrYes G).observe prior agShrink.2.1 rsOuter).2
      else ((rbrNo G).observe prior agShrink.2.1 rsOuter).2 :=
  observeIfElse_selected_scopes G packedStepFrame 10 0 none (.bool flag) (.block rboExtendedBody) (.block rtcBody)
    (rbrYes G) (rbrNo G) prior agShrink.2.1 agShrink.2.1 rsOuter rsOuter flag rfl

theorem rbr_selected_capture (G : Source.Glob agEnv) (flag : Bool) (prior : List (EntryReferenceScope agEnv)) :
    runtimeScope packedStepFrame (.val rtAlias)∈(rbrCapture G flag prior).2 := by
  rw [rbr_selected_scopes]
  cases flag
  · exact captureTupleItems_head G packedStepFrame 5 0 none (.local .here)
      (.cons (.tuple (.cons (.local (.there .here)) .nil)) .nil) rssTail prior agShrink.2.1 rsOuter _ (.val rtAlias) rfl
  · exact captureTupleItems_head G packedStepFrame 5 0 none (.local .here)
      (.cons (.tuple (.cons (.local (.there .here)) .nil)) .nil) (.stmt (.declVar .bool) .nil)
      prior agShrink.2.1 rsOuter _ (.val rtAlias) rfl (R:=[]) (M:=false) (k:=Source.SCtx.body)

/-- This is the same typed Source conditional expression at every depth. -/
def rbrDeepBool : Nat → Source.RExpr agEnv [agAliasTy,agAliasTy] .bool
  | 0 => .bool true
  | n+1 => .cond (.bool true) (rbrDeepBool n) (.bool false)

def rbrTimeout (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :=
  (rbrObserver G (rbrDeepBool 11)).observe prior agShrink.2.1 rsOuter

theorem rbr_guard_timeout (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    rbrTimeout G prior=((.error .timeout,rsOuter),prior) := by
  rfl

theorem rbr_prior (G : Source.Glob agEnv) (flag : Bool) (prior : List (EntryReferenceScope agEnv))
    (scope) (member : scope∈prior) : scope∈(rbrCapture G flag prior).2 :=
  (rbrObserver G (.bool flag)).prior prior agShrink.2.1 rsOuter scope member

end Solidity.Yul.Views.Controls
