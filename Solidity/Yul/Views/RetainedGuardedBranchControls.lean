import Solidity.Yul.Views.RetainedGuardedBranch
import Solidity.Yul.Views.RetainedGuardObserverControls

/-! Observed scalar guards select actual distinct success/halt arms. A tuple
comparison guard captures its operands before conversion fails, bypassing both
bodies. Tuple comparison is a typed evaluator boundary, not frontend admission;
no exclusive provenance or general capture completeness is inferred. -/
namespace Solidity.Yul.Views.Controls

def rgeScalarCondition (flag : Bool) : Source.RExpr agEnv [agAliasTy,agAliasTy] .bool :=
  .compare .eq (.bool flag) (.bool true)

def rgeScalarGuard (G : Source.Glob agEnv) (flag : Bool) : GuardObserver G packedStepFrame 10 (rgeScalarCondition flag) :=
  comparisonGuardObserver G packedStepFrame 10 .eq (.bool flag) (.bool true)

def rgeScalarObserver (G : Source.Glob agEnv) (flag : Bool) :=
  guardedIfElseStatementObserver G packedStepFrame 10 0 none (rgeScalarCondition flag)
    (.block rboExtendedBody) (.block rtcBody) (rgeScalarGuard G flag) (rbrYes G) (rbrNo G)

def rgeScalar (G : Source.Glob agEnv) (flag : Bool) (prior : List (EntryReferenceScope agEnv)) :=
  (rgeScalarObserver G flag).observe prior agShrink.2.1 rsOuter

theorem rge_scalar_source (G : Source.Glob agEnv) (flag : Bool) (prior : List (EntryReferenceScope agEnv)) :
    (rgeScalar G flag prior).1=
      (Source.execS G packedStepFrame 11 0 none (.ifElse (rgeScalarCondition flag)
        (.block rboExtendedBody) (.block rtcBody)) agShrink.2.1).run rsOuter :=
  (rgeScalarObserver G flag).source prior agShrink.2.1 rsOuter

theorem rge_scalar_true (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rgeScalar G true prior).1=(.ok (.normal agShrink.2.1),rsOuter) := by
  cases G with
  | mk prog pipeline fixed balance hasCode callee timestamp => cases pipeline <;> rfl

theorem rge_scalar_false (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rgeScalar G false prior).1=(.error (.stuck "no default value"),rsOuter) := by
  cases G with
  | mk prog pipeline fixed balance hasCode callee timestamp => cases pipeline <;> rfl

theorem rge_scalar_guard_run (G : Source.Glob agEnv) (flag : Bool) (prior : List (EntryReferenceScope agEnv)) :
    ((rgeScalarGuard G flag).observe prior agShrink.2.1 rsOuter).1=
      (.ok (.val (.bool flag),agShrink.2.1),rsOuter) := by
  cases flag
  · cases G with
    | mk prog pipeline fixed balance hasCode callee timestamp => cases pipeline <;> rfl
  · cases G with
    | mk prog pipeline fixed balance hasCode callee timestamp => cases pipeline <;> rfl

theorem rge_scalar_selected (G : Source.Glob agEnv) (flag : Bool) (prior : List (EntryReferenceScope agEnv)) :
    (rgeScalar G flag prior).2=
      if flag then ((rbrYes G).observe ((rgeScalarGuard G flag).observe prior agShrink.2.1 rsOuter).2 agShrink.2.1 rsOuter).2
      else ((rbrNo G).observe ((rgeScalarGuard G flag).observe prior agShrink.2.1 rsOuter).2 agShrink.2.1 rsOuter).2 :=
  observeGuardedIfElse_selected_scopes G packedStepFrame 10 0 none (rgeScalarCondition flag)
    (.block rboExtendedBody) (.block rtcBody) (rgeScalarGuard G flag) (rbrYes G) (rbrNo G) prior
    agShrink.2.1 agShrink.2.1 rsOuter rsOuter flag (rge_scalar_guard_run G flag prior)

def rgeBadObserver (G : Source.Glob agEnv) :=
  guardedIfElseStatementObserver G packedStepFrame 9 0 none rguCondition
    (.block rtcBody) (.block rtcBody) (rguGuard G) (rguBody G) (rguBody G)

def rgeBad (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :=
  (rgeBadObserver G).observe prior agShrink.2.1 rsOuter

theorem rge_error_inventory (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    rgeBad G prior=((.error (.stuck "not a plain value"),rsOuter),((rguGuard G).observe prior agShrink.2.1 rsOuter).2) :=
  observeGuardedIfElse_error G packedStepFrame 9 0 none rguCondition (.block rtcBody) (.block rtcBody)
    (rguGuard G) (rguBody G) (rguBody G) prior agShrink.2.1 rsOuter rsOuter _ (rgu_guard_error G prior)

theorem rge_tuple_retained (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame rcmpTuple∈(rgeBad G []).2 := by
  exact observeGuardedIfElse_guard_scopes G packedStepFrame 9 0 none rguCondition (.block rtcBody) (.block rtcBody)
    (rguGuard G) (rguBody G) (rguBody G) [] agShrink.2.1 rsOuter _ (rcmp_tuple_retained G)

theorem rge_prior (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv))
    (scope) (member : scope∈prior) : scope∈(rgeBad G prior).2 :=
  (rgeBadObserver G).prior prior agShrink.2.1 rsOuter scope member

end Solidity.Yul.Views.Controls
