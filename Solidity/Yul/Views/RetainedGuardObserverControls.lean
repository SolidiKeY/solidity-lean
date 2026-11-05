import Solidity.Yul.Views.RetainedGuardObserver
import Solidity.Yul.Views.RetainedComparisonControls
import Solidity.Yul.Views.RetainedBranchObserverControls

/-! Actual tuple operands are captured inside a comparison guard before getV
halts. This is a typed Source evaluator boundary, not frontend admission.
The same aliases remain in locals; no exclusive provenance is asserted. -/
namespace Solidity.Yul.Views.Controls

def rguCondition : Source.RExpr agEnv [agAliasTy,agAliasTy] .bool :=
  .compare .eq (.tuple rcmpArgs) (.tuple rcmpArgs)

def rguBody (G : Source.Glob agEnv) :=
  blockStatementObserver G packedStepFrame 8 0 none rtcBody
    (tupleItemsObserver G packedStepFrame 8 0 none rtArgs rssTail)

def rguGuard (G : Source.Glob agEnv) :=
  comparisonGuardObserver G packedStepFrame 9 .eq (.tuple rcmpArgs) (.tuple rcmpArgs)

def rguObserver (G : Source.Glob agEnv) :=
  guardedIfThenStatementObserver G packedStepFrame 9 0 none rguCondition (.block rtcBody) (rguGuard G) (rguBody G)

def rguCapture (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :=
  (rguObserver G).observe prior agShrink.2.1 rsOuter

theorem rgu_exact_source (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rguCapture G prior).1=
      (Source.execS G packedStepFrame 10 0 none (.ifThen rguCondition (.block rtcBody)) agShrink.2.1).run rsOuter :=
  (rguObserver G).source prior agShrink.2.1 rsOuter

theorem rgu_guard_error (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    ((rguGuard G).observe prior agShrink.2.1 rsOuter).1=(.error (.stuck "not a plain value"),rsOuter) := by
  change (captureComparisonGuard G packedStepFrame 9 .eq (.tuple rcmpArgs) (.tuple rcmpArgs)
    prior agShrink.2.1 rsOuter).1=_
  unfold captureComparisonGuard
  dsimp only
  rw [captureComparisonRun_source]
  rw [show (Source.evalE G packedStepFrame 9 (.compare .eq (.tuple rcmpArgs) (.tuple rcmpArgs))).run
      (agShrink.2.1,rsOuter.2)=(.error (.stuck "not a plain value"),agShrink.2) from rcmp_getV_failure G]
  rfl

theorem rgu_error_inventory (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    rguCapture G prior=((.error (.stuck "not a plain value"),rsOuter),
      ((rguGuard G).observe prior agShrink.2.1 rsOuter).2) :=
  observeGuardedIfThen_error G packedStepFrame 9 0 none rguCondition (.block rtcBody) (rguGuard G) (rguBody G)
    prior agShrink.2.1 rsOuter rsOuter _ (rgu_guard_error G prior)

theorem rgu_tuple_retained (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame rcmpTuple∈(rguCapture G []).2 := by
  exact observeGuardedIfThen_guard_scopes G packedStepFrame 9 0 none rguCondition (.block rtcBody)
    (rguGuard G) (rguBody G) [] agShrink.2.1 rsOuter _ (rcmp_tuple_retained G)

/-- The earlier raw-guard adapter has no produced guard scope on this error. -/
theorem rgu_raw_guard_list (G : Source.Glob agEnv) :
    (observeIfThen G packedStepFrame 9 0 none rguCondition (.block rtcBody) (rguBody G)
      [] agShrink.2.1 rsOuter).2=[] := by
  unfold observeIfThen
  dsimp only
  rw [show (Source.EM.sub agShrink.2.1 (Source.evalE G packedStepFrame 9 rguCondition) :
      Source.EM agEnv [] (Source.RVal agEnv.layout .bool × Source.Locals agEnv.layout [agAliasTy,agAliasTy])).run rsOuter=
        (.error (.stuck "not a plain value"),rsOuter) from (rguGuard G).source [] agShrink.2.1 rsOuter |>.symm.trans (rgu_guard_error G [])]

theorem rgu_prior (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv))
    (scope) (member : scope∈prior) : scope∈(rguCapture G prior).2 :=
  (rguObserver G).prior prior agShrink.2.1 rsOuter scope member

/-- Successful scalar comparisons also use the actual selected body. -/
def rguScalar (G : Source.Glob agEnv) (flag : Bool) (prior : List (EntryReferenceScope agEnv)) :=
  (guardedIfThenStatementObserver G packedStepFrame 9 0 none (.compare .eq (.bool flag) (.bool true))
    (.block rtcBody) (comparisonGuardObserver G packedStepFrame 9 .eq (.bool flag) (.bool true)) (rguBody G)).observe
    prior agShrink.2.1 rsOuter

theorem rgu_scalar_false (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rguScalar G false prior).1=(.ok (.normal agShrink.2.1),rsOuter) := by
  cases G with
  | mk prog pipeline fixed balance hasCode callee timestamp => cases pipeline <;> rfl

theorem rgu_scalar_true (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rguScalar G true prior).1=(.error (.stuck "no default value"),rsOuter) := by
  cases G with
  | mk prog pipeline fixed balance hasCode callee timestamp => cases pipeline <;> rfl

end Solidity.Yul.Views.Controls
