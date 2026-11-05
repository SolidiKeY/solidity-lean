import Solidity.Yul.Views.RetainedForPostRetention
import Solidity.Yul.Views.RetainedForPostIterationControls
import Solidity.Yul.Views.RetainedWhileObserverControls
import Solidity.Yul.Views.RetainedGuardObserverControls

/-! Actual tuple-producing bodies retain their references with a present post,
for arbitrary typed terminal control. A reference-valued comparison test keeps
its captured tuple when actual getV fails, before the body/post can run.
These controls prove retention, not completeness or exclusive provenance. -/
namespace Solidity.Yul.Views.Controls

def rfprObserver (G : Source.Glob agEnv)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) (n : Nat) :=
  postForIterationObserver G packedStepFrame n 0 none .none (.tuple rtArgs) (.block (rboInner control))
    (absentForTestObserver G packedStepFrame) (rwhBodies G control) (rfiPosts G)

theorem rfpr_body_source (G : Source.Glob agEnv)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy])
    (n : Nat) (prior : List (EntryReferenceScope agEnv)) :
    ((rfprObserver G control n).observe prior agShrink.2.1 rsOuter).1=
      (Source.forIter G packedStepFrame n 0 none .none (.some (.tuple rtArgs))
        (.block (rboInner control)) agShrink.2.1).run rsOuter :=
  (rfprObserver G control n).source prior agShrink.2.1 rsOuter

/-- The body capture survives without imposing a particular later control,
post result, recursive result or loop exit. -/
theorem rfpr_body_head (G : Source.Glob agEnv)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) :
    runtimeScope packedStepFrame (.val rtAlias)∈((rfprObserver G control 16).observe [] agShrink.2.1 rsOuter).2 := by
  exact observeForPostIteration_body_scopes G packedStepFrame 15 0 none .none (.tuple rtArgs)
    (.block (rboInner control)) (absentForTestObserver G packedStepFrame) (rwhBodies G control) (rfiPosts G)
    [] agShrink.2.1 agShrink.2.1 rsOuter rsOuter rfl _
    (captureTupleItems_head G packedStepFrame 10 0 none (.local .here)
      (.cons (.tuple (.cons (.local (.there .here)) .nil)) .nil) (.stmt control .nil)
      [] agShrink.2.1 rsOuter _ (.val rtAlias) rfl)

def rfprGuardTests (G : Source.Glob agEnv) (n : Nat) :=
  presentForTestObserver G packedStepFrame n rguCondition
    (comparisonGuardObserver G packedStepFrame n .eq (.tuple rcmpArgs) (.tuple rcmpArgs))

def rfprGuardObserver (G : Source.Glob agEnv) :=
  postForIterationObserver G packedStepFrame 10 0 none (.some rguCondition) (.tuple rtArgs) .skip
    (rfprGuardTests G) (rfiBodies G) (rfiPosts G)

theorem rfpr_test_error (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    ((rfprGuardTests G 9).observe prior agShrink.2.1 rsOuter).1=
      (.error (.stuck "not a plain value"),rsOuter) := by
  change (observePresentForTest G packedStepFrame 9 rguCondition (rguGuard G)
    prior agShrink.2.1 rsOuter).1=_
  unfold observePresentForTest
  dsimp only
  rw [rgu_guard_error]

theorem rfpr_error_inventory (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rfprGuardObserver G).observe prior agShrink.2.1 rsOuter=
      ((.error (.stuck "not a plain value"),rsOuter),
        ((rfprGuardTests G 9).observe prior agShrink.2.1 rsOuter).2) := by
  exact observeForPostIteration_test_error G packedStepFrame 9 0 none (.some rguCondition) (.tuple rtArgs)
    .skip (rfprGuardTests G) (rfiBodies G) (rfiPosts G) prior agShrink.2.1 rsOuter rsOuter
    (.stuck "not a plain value") (rfpr_test_error G prior)

theorem rfpr_test_tuple (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame rcmpTuple∈((rfprGuardObserver G).observe [] agShrink.2.1 rsOuter).2 := by
  exact observeForPostIteration_test_scopes G packedStepFrame 9 0 none (.some rguCondition) (.tuple rtArgs)
    .skip (rfprGuardTests G) (rfiBodies G) (rfiPosts G) [] agShrink.2.1 rsOuter _ (rcmp_tuple_retained G)

theorem rfpr_guard_source (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    ((rfprGuardObserver G).observe prior agShrink.2.1 rsOuter).1=
      (Source.forIter G packedStepFrame 10 0 none (.some rguCondition) (.some (.tuple rtArgs))
        (.skip (R:=[]) (M:=false) (k:=⟨true,false⟩)) agShrink.2.1).run rsOuter :=
  (rfprGuardObserver G).source prior agShrink.2.1 rsOuter

end Solidity.Yul.Views.Controls
