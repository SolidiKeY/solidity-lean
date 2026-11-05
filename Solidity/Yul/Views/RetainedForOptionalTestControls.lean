import Solidity.Yul.Views.RetainedForOptionalTest
import Solidity.Yul.Views.RetainedForPostRetentionControls
import Solidity.Yul.Views.RetainedForGuardedControls

/-! The actual reference-valued comparison test fails getV before body/post.
Its tuple capture survives for any optional post and explicit post-family
input. Final error equality is separate from actual test capture evidence. -/
namespace Solidity.Yul.Views.Controls

def rfotIteration (G : Source.Glob agEnv) (post : Source.ROptExpr agEnv [agAliasTy,agAliasTy])
    (posts : OptionalForPosts G packedStepFrame post) :=
  optionalForIterationObserver G packedStepFrame 10 0 none (.some rguCondition) post
    .skip (rfgBadGuards G) posts (rfiBodies G)

theorem rfot_test_error (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    ((optionalForTestObserver G packedStepFrame 9 (.some rguCondition) (rfgBadGuards G)).observe
      prior agShrink.2.1 rsOuter).1=(.error (.stuck "not a plain value"),rsOuter) :=
  rfpr_test_error G prior

/-- Test capture remains available with an arbitrary post, without assuming
a successful Boolean result or executing the body. -/
theorem rfot_tuple (G : Source.Glob agEnv) (post : Source.ROptExpr agEnv [agAliasTy,agAliasTy])
    (posts : OptionalForPosts G packedStepFrame post) :
    runtimeScope packedStepFrame rcmpTuple∈((rfotIteration G post posts).observe [] agShrink.2.1 rsOuter).2 := by
  exact optionalForIteration_test_scopes G packedStepFrame 9 0 none (.some rguCondition) post
    .skip (rfgBadGuards G) posts (rfiBodies G) [] agShrink.2.1 rsOuter _ (rcmp_tuple_retained G)

theorem rfot_error_inventory (G : Source.Glob agEnv) (post : Source.ROptExpr agEnv [agAliasTy,agAliasTy])
    (posts : OptionalForPosts G packedStepFrame post) (prior : List (EntryReferenceScope agEnv)) :
    (rfotIteration G post posts).observe prior agShrink.2.1 rsOuter=
      ((.error (.stuck "not a plain value"),rsOuter),
        ((optionalForTestObserver G packedStepFrame 9 (.some rguCondition) (rfgBadGuards G)).observe
          prior agShrink.2.1 rsOuter).2) := by
  cases post with
  | none =>
    have raw : ((rfgBadGuards G 9).observe prior agShrink.2.1 rsOuter).1=
        (.error (.stuck "not a plain value"),rsOuter) := rgu_guard_error G prior
    change observeWhile G packedStepFrame 10 0 none rguCondition .skip
      (rfgBadGuards G) (rfiBodies G) prior agShrink.2.1 rsOuter (lp:=false)=_
    unfold observeWhile
    dsimp only
    rw [raw]
    rfl
  | some pe =>
    exact observeForPostIteration_test_error G packedStepFrame 9 0 none (.some rguCondition) pe .skip
      (fun i => presentForTestObserver G packedStepFrame i rguCondition (rfgBadGuards G i))
      (rfiBodies G) posts prior agShrink.2.1 rsOuter rsOuter (.stuck "not a plain value") (rfot_test_error G prior)

theorem rfot_source (G : Source.Glob agEnv) (post : Source.ROptExpr agEnv [agAliasTy,agAliasTy])
    (posts : OptionalForPosts G packedStepFrame post) (prior : List (EntryReferenceScope agEnv)) :
    ((rfotIteration G post posts).observe prior agShrink.2.1 rsOuter).1=
      (Source.forIter G packedStepFrame 10 0 none (.some rguCondition) post
        (.skip (R:=[]) (M:=false) (k:=⟨true,false⟩)) agShrink.2.1).run rsOuter :=
  (rfotIteration G post posts).source prior agShrink.2.1 rsOuter

theorem rfot_absent_post (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame rcmpTuple∈((rfotIteration G .none PUnit.unit).observe [] agShrink.2.1 rsOuter).2 :=
  rfot_tuple G .none PUnit.unit

theorem rfot_present_post (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame rcmpTuple∈
      ((rfotIteration G (.some (.tuple rtArgs)) (rfiPosts G)).observe [] agShrink.2.1 rsOuter).2 :=
  rfot_tuple G (.some (.tuple rtArgs)) (rfiPosts G)

end Solidity.Yul.Views.Controls
