import Solidity.Yul.Views.RetainedForPost
import Solidity.Yul.Views.RetainedBranchObserverControls

/-! An actual for iteration reaches a tuple post before its next guard times
out. Post references survive that late failure, and an earlier argument also
survives failure inside a post. These are typed Source boundary controls, not
frontend admission, exclusive provenance or general loop/compiler adequacy. -/
namespace Solidity.Yul.Views.Controls

def rfpPost (G : Source.Glob agEnv) := tuplePostObserver G packedStepFrame 10 rtArgs

/-- These prefix facts witness actual reachability of the post, independently
of the equality of final timeout results. -/
theorem rfp_initial_guard (G : Source.Glob agEnv) :
    (Source.EM.sub agShrink.2.1 (Source.evalE G packedStepFrame 10 (rbrDeepBool 9)) :
      Source.EM agEnv [] (Source.RVal agEnv.layout .bool × Source.Locals agEnv.layout [agAliasTy,agAliasTy])).run rsOuter=
        (.ok (.val (.bool true),agShrink.2.1),rsOuter) := by
  rfl

theorem rfp_initial_body (G : Source.Glob agEnv) :
    (Source.execS G packedStepFrame 10 0 none (.skip (R:=[]) (M:=false) (k:=⟨true,false⟩)) agShrink.2.1).run rsOuter=
      (.ok (.normal agShrink.2.1),rsOuter) := rfl

theorem rfp_initial_restore : agShrink.2.1.restore [agAliasTy,agAliasTy]=.ok agShrink.2.1 := rfl

/-- The literal guard needs ten eval horizons, so the next iteration at ten
fails at its guard's horizon nine before reaching its body or post. -/
def rfpBack (G : Source.Glob agEnv) : ForIterationObserver G packedStepFrame 10 0 none
    (.some (rbrDeepBool 9)) (.some (.tuple rtArgs)) (.skip (R:=[]) (M:=false) (k:=⟨true,false⟩)) where
  observe := fun prior _ s => ((.error .timeout,s),prior)
  source := fun _ _ _ => by
    rfl
  prior := fun _ _ _ _ member => member

def rfpJoined (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :=
  observePostThen G packedStepFrame 10 (.tuple rtArgs) (rfpPost G) (rfpBack G).observe prior agShrink.2.1 rsOuter

theorem rfp_post_success (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    ((rfpPost G).observe prior agShrink.2.1 rsOuter).1=(.ok agShrink.2.1,rsOuter) := by
  rfl

theorem rfp_joined_source (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rfpJoined G prior).1=
      ((do let l1 ← (do pure (← Source.EM.sub agShrink.2.1 (Source.evalE G packedStepFrame 10 (.tuple rtArgs))).2)
           Source.forIter G packedStepFrame 10 0 none (.some (rbrDeepBool 9)) (.some (.tuple rtArgs))
             (.skip (R:=[]) (M:=false) (k:=⟨true,false⟩)) l1) :
        Source.EM agEnv [] (Source.Out agEnv.layout [agAliasTy,agAliasTy] [agAliasTy,agAliasTy])).run rsOuter :=
  observePostThen_source G packedStepFrame 10 (.tuple rtArgs) (rfpPost G) (rfpBack G).observe
    (fun l1 => Source.forIter G packedStepFrame 10 0 none (.some (rbrDeepBool 9)) (.some (.tuple rtArgs))
      (.skip (R:=[]) (M:=false) (k:=⟨true,false⟩)) l1) (rfpBack G).source prior agShrink.2.1 rsOuter

theorem rfp_post_reached_by_for (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rfpJoined G prior).1=(Source.forIter G packedStepFrame 11 0 none (.some (rbrDeepBool 9))
      (.some (.tuple rtArgs)) (.skip (R:=[]) (M:=false) (k:=⟨true,false⟩)) agShrink.2.1).run rsOuter := by
  rw [rfp_joined_source]
  rfl

theorem rfp_late_timeout (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rfpJoined G prior).1=(.error .timeout,rsOuter) := by
  rfl

theorem rfp_post_head (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame (.val rtAlias)∈((rfpPost G).observe [] agShrink.2.1 rsOuter).2 := by
  exact captureTuplePost_head G packedStepFrame 8 (.local .here)
    (.cons (.tuple (.cons (.local (.there .here)) .nil)) .nil) [] agShrink.2.1 rsOuter _ (.val rtAlias) rfl

theorem rfp_joined_head (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame (.val rtAlias)∈(rfpJoined G []).2 := by
  exact observePostThen_post_scopes G packedStepFrame 10 (.tuple rtArgs) (rfpPost G) (rfpBack G).observe
    (rfpBack G).prior [] agShrink.2.1 rsOuter _ (rfp_post_head G)

theorem rfp_inside_post_timeout (G : Source.Glob agEnv) :
    (captureTuplePost G packedStepFrame 3 rtLateArgs [] agShrink.2.1 rsOuter).1=(.error .timeout,rsOuter) := by
  rfl

theorem rfp_inside_post_head (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame (.val rtAlias)∈(captureTuplePost G packedStepFrame 3 rtLateArgs [] agShrink.2.1 rsOuter).2 := by
  exact captureTuplePost_head G packedStepFrame 1 (.local .here) (.cons (.local (.there .here)) .nil)
    [] agShrink.2.1 rsOuter _ (.val rtAlias) rfl

end Solidity.Yul.Views.Controls
