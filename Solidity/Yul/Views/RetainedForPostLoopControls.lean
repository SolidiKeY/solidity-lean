import Solidity.Yul.Views.RetainedForComposition
import Solidity.Yul.Views.RetainedForPostIterationControls

/-! Actual for initialization composes with the full present-post iteration.
The initializer and reached post inventories survive a later guard timeout.
Both captures can alias locals: membership is not exclusive provenance or
capture completeness, frontend admission, or compiler adequacy. -/
namespace Solidity.Yul.Views.Controls

def rfplInit (G : Source.Glob agEnv) : StatementObserver G packedStepFrame 11 0 none
    (.expr (.tuple rtArgs) (R:=[]) (M:=false) (k:=⟨true,false⟩)) where
  observe := captureTupleStatement G packedStepFrame 11 rtArgs
  source := captureTupleStatement_source G packedStepFrame 11 0 none rtArgs
  prior := captureTupleStatement_prior G packedStepFrame 11 rtArgs

def rfplObserver (G : Source.Glob agEnv) :=
  forLoopStatementObserver G packedStepFrame 11 0 none (.expr (.tuple rtArgs))
    (.some (rbrDeepBool 9)) (.some (.tuple rtArgs)) .skip (rfplInit G) (rfiObserver G 11) (lp:=false)

theorem rfpl_init_success (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    ((rfplInit G).observe prior agShrink.2.1 rsOuter).1=(.ok (.normal agShrink.2.1),rsOuter) := by
  rfl

theorem rfpl_source (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    ((rfplObserver G).observe prior agShrink.2.1 rsOuter).1=
      (Source.execS G packedStepFrame 12 0 none
        (.forLoop (l:=false) (u:=false) (.expr (.tuple rtArgs)) (.some (rbrDeepBool 9)) (.some (.tuple rtArgs))
          (.skip (R:=[]) (M:=false) (k:=⟨true,false⟩))) agShrink.2.1).run rsOuter :=
  (rfplObserver G).source prior agShrink.2.1 rsOuter

theorem rfpl_late_timeout (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    ((rfplObserver G).observe prior agShrink.2.1 rsOuter).1=(.error .timeout,rsOuter) := by
  rfl

/-- Actual initializer captures survive the entire loop's late failure. -/
theorem rfpl_initializer_head (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame (.val rtAlias)∈((rfplObserver G).observe [] agShrink.2.1 rsOuter).2 := by
  exact observeForLoop_init_scopes G packedStepFrame 11 0 none (.expr (.tuple rtArgs))
    (.some (rbrDeepBool 9)) (.some (.tuple rtArgs)) .skip (rfplInit G) (rfiObserver G 11)
    [] agShrink.2.1 rsOuter _
    (captureTupleStatement_head G packedStepFrame 8 (.local .here)
      (.cons (.tuple (.cons (.local (.there .here)) .nil)) .nil)
      [] agShrink.2.1 rsOuter _ (.val rtAlias) rfl)

/-- The successful test/body/restoration prefix reaches a tuple post for any
inherited inventory; this is stronger than equality of final timeout errors. -/
theorem rfpl_iteration_post_head (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    runtimeScope packedStepFrame (.val rtAlias)∈((rfiObserver G 11).observe prior agShrink.2.1 rsOuter).2 := by
  exact observeForPostIteration_normal_post_scopes G packedStepFrame 10 0 none
    (.some (rbrDeepBool 9)) (.tuple rtArgs) .skip (rfiTests G) (rfiBodies G) (rfiPosts G)
    prior agShrink.2.1 agShrink.2.1 agShrink.2.1 agShrink.2.1 rsOuter rsOuter rsOuter
    rfl rfl rfl _
    (captureTuplePost_head G packedStepFrame 8 (.local .here)
      (.cons (.tuple (.cons (.local (.there .here)) .nil)) .nil)
      prior agShrink.2.1 rsOuter _ (.val rtAlias) rfl)

/-- The post inventory survives for-loop composition after normal init. -/
theorem rfpl_post_head (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame (.val rtAlias)∈((rfplObserver G).observe [] agShrink.2.1 rsOuter).2 := by
  have inventory := observeForLoop_iteration_scopes G packedStepFrame 11 0 none (.expr (.tuple rtArgs))
    (.some (rbrDeepBool 9)) (.some (.tuple rtArgs)) .skip (rfplInit G) (rfiObserver G 11)
    [] agShrink.2.1 agShrink.2.1 rsOuter rsOuter (rfpl_init_success G [])
  change runtimeScope packedStepFrame (.val rtAlias)∈
    (observeForLoop G packedStepFrame 11 0 none (.expr (.tuple rtArgs))
      (.some (rbrDeepBool 9)) (.some (.tuple rtArgs)) .skip (rfplInit G) (rfiObserver G 11)
      [] agShrink.2.1 rsOuter).2
  rw [inventory]
  exact rfpl_iteration_post_head G _

/-- Continue has no expression; it still reaches the actual present post. -/
def rfplContinues (G : Source.Glob agEnv) (n : Nat) :
    StatementObserver G packedStepFrame n 0 none
      (.cont (Γ:=[agAliasTy,agAliasTy]) (R:=[]) (M:=false) (u:=false)) where
  observe := fun prior l s => ((Source.execS G packedStepFrame n 0 none .cont l).run s,prior)
  source := fun _ _ _ => rfl
  prior := fun _ _ _ _ member => member

def rfplContinueIteration (G : Source.Glob agEnv) :=
  postForIterationObserver G packedStepFrame 11 0 none (.some (rbrDeepBool 9)) (.tuple rtArgs)
    .cont (rfiTests G) (rfplContinues G) (rfiPosts G)

def rfplContinueObserver (G : Source.Glob agEnv) :=
  forLoopStatementObserver G packedStepFrame 11 0 none (.expr (.tuple rtArgs))
    (.some (rbrDeepBool 9)) (.some (.tuple rtArgs)) .cont (rfplInit G) (rfplContinueIteration G) (lp:=false)

theorem rfpl_continue_source (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    ((rfplContinueObserver G).observe prior agShrink.2.1 rsOuter).1=
      (Source.execS G packedStepFrame 12 0 none
        (.forLoop (l:=false) (u:=false) (.expr (.tuple rtArgs)) (.some (rbrDeepBool 9)) (.some (.tuple rtArgs))
          (.cont (R:=[]) (M:=false))) agShrink.2.1).run rsOuter :=
  (rfplContinueObserver G).source prior agShrink.2.1 rsOuter

theorem rfpl_continue_late_timeout (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    ((rfplContinueObserver G).observe prior agShrink.2.1 rsOuter).1=(.error .timeout,rsOuter) := by
  rfl

/-- Continue reaches and retains the post before the next guard fails. -/
theorem rfpl_continue_iteration_post_head (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    runtimeScope packedStepFrame (.val rtAlias)∈((rfplContinueIteration G).observe prior agShrink.2.1 rsOuter).2 := by
  exact observeForPostIteration_continue_post_scopes G packedStepFrame 10 0 none
    (.some (rbrDeepBool 9)) (.tuple rtArgs) .cont (rfiTests G) (rfplContinues G) (rfiPosts G)
    prior agShrink.2.1 agShrink.2.1 agShrink.2.1 rsOuter rsOuter rsOuter rfl rfl _
    (captureTuplePost_head G packedStepFrame 8 (.local .here)
      (.cons (.tuple (.cons (.local (.there .here)) .nil)) .nil)
      prior agShrink.2.1 rsOuter _ (.val rtAlias) rfl)

theorem rfpl_continue_post_head (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame (.val rtAlias)∈((rfplContinueObserver G).observe [] agShrink.2.1 rsOuter).2 := by
  have inventory := observeForLoop_iteration_scopes G packedStepFrame 11 0 none (.expr (.tuple rtArgs))
    (.some (rbrDeepBool 9)) (.some (.tuple rtArgs)) .cont (rfplInit G) (rfplContinueIteration G)
    [] agShrink.2.1 agShrink.2.1 rsOuter rsOuter (rfpl_init_success G [])
  change runtimeScope packedStepFrame (.val rtAlias)∈
    (observeForLoop G packedStepFrame 11 0 none (.expr (.tuple rtArgs))
      (.some (rbrDeepBool 9)) (.some (.tuple rtArgs)) .cont (rfplInit G) (rfplContinueIteration G)
      [] agShrink.2.1 rsOuter).2
  rw [inventory]
  exact rfpl_continue_iteration_post_head G _

end Solidity.Yul.Views.Controls
