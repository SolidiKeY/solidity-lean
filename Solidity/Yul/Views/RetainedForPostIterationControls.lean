import Solidity.Yul.Views.RetainedForPostIteration
import Solidity.Yul.Views.RetainedForPostControls

/-! A full observed iteration reaches a tuple post before the next guard times
out. Independent prefix facts and retained scope membership establish reachability;
final error equality alone is not used for that claim. Break bypasses the post. -/
namespace Solidity.Yul.Views.Controls

/-- This scalar guard contains no reference-valued subexpression. -/
def rfiGuards (G : Source.Glob agEnv) (n : Nat) :
    GuardObserver G packedStepFrame n (rbrDeepBool 9) where
  observe := fun prior l s => ((Source.EM.sub l (Source.evalE G packedStepFrame n (rbrDeepBool 9))).run s,prior)
  source := fun _ _ _ => rfl
  prior := fun _ _ _ _ member => member

/-- Skip has no expression to capture; its actual timeout behavior is retained. -/
def rfiBodies (G : Source.Glob agEnv) (n : Nat) :
    StatementObserver G packedStepFrame n 0 none
      (.skip (Γ:=[agAliasTy,agAliasTy]) (R:=[]) (M:=false) (k:=⟨true,false⟩)) where
  observe := fun prior l s => ((Source.execS G packedStepFrame n 0 none .skip l).run s,prior)
  source := fun _ _ _ => rfl
  prior := fun _ _ _ _ member => member

def rfiTests (G : Source.Glob agEnv) (n : Nat) :=
  presentForTestObserver G packedStepFrame n (rbrDeepBool 9) (rfiGuards G n)

def rfiPosts (G : Source.Glob agEnv) (n : Nat) := tuplePostObserver G packedStepFrame n rtArgs

def rfiObserver (G : Source.Glob agEnv) (n : Nat) :=
  postForIterationObserver G packedStepFrame n 0 none (.some (rbrDeepBool 9)) (.tuple rtArgs)
    (.skip (R:=[]) (M:=false) (k:=⟨true,false⟩)) (rfiTests G) (rfiBodies G) (rfiPosts G)

theorem rfi_source (G : Source.Glob agEnv) (n : Nat) (prior : List (EntryReferenceScope agEnv)) :
    ((rfiObserver G n).observe prior agShrink.2.1 rsOuter).1=
      (Source.forIter G packedStepFrame n 0 none (.some (rbrDeepBool 9)) (.some (.tuple rtArgs))
        (.skip (R:=[]) (M:=false) (k:=⟨true,false⟩)) agShrink.2.1).run rsOuter :=
  (rfiObserver G n).source prior agShrink.2.1 rsOuter

theorem rfi_late_timeout (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    ((rfiObserver G 11).observe prior agShrink.2.1 rsOuter).1=(.error .timeout,rsOuter) := by
  rw [rfi_source]
  rfl

/-- The actual test, skip and restoration reach the post at horizon ten. -/
theorem rfi_post_head (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame (.val rtAlias)∈((rfiObserver G 11).observe [] agShrink.2.1 rsOuter).2 := by
  exact observeForPostIteration_normal_post_scopes G packedStepFrame 10 0 none
    (.some (rbrDeepBool 9)) (.tuple rtArgs) .skip (rfiTests G) (rfiBodies G) (rfiPosts G)
    [] agShrink.2.1 agShrink.2.1 agShrink.2.1 agShrink.2.1 rsOuter rsOuter rsOuter
    rfl rfl rfl _ (rfp_post_head G)

/-- No test is evaluated for the absent-test case, even at test horizon zero. -/
theorem rfi_absent_zero (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (absentForTestObserver G packedStepFrame 0).observe prior agShrink.2.1 rsOuter=
      ((.ok (true,agShrink.2.1),rsOuter),prior) := rfl

/-- Break has no expression; the present tuple post must be bypassed. -/
def rfiBreaks (G : Source.Glob agEnv) (n : Nat) :
    StatementObserver G packedStepFrame n 0 none
      (.brk (Γ:=[agAliasTy,agAliasTy]) (R:=[]) (M:=false) (u:=false)) where
  observe := fun prior l s => ((Source.execS G packedStepFrame n 0 none .brk l).run s,prior)
  source := fun _ _ _ => rfl
  prior := fun _ _ _ _ member => member

theorem rfi_break_bypasses_post (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (postForIterationObserver G packedStepFrame 2 0 none .none (.tuple rtArgs) .brk
      (absentForTestObserver G packedStepFrame) (rfiBreaks G) (rfiPosts G)).observe prior agShrink.2.1 rsOuter=
        ((.ok (.normal agShrink.2.1),rsOuter),prior) := rfl

end Solidity.Yul.Views.Controls
