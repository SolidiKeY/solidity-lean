import Solidity.Yul.Views.RetainedIfThenObserver
import Solidity.Yul.Views.RetainedBranchObserverControls

/-! A false Source guard skips an actual observed body, retaining only prior
scopes. True enters it and retains its producers on halt. The minimal literal
guard horizon also distinguishes skipped versus entered timeout bodies. -/
namespace Solidity.Yul.Views.Controls

def ritObserver (G : Source.Glob agEnv) (flag : Bool) :=
  ifThenStatementObserver G packedStepFrame 10 0 none (.bool flag) (.block rtcBody) (rbrNo G)

def ritCapture (G : Source.Glob agEnv) (flag : Bool) (prior : List (EntryReferenceScope agEnv)) :=
  (ritObserver G flag).observe prior agShrink.2.1 rsOuter

theorem rit_exact_source (G : Source.Glob agEnv) (flag : Bool) (prior : List (EntryReferenceScope agEnv)) :
    (ritCapture G flag prior).1=
      (Source.execS G packedStepFrame 11 0 none (.ifThen (.bool flag) (.block rtcBody)) agShrink.2.1).run rsOuter :=
  (ritObserver G flag).source prior agShrink.2.1 rsOuter

theorem rit_false_skips (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    ritCapture G false prior=((.ok (.normal agShrink.2.1),rsOuter),prior) := by
  rfl

theorem rit_true_halts (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (ritCapture G true prior).1=(.error (.stuck "no default value"),rsOuter) := by
  rfl

theorem rit_true_scopes (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (ritCapture G true prior).2=((rbrNo G).observe prior agShrink.2.1 rsOuter).2 := by
  rfl

theorem rit_true_capture (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    runtimeScope packedStepFrame (.val rtAlias)∈(ritCapture G true prior).2 := by
  rw [rit_true_scopes]
  exact captureTupleItems_head G packedStepFrame 5 0 none (.local .here)
    (.cons (.tuple (.cons (.local (.there .here)) .nil)) .nil) rssTail prior agShrink.2.1 rsOuter _ (.val rtAlias) rfl

/-- Both the body observer and its timeout are concrete actual Source runs. -/
def ritLowBody (G : Source.Glob agEnv) :=
  blockStatementObserver G packedStepFrame 0 0 none rtcBody
    (tupleItemsObserver G packedStepFrame 0 0 none rtArgs rssTail)

def ritLow (G : Source.Glob agEnv) (flag : Bool) (prior : List (EntryReferenceScope agEnv)) :=
  (ifThenStatementObserver G packedStepFrame 1 0 none (.bool flag) (.block rtcBody) (ritLowBody G)).observe
    prior agShrink.2.1 rsOuter

theorem rit_low_false (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    ritLow G false prior=((.ok (.normal agShrink.2.1),rsOuter),prior) := by
  rfl

theorem rit_low_true (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (ritLow G true prior).1=(.error .timeout,rsOuter) := by
  rfl

theorem rit_prior (G : Source.Glob agEnv) (flag : Bool) (prior : List (EntryReferenceScope agEnv))
    (scope) (member : scope∈prior) : scope∈(ritCapture G flag prior).2 :=
  (ritObserver G flag).prior prior agShrink.2.1 rsOuter scope member

end Solidity.Yul.Views.Controls
