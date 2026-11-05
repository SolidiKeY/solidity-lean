import Solidity.Yul.Views.RetainedTupleComposition
import Solidity.Yul.Views.RetainedTupleSequenceControls

/-! Two actual tuple expression statements precede a Source declaration halt.
The first and tail captures compose, and a prior scope survives. These fixtures
assert neither exclusive tuple provenance nor general recursive coverage. -/
namespace Solidity.Yul.Views.Controls

def rtcBody : Source.RItems agEnv [] false Source.SCtx.body
    [agAliasTy,agAliasTy] [agAliasTy,agAliasTy,agAliasTy] :=
  .stmt (.expr (.tuple rtArgs)) rssTail

def rtcObserver (G : Source.Glob agEnv) :=
  tupleThenObserver G packedStepFrame 9 0 none rtArgs rtcBody
    (tupleItemsObserver G packedStepFrame 9 0 none rtArgs rssTail)

def rtcFirst (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :=
  captureTupleStatement G packedStepFrame 9 rtArgs prior agShrink.2.1 rsOuter

def rtcCapture (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :=
  (rtcObserver G).observe prior agShrink.2.1 rsOuter

theorem rtc_prefix_normal (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rtcFirst G prior).1=(.ok (.normal agShrink.2.1),rsOuter) := rfl

theorem rtc_exact_source (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rtcCapture G prior).1=
      (Source.execItems G packedStepFrame 10 0 none (.stmt (.expr (.tuple rtArgs)) rtcBody) agShrink.2.1).run rsOuter :=
  (rtcObserver G).source prior agShrink.2.1 rsOuter

theorem rtc_actual_halt (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rtcCapture G prior).1=(.error (.stuck "no default value"),rsOuter) := by
  rfl

theorem rtc_tail_scopes (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rtcCapture G prior).2=
      (captureTupleItems G packedStepFrame 9 0 none rtArgs rssTail (rtcFirst G prior).2 agShrink.2.1 rsOuter).2 :=
  observeTupleThen_normal_scopes G packedStepFrame 9 0 none rtArgs rtcBody
    (tupleItemsObserver G packedStepFrame 9 0 none rtArgs rssTail) prior
    agShrink.2.1 agShrink.2.1 rsOuter rsOuter (rtc_prefix_normal G prior)

theorem rtc_prefix_retained (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    runtimeScope packedStepFrame (.val rtAlias)∈(rtcCapture G prior).2 := by
  exact observeTupleThen_prefix G packedStepFrame 9 0 none rtArgs rtcBody
    (tupleItemsObserver G packedStepFrame 9 0 none rtArgs rssTail) prior agShrink.2.1 rsOuter _
    (captureTupleStatement_head G packedStepFrame 6 (.local .here)
      (.cons (.tuple (.cons (.local (.there .here)) .nil)) .nil) prior agShrink.2.1 rsOuter _ (.val rtAlias) rfl)

theorem rtc_tail_retained (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    runtimeScope packedStepFrame (.val rtAlias)∈(rtcCapture G prior).2 := by
  rw [rtc_tail_scopes]
  exact captureTupleItems_head G packedStepFrame 5 0 none (.local .here)
    (.cons (.tuple (.cons (.local (.there .here)) .nil)) .nil) rssTail (rtcFirst G prior).2
    agShrink.2.1 rsOuter _ (.val rtAlias) rfl

theorem rtc_prior_retained (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv))
    (scope) (member : scope∈prior) : scope∈(rtcCapture G prior).2 :=
  (rtcObserver G).prior prior agShrink.2.1 rsOuter scope member

end Solidity.Yul.Views.Controls
