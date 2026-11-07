import Solidity.Yul.Views.RetainedForOptional
import Solidity.Yul.Views.RetainedForGuardedControls
import Solidity.Yul.Views.RetainedForPostLoopControls

/-! All four optional test/post routes use existing actual observer producers.
Absent expressions introduce no evaluator work. The present/present route
composes actual initialization and retains a reached tuple post through timeout.
These are selector controls, not completeness or compiler adequacy. -/
namespace Solidity.Yul.Views.Controls

def rfoAbsent (G : Source.Glob agEnv) :=
  optionalForIterationObserver G packedStepFrame 16 0 none .none .none (.block (rboInner .brk))
    PUnit.unit PUnit.unit (rwhBodies G .brk)

theorem rfo_absent_route (G : Source.Glob agEnv) : rfoAbsent G=rufObserver G .brk 16 := rfl

theorem rfo_absent_break (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    ((rfoAbsent G).observe prior agShrink.2.1 rsOuter).1=(.ok (.normal agShrink.2.1),rsOuter) :=
  ruf_break G prior

theorem rfo_absent_body_head (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame (.val rtAlias)∈((rfoAbsent G).observe [] agShrink.2.1 rsOuter).2 :=
  ruf_body_tuple G .brk

def rfoGuarded (G : Source.Glob agEnv) (flag : Bool) :=
  optionalForIterationObserver G packedStepFrame 16 0 none (.some (rwhCondition flag)) .none
    (.block (rboInner .brk)) (rwhGuards G flag) PUnit.unit (rwhBodies G .brk)

theorem rfo_guarded_route (G : Source.Glob agEnv) (flag : Bool) :
    rfoGuarded G flag=rfgObserver G flag .brk 16 := rfl

theorem rfo_false (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    ((rfoGuarded G false).observe prior agShrink.2.1 rsOuter).1=(.ok (.normal agShrink.2.1),rsOuter) :=
  rfg_false G prior

def rfoPost (G : Source.Glob agEnv) :=
  optionalForIterationObserver G packedStepFrame 2 0 none .none (.some (.tuple rtArgs))
    .brk PUnit.unit (rfiPosts G) (rfiBreaks G)

theorem rfo_post_route (G : Source.Glob agEnv) :
    rfoPost G=postForIterationObserver G packedStepFrame 2 0 none .none (.tuple rtArgs) .brk
      (absentForTestObserver G packedStepFrame) (rfiBreaks G) (rfiPosts G) := rfl

theorem rfo_break_bypasses_post (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rfoPost G).observe prior agShrink.2.1 rsOuter=((.ok (.normal agShrink.2.1),rsOuter),prior) :=
  rfi_break_bypasses_post G prior

def rfoFull (G : Source.Glob agEnv) :=
  optionalForLoopStatementObserver G packedStepFrame 11 0 none (.expr (.tuple rtArgs))
    (.some (rbrDeepBool 9)) (.some (.tuple rtArgs)) .skip (rfplInit G)
    (rfiGuards G) (rfiPosts G) (rfiBodies G) (lp:=false)

theorem rfo_full_route (G : Source.Glob agEnv) : rfoFull G=rfplObserver G := rfl

theorem rfo_full_source (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    ((rfoFull G).observe prior agShrink.2.1 rsOuter).1=
      (Source.execS G packedStepFrame 12 0 none
        (.forLoop (l:=false) (u:=false) (.expr (.tuple rtArgs)) (.some (rbrDeepBool 9)) (.some (.tuple rtArgs))
          (.skip (R:=[]) (M:=false) (k:=⟨true,false⟩))) agShrink.2.1).run rsOuter :=
  (rfoFull G).source prior agShrink.2.1 rsOuter

theorem rfo_full_late_timeout (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    ((rfoFull G).observe prior agShrink.2.1 rsOuter).1=(.error .timeout,rsOuter) :=
  rfpl_late_timeout G prior

theorem rfo_full_post_head (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame (.val rtAlias)∈((rfoFull G).observe [] agShrink.2.1 rsOuter).2 :=
  rfpl_post_head G

end Solidity.Yul.Views.Controls
