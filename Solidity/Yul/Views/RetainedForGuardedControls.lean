import Solidity.Yul.Views.RetainedForGuarded
import Solidity.Yul.Views.RetainedForUnconditionalControls
import Solidity.Yul.Views.RetainedGuardObserverControls

/-! Present-guard for iterations reuse real comparison/body observers. False
exit, early control, timeout and guard conversion failure retain exact Source
results. Initializer and body tuple captures remain distinct proof obligations;
no exclusive provenance or frontend/compiler adequacy is inferred. -/
namespace Solidity.Yul.Views.Controls

def rfgObserver (G : Source.Glob agEnv) (flag : Bool)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) (n : Nat) :=
  guardedForIterationObserver G packedStepFrame n 0 none (rwhCondition flag) (.block (rboInner control))
    (rwhGuards G flag) (rwhBodies G control)

def rfgCapture (G : Source.Glob agEnv) (flag : Bool)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) (n : Nat)
    (prior : List (EntryReferenceScope agEnv)) :=
  (rfgObserver G flag control n).observe prior agShrink.2.1 rsOuter

theorem rfg_exact_source (G : Source.Glob agEnv) (flag : Bool)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) (n : Nat)
    (prior : List (EntryReferenceScope agEnv)) :
    (rfgCapture G flag control n prior).1=(Source.forIter G packedStepFrame n 0 none
      (.some (rwhCondition flag)) .none (.block (rboInner control)) agShrink.2.1).run rsOuter :=
  (rfgObserver G flag control n).source prior agShrink.2.1 rsOuter

theorem rfg_false (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rfgCapture G false .brk 16 prior).1=(.ok (.normal agShrink.2.1),rsOuter) := rwh_false G prior

theorem rfg_break (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rfgCapture G true .brk 16 prior).1=(.ok (.normal agShrink.2.1),rsOuter) := rwh_break G prior

theorem rfg_return (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rfgCapture G true (.ret rfl) 16 prior).1=(.ok (.ret agShrink.2.1),rsOuter) := rwh_return G prior

theorem rfg_continue_timeout (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rfgCapture G true .cont 16 prior).1=(.error .timeout,rsOuter) := rwh_continue_timeout G prior

theorem rfg_normal_timeout (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rfgCapture G true .skip 16 prior).1=(.error .timeout,rsOuter) := rwh_normal_timeout G prior

theorem rfg_false_guard_run (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    ((rwhGuards G false 15).observe prior agShrink.2.1 rsOuter).1=
      (.ok (.val (.bool false),agShrink.2.1),rsOuter) := by
  cases G with
  | mk prog pipeline fixed balance hasCode callee timestamp => cases pipeline <;> rfl

theorem rfg_false_inventory (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    rfgCapture G false .brk 16 prior=((.ok (.normal agShrink.2.1),rsOuter),
      ((rwhGuards G false 15).observe prior agShrink.2.1 rsOuter).2) :=
  guardedForIteration_guard_false G packedStepFrame 15 0 none (rwhCondition false) (.block (rboInner .brk))
    (rwhGuards G false) (rwhBodies G .brk) prior agShrink.2.1 agShrink.2.1 rsOuter rsOuter (rfg_false_guard_run G prior)

theorem rfg_body_tuple (G : Source.Glob agEnv)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) :
    runtimeScope packedStepFrame (.val rtAlias)∈(rfgCapture G true control 16 []).2 := rwh_tuple_retained G control

def rfgBadGuards (G : Source.Glob agEnv) (n : Nat) : GuardObserver G packedStepFrame n rguCondition :=
  comparisonGuardObserver G packedStepFrame n .eq (.tuple rcmpArgs) (.tuple rcmpArgs)

def rfgBad (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :=
  (guardedForIterationObserver G packedStepFrame 10 0 none rguCondition (.block (rboInner .brk))
    (rfgBadGuards G) (rwhBodies G .brk)).observe prior agShrink.2.1 rsOuter

theorem rfg_bad_inventory (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    rfgBad G prior=((.error (.stuck "not a plain value"),rsOuter),((rguGuard G).observe prior agShrink.2.1 rsOuter).2) :=
  guardedForIteration_guard_error G packedStepFrame 9 0 none rguCondition (.block (rboInner .brk))
    (rfgBadGuards G) (rwhBodies G .brk) prior agShrink.2.1 rsOuter rsOuter _ (rgu_guard_error G prior)

theorem rfg_guard_tuple (G : Source.Glob agEnv) : runtimeScope packedStepFrame rcmpTuple∈(rfgBad G []).2 := by
  rw [rfg_bad_inventory]
  exact rcmp_tuple_retained G

def rfgLoop (G : Source.Glob agEnv)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy])
    (prior : List (EntryReferenceScope agEnv)) :=
  (forLoopStatementObserver G packedStepFrame 16 0 none (.expr (.tuple rtArgs)) (.some (rwhCondition true)) .none
    (.block (rboInner control)) (rufInit G) (rfgObserver G true control 16) (lp:=false)).observe prior agShrink.2.1 rsOuter

theorem rfg_initializer_tuple (G : Source.Glob agEnv)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) :
    runtimeScope packedStepFrame (.val rtAlias)∈(rfgLoop G control []).2 := by
  exact observeForLoop_init_scopes G packedStepFrame 16 0 none (.expr (.tuple rtArgs))
    (.some (rwhCondition true)) .none (.block (rboInner control)) (rufInit G) (rfgObserver G true control 16)
    [] agShrink.2.1 rsOuter _ (captureTupleStatement_head G packedStepFrame 13 (.local .here)
      (.cons (.tuple (.cons (.local (.there .here)) .nil)) .nil) [] agShrink.2.1 rsOuter _ (.val rtAlias) rfl)

end Solidity.Yul.Views.Controls
