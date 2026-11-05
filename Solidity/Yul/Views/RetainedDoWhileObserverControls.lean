import Solidity.Yul.Views.RetainedDoWhileObserver
import Solidity.Yul.Views.RetainedWhileObserverControls
import Solidity.Yul.Views.RetainedComparisonControls

/-! Actual body-first loop controls distinguish break/return bypass from
continue reaching the test. First-body tuple captures survive false exit,
conversion failure and finite-horizon iteration timeout. Tuple comparison is
a typed evaluator boundary, not a frontend-admission claim. -/
namespace Solidity.Yul.Views.Controls

def rdwObserver (G : Source.Glob agEnv) (flag : Bool)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) (n : Nat) :=
  doWhileStatementObserver G packedStepFrame n 0 none (.block (rboInner control)) (rwhCondition flag)
    (rwhGuards G flag) (rwhBodies G control) (lp:=false)

def rdwCapture (G : Source.Glob agEnv) (flag : Bool)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) (n : Nat)
    (prior : List (EntryReferenceScope agEnv)) :=
  (rdwObserver G flag control n).observe prior agShrink.2.1 rsOuter

theorem rdw_exact_source (G : Source.Glob agEnv) (flag : Bool)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) (n : Nat)
    (prior : List (EntryReferenceScope agEnv)) :
    (rdwCapture G flag control n prior).1=
      (Source.execS G packedStepFrame n 0 none
        (.doWhile (l:=false) (.block (rboInner control)) (rwhCondition flag)) agShrink.2.1).run rsOuter :=
  (rdwObserver G flag control n).source prior agShrink.2.1 rsOuter

theorem rdw_false_after_body (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rdwCapture G false .skip 16 prior).1=(.ok (.normal agShrink.2.1),rsOuter) := by
  cases G with
  | mk prog pipeline fixed balance hasCode callee timestamp => cases pipeline <;> rfl

theorem rdw_continue_false (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rdwCapture G false .cont 16 prior).1=(.ok (.normal agShrink.2.1),rsOuter) := by
  cases G with
  | mk prog pipeline fixed balance hasCode callee timestamp => cases pipeline <;> rfl

theorem rdw_continue_timeout (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rdwCapture G true .cont 16 prior).1=(.error .timeout,rsOuter) := by
  rw [rdw_exact_source]
  cases G with
  | mk prog pipeline fixed balance hasCode callee timestamp => cases pipeline <;> rfl

theorem rdw_normal_timeout (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rdwCapture G true .skip 16 prior).1=(.error .timeout,rsOuter) := by
  rw [rdw_exact_source]
  cases G with
  | mk prog pipeline fixed balance hasCode callee timestamp => cases pipeline <;> rfl

theorem rdw_tuple_retained (G : Source.Glob agEnv) (flag : Bool)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) :
    runtimeScope packedStepFrame (.val rtAlias)∈(rdwCapture G flag control 16 []).2 := by
  exact observeDoWhile_body_scopes G packedStepFrame 15 0 none (.block (rboInner control)) (rwhCondition flag)
    (rwhGuards G flag) (rwhBodies G control) [] agShrink.2.1 rsOuter _
    (captureTupleItems_head G packedStepFrame 10 0 none (.local .here)
      (.cons (.tuple (.cons (.local (.there .here)) .nil)) .nil) (.stmt control .nil)
      [] agShrink.2.1 rsOuter _ (.val rtAlias) rfl) (lp:=false)

def rdwBadCondition : Source.RExpr agEnv [agAliasTy,agAliasTy] .bool :=
  .compare .eq (.tuple rcmpArgs) (.tuple rcmpArgs)

def rdwBadGuards (G : Source.Glob agEnv) (n : Nat) : GuardObserver G packedStepFrame n rdwBadCondition :=
  comparisonGuardObserver G packedStepFrame n .eq (.tuple rcmpArgs) (.tuple rcmpArgs)

def rdwBad (G : Source.Glob agEnv)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy])
    (prior : List (EntryReferenceScope agEnv)) :=
  (doWhileStatementObserver G packedStepFrame 16 0 none (.block (rboInner control)) rdwBadCondition
    (rdwBadGuards G) (rwhBodies G control) (lp:=false)).observe prior agShrink.2.1 rsOuter

theorem rdw_break_skips_bad_guard (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rdwBad G .brk prior).1=(.ok (.normal agShrink.2.1),rsOuter) := by
  rfl

theorem rdw_return_skips_bad_guard (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rdwBad G (.ret rfl) prior).1=(.ok (.ret agShrink.2.1),rsOuter) := by
  rfl

theorem rdw_continue_hits_bad_guard (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rdwBad G .cont prior).1=(.error (.stuck "not a plain value"),rsOuter) := by
  cases G with
  | mk prog pipeline fixed balance hasCode callee timestamp => cases pipeline <;> rfl

theorem rdw_prior (G : Source.Glob agEnv) (flag : Bool)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) (n : Nat)
    (prior : List (EntryReferenceScope agEnv)) (scope) (member : scope∈prior) :
    scope∈(rdwCapture G flag control n prior).2 :=
  (rdwObserver G flag control n).prior prior agShrink.2.1 rsOuter scope member

end Solidity.Yul.Views.Controls
