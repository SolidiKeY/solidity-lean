import Solidity.Yul.Views.RetainedWhileObserver
import Solidity.Yul.Views.RetainedBlockObserverControls

/-! Inhabited finite-horizon Source loops with observed tuple-producing bodies.
Actual break/return propagate, continue/normal iteration time out, and false
comparison guards skip the body. These are capture-transport controls, not
compiler adequacy, frontend admission or general producer completeness. -/
namespace Solidity.Yul.Views.Controls

def rwhCondition (flag : Bool) : Source.RExpr agEnv [agAliasTy,agAliasTy] .bool :=
  .compare .eq (.bool flag) (.bool true)

def rwhGuards (G : Source.Glob agEnv) (flag : Bool) (n : Nat) : GuardObserver G packedStepFrame n (rwhCondition flag) :=
  comparisonGuardObserver G packedStepFrame n .eq (.bool flag) (.bool true)

def rwhBodies (G : Source.Glob agEnv)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) :
    (n : Nat) → StatementObserver G packedStepFrame n 0 none (.block (rboInner control))
  | 0 => zeroStatementObserver G packedStepFrame 0 none (.block (rboInner control))
  | n+1 => blockStatementObserver G packedStepFrame n 0 none (rboInner control)
      (tupleItemsObserver G packedStepFrame n 0 none rtArgs (.stmt control .nil))

def rwhObserver (G : Source.Glob agEnv) (flag : Bool)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) (n : Nat) :=
  whileStatementObserver G packedStepFrame n 0 none (rwhCondition flag) (.block (rboInner control))
    (rwhGuards G flag) (rwhBodies G control) (lp:=false)

def rwhCapture (G : Source.Glob agEnv) (flag : Bool)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) (n : Nat)
    (prior : List (EntryReferenceScope agEnv)) :=
  (rwhObserver G flag control n).observe prior agShrink.2.1 rsOuter

theorem rwh_exact_source (G : Source.Glob agEnv) (flag : Bool)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) (n : Nat)
    (prior : List (EntryReferenceScope agEnv)) :
    (rwhCapture G flag control n prior).1=
      (Source.execS G packedStepFrame n 0 none
        (.whileLoop (l:=false) (rwhCondition flag) (.block (rboInner control))) agShrink.2.1).run rsOuter :=
  (rwhObserver G flag control n).source prior agShrink.2.1 rsOuter

theorem rwh_false (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rwhCapture G false .brk 16 prior).1=(.ok (.normal agShrink.2.1),rsOuter) := by
  cases G with
  | mk prog pipeline fixed balance hasCode callee timestamp => cases pipeline <;> rfl

theorem rwh_break (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rwhCapture G true .brk 16 prior).1=(.ok (.normal agShrink.2.1),rsOuter) := by
  cases G with
  | mk prog pipeline fixed balance hasCode callee timestamp => cases pipeline <;> rfl

theorem rwh_return (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rwhCapture G true (.ret rfl) 16 prior).1=(.ok (.ret agShrink.2.1),rsOuter) := by
  cases G with
  | mk prog pipeline fixed balance hasCode callee timestamp => cases pipeline <;> rfl

theorem rwh_continue_timeout (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rwhCapture G true .cont 16 prior).1=(.error .timeout,rsOuter) := by
  rw [rwh_exact_source]
  cases G with
  | mk prog pipeline fixed balance hasCode callee timestamp => cases pipeline <;> rfl

theorem rwh_normal_timeout (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rwhCapture G true .skip 16 prior).1=(.error .timeout,rsOuter) := by
  rw [rwh_exact_source]
  cases G with
  | mk prog pipeline fixed balance hasCode callee timestamp => cases pipeline <;> rfl

theorem rwh_true_guard (G : Source.Glob agEnv) :
    ((rwhGuards G true 15).observe [] agShrink.2.1 rsOuter).1=
      (.ok (.val (.bool true),agShrink.2.1),rsOuter) := by
  cases G with
  | mk prog pipeline fixed balance hasCode callee timestamp => cases pipeline <;> rfl

/-- A captured first-body tuple survives any later control or iteration halt. -/
theorem rwh_tuple_retained (G : Source.Glob agEnv)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) :
    runtimeScope packedStepFrame (.val rtAlias)∈(rwhCapture G true control 16 []).2 := by
  exact observeWhile_body_scopes G packedStepFrame 15 0 none (rwhCondition true) (.block (rboInner control))
    (rwhGuards G true) (rwhBodies G control) [] agShrink.2.1 agShrink.2.1 rsOuter rsOuter (rwh_true_guard G) _
    (captureTupleItems_head G packedStepFrame 10 0 none (.local .here)
      (.cons (.tuple (.cons (.local (.there .here)) .nil)) .nil) (.stmt control .nil)
      ((rwhGuards G true 15).observe [] agShrink.2.1 rsOuter).2 agShrink.2.1 rsOuter _ (.val rtAlias) rfl) (lp:=false)

theorem rwh_prior (G : Source.Glob agEnv) (flag : Bool)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) (n : Nat)
    (prior : List (EntryReferenceScope agEnv)) (scope) (member : scope∈prior) :
    scope∈(rwhCapture G flag control n prior).2 :=
  (rwhObserver G flag control n).prior prior agShrink.2.1 rsOuter scope member

end Solidity.Yul.Views.Controls
