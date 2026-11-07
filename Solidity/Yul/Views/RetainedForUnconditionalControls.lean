import Solidity.Yul.Views.RetainedForUnconditional
import Solidity.Yul.Views.RetainedForComposition
import Solidity.Yul.Views.RetainedWhileObserverControls

/-! Actual unconditional for iterations with tuple-producing bodies. Concrete
break/return and normal/continue timeout preserve captures. The same observer
plugs into actual for initialization. Aliases also remain in locals; neither
exclusive provenance nor general guard/post or compiler adequacy is asserted. -/
namespace Solidity.Yul.Views.Controls

def rufObserver (G : Source.Glob agEnv)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) (n : Nat) :=
  unconditionalForIterationObserver G packedStepFrame n 0 none (.block (rboInner control)) (rwhBodies G control)

def rufCapture (G : Source.Glob agEnv)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) (n : Nat)
    (prior : List (EntryReferenceScope agEnv)) :=
  (rufObserver G control n).observe prior agShrink.2.1 rsOuter

theorem ruf_exact_source (G : Source.Glob agEnv)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) (n : Nat)
    (prior : List (EntryReferenceScope agEnv)) :
    (rufCapture G control n prior).1=
      (Source.forIter G packedStepFrame n 0 none .none .none (.block (rboInner control)) agShrink.2.1).run rsOuter :=
  (rufObserver G control n).source prior agShrink.2.1 rsOuter

theorem ruf_break (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rufCapture G .brk 16 prior).1=(.ok (.normal agShrink.2.1),rsOuter) := by
  rfl

theorem ruf_return (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rufCapture G (.ret rfl) 16 prior).1=(.ok (.ret agShrink.2.1),rsOuter) := by
  rfl

/-- These concrete bodies either time out or finish with their actual
unchanged locals/state. This is uniform in the owner horizon. -/
theorem ruf_repeating_body (G : Source.Glob agEnv) (flag : Bool) (n : Nat) :
    (Source.execS G packedStepFrame n 0 none
      (.block (rboInner (if flag then .cont else .skip))) agShrink.2.1).run rsOuter=(.error .timeout,rsOuter) ∨
    (Source.execS G packedStepFrame n 0 none
      (.block (rboInner (if flag then .cont else .skip))) agShrink.2.1).run rsOuter=
      (.ok (if flag then .cont agShrink.2.1 else .normal agShrink.2.1),rsOuter) := by
  by_cases small : n < 12
  · have options : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 ∨ n=7 ∨ n=8 ∨ n=9 ∨ n=10 ∨ n=11 := by omega
    rcases options with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      cases flag <;> first | (left;rfl) | (right;rfl)
  · obtain ⟨k,rfl⟩ : ∃ k, n=k+12 := ⟨n-12,by omega⟩
    cases flag <;> right <;> rfl

theorem ruf_repeating_do_timeout (G : Source.Glob agEnv) (flag : Bool) (n : Nat) :
    (Source.execS G packedStepFrame n 0 none
      (.doWhile (l:=false) (.block (rboInner (if flag then .cont else .skip))) (.bool true)) agShrink.2.1).run rsOuter=
        (.error .timeout,rsOuter) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      rw [Source.execS,Source.Hoare.run_bind]
      rcases ruf_repeating_body G flag (n+1) with timeout | completed
      · rw [timeout]
      · cases flag <;> rw [completed] <;> exact ih

theorem ruf_repeating_timeout (G : Source.Glob agEnv) (flag : Bool) (n : Nat) :
    (Source.forIter G packedStepFrame n 0 none .none .none
      (.block (rboInner (if flag then .cont else .skip))) agShrink.2.1).run rsOuter=(.error .timeout,rsOuter) := by
  rw [forIter_none_none_eq_doWhile (lp:=false)]
  exact ruf_repeating_do_timeout G flag n

theorem ruf_continue_timeout (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rufCapture G .cont 16 prior).1=(.error .timeout,rsOuter) := by
  rw [ruf_exact_source]
  exact ruf_repeating_timeout G true 16

theorem ruf_normal_timeout (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rufCapture G .skip 16 prior).1=(.error .timeout,rsOuter) := by
  rw [ruf_exact_source]
  exact ruf_repeating_timeout G false 16

theorem ruf_body_tuple (G : Source.Glob agEnv)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) :
    runtimeScope packedStepFrame (.val rtAlias)∈(rufCapture G control 16 []).2 := by
  exact unconditionalForIteration_body_scopes G packedStepFrame 15 0 none (.block (rboInner control))
    (rwhBodies G control) [] agShrink.2.1 rsOuter _
    (captureTupleItems_head G packedStepFrame 10 0 none (.local .here)
      (.cons (.tuple (.cons (.local (.there .here)) .nil)) .nil) (.stmt control .nil)
      [] agShrink.2.1 rsOuter _ (.val rtAlias) rfl)

def rufInit (G : Source.Glob agEnv) : StatementObserver G packedStepFrame 16 0 none
    (.expr (.tuple rtArgs) (R:=[]) (M:=false) (k:=⟨true,false⟩)) where
  observe := captureTupleStatement G packedStepFrame 16 rtArgs
  source := captureTupleStatement_source G packedStepFrame 16 0 none rtArgs
  prior := captureTupleStatement_prior G packedStepFrame 16 rtArgs

def rufLoop (G : Source.Glob agEnv)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy])
    (prior : List (EntryReferenceScope agEnv)) :=
  (forLoopStatementObserver G packedStepFrame 16 0 none (.expr (.tuple rtArgs)) .none .none (.block (rboInner control))
    (rufInit G) (rufObserver G control 16) (lp:=false)).observe prior agShrink.2.1 rsOuter

theorem ruf_loop_break (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rufLoop G .brk prior).1=(.ok (.normal agShrink.2.1),rsOuter) := by
  rfl

theorem ruf_loop_return (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rufLoop G (.ret rfl) prior).1=(.ok (.ret agShrink.2.1),rsOuter) := by
  rfl

theorem ruf_initializer_tuple (G : Source.Glob agEnv)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) :
    runtimeScope packedStepFrame (.val rtAlias)∈(rufLoop G control []).2 := by
  exact observeForLoop_init_scopes G packedStepFrame 16 0 none (.expr (.tuple rtArgs)) .none .none
    (.block (rboInner control)) (rufInit G) (rufObserver G control 16) [] agShrink.2.1 rsOuter _
    (captureTupleStatement_head G packedStepFrame 13 (.local .here)
      (.cons (.tuple (.cons (.local (.there .here)) .nil)) .nil) [] agShrink.2.1 rsOuter _ (.val rtAlias) rfl)

end Solidity.Yul.Views.Controls
