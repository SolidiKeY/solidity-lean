import Solidity.Yul.LocalBoolControl

/-! Concrete steps of actual Source.evalE for the new control adapter.
Child-execution premises below are real equations; the final clean composition
must discharge them using actual source runs, never assume a preparation law. -/
namespace Solidity.Yul.LocalBoolControl

/-- Run an actual Source action under separate locals, retaining the reached
world on both success and halt and exposing inner locals only on success. -/
theorem source_sub_run {env Γ Δ α} {action : Solidity.Source.EM env Δ α}
    {locals : Solidity.Source.Locals env.layout Δ}
    (outer : Solidity.Source.Locals env.layout Γ) {world afterWorld : Solidity.Source.St env}
    {after : Solidity.Source.Locals env.layout Δ} {result : Solidity.Source.R α}
    (actual : action.run (locals, world) = (result, (after, afterWorld))) :
    (Solidity.Source.EM.sub locals action).run (outer, world) =
      (result.map (fun value => (value, after)), (outer, afterWorld)) := by
  change action (locals, world) = _ at actual
  cases result <;> simp only [Solidity.Source.EM.sub, ExceptT.run, ExceptT.mk, actual, Except.map]

theorem source_and_error {env ctx} (left right : Solidity.Source.RExpr env ctx .bool)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (state next : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env)
    (halt : Solidity.Source.Halt)
    (actual : (Solidity.Source.evalE glob frame fuel left).run state = (.error halt,next)) :
    (Solidity.Source.evalE glob frame (fuel+1) (.binary .and left right)).run state =
      (.error halt,next) := by
  rw [Solidity.Source.evalE]
  simp only [reduceCtorEq,decide_true,decide_false,Bool.true_or,if_true]
  rw [Solidity.Source.Hoare.run_bind,actual]

theorem source_and_false {env ctx} (left right : Solidity.Source.RExpr env ctx .bool)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (state next : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env)
    (actual : (Solidity.Source.evalE glob frame fuel left).run state = (.ok (.val (.bool false)),next)) :
    (Solidity.Source.evalE glob frame (fuel+1) (.binary .and left right)).run state =
      (.ok (.val (.bool false)),next) := by
  rw [Solidity.Source.evalE]
  simp only [reduceCtorEq,decide_true,decide_false,Bool.true_or,if_true]
  rw [Solidity.Source.Hoare.run_bind,actual]
  rfl

theorem source_and_true {env ctx} (left right : Solidity.Source.RExpr env ctx .bool)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (state next : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env)
    (actual : (Solidity.Source.evalE glob frame fuel left).run state = (.ok (.val (.bool true)),next)) :
    (Solidity.Source.evalE glob frame (fuel+1) (.binary .and left right)).run state =
      (Solidity.Source.evalE glob frame fuel right).run next := by
  rw [Solidity.Source.evalE]
  simp only [reduceCtorEq,decide_true,decide_false,Bool.true_or,if_true]
  rw [Solidity.Source.Hoare.run_bind,actual]
  change (do
    let value ← Solidity.Source.getV (← Solidity.Source.evalE glob frame fuel right)
    pure (Solidity.Source.RVal.val value)).run next = _
  rw [Solidity.Source.Hoare.run_bind]
  cases nextRun : (Solidity.Source.evalE glob frame fuel right).run next with
  | mk result after =>
      cases result with
      | error halt => rfl
      | ok value => cases value with
        | val value => rfl

theorem source_or_error {env ctx} (left right : Solidity.Source.RExpr env ctx .bool)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (state next : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env)
    (halt : Solidity.Source.Halt)
    (actual : (Solidity.Source.evalE glob frame fuel left).run state = (.error halt,next)) :
    (Solidity.Source.evalE glob frame (fuel+1) (.binary .or left right)).run state =
      (.error halt,next) := by
  rw [Solidity.Source.evalE]
  simp only [reduceCtorEq,decide_true,decide_false,Bool.false_or,if_true]
  rw [Solidity.Source.Hoare.run_bind,actual]

theorem source_or_true {env ctx} (left right : Solidity.Source.RExpr env ctx .bool)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (state next : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env)
    (actual : (Solidity.Source.evalE glob frame fuel left).run state = (.ok (.val (.bool true)),next)) :
    (Solidity.Source.evalE glob frame (fuel+1) (.binary .or left right)).run state =
      (.ok (.val (.bool true)),next) := by
  rw [Solidity.Source.evalE]
  simp only [reduceCtorEq,decide_true,decide_false,Bool.false_or,if_true]
  rw [Solidity.Source.Hoare.run_bind,actual]
  rfl

theorem source_or_false {env ctx} (left right : Solidity.Source.RExpr env ctx .bool)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (state next : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env)
    (actual : (Solidity.Source.evalE glob frame fuel left).run state = (.ok (.val (.bool false)),next)) :
    (Solidity.Source.evalE glob frame (fuel+1) (.binary .or left right)).run state =
      (Solidity.Source.evalE glob frame fuel right).run next := by
  rw [Solidity.Source.evalE]
  simp only [reduceCtorEq,decide_true,decide_false,Bool.false_or,if_true]
  rw [Solidity.Source.Hoare.run_bind,actual]
  change (do
    let value ← Solidity.Source.getV (← Solidity.Source.evalE glob frame fuel right)
    pure (Solidity.Source.RVal.val value)).run next = _
  rw [Solidity.Source.Hoare.run_bind]
  cases nextRun : (Solidity.Source.evalE glob frame fuel right).run next with
  | mk result after =>
      cases result with
      | error halt => rfl
      | ok value => cases value with
        | val value => rfl

theorem source_cond_error {env ctx} (condition yes no : Solidity.Source.RExpr env ctx .bool)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (state next : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env)
    (halt : Solidity.Source.Halt)
    (actual : (Solidity.Source.evalE glob frame fuel condition).run state = (.error halt,next)) :
    (Solidity.Source.evalE glob frame (fuel+1) (.cond condition yes no)).run state =
      (.error halt,next) := by
  rw [Solidity.Source.evalE,Solidity.Source.Hoare.run_bind,actual]

theorem source_cond_true {env ctx} (condition yes no : Solidity.Source.RExpr env ctx .bool)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (state next : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env)
    (actual : (Solidity.Source.evalE glob frame fuel condition).run state = (.ok (.val (.bool true)),next)) :
    (Solidity.Source.evalE glob frame (fuel+1) (.cond condition yes no)).run state =
      (Solidity.Source.evalE glob frame fuel yes).run next := by
  rw [Solidity.Source.evalE,Solidity.Source.Hoare.run_bind,actual]
  rfl

theorem source_cond_false {env ctx} (condition yes no : Solidity.Source.RExpr env ctx .bool)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (state next : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env)
    (actual : (Solidity.Source.evalE glob frame fuel condition).run state = (.ok (.val (.bool false)),next)) :
    (Solidity.Source.evalE glob frame (fuel+1) (.cond condition yes no)).run state =
      (Solidity.Source.evalE glob frame fuel no).run next := by
  rw [Solidity.Source.evalE,Solidity.Source.Hoare.run_bind,actual]
  rfl

end Solidity.Yul.LocalBoolControl
