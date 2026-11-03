import Solidity.Yul.LocalU8Expr

/-! Actual Source evaluator steps for checked uint8. Real pair execution and
frame checkedness premises are explicit; final composition must discharge them. -/
namespace Solidity.Yul.LocalU8Expr

def cleanOutcome {env ctx}
    (result : Solidity.Source.R (Solidity.Source.RVal env.layout Ty) ×
      (Solidity.Source.Locals env.layout ctx × Solidity.Source.St env)) :
    Solidity.Source.R (LocalValue env Ty) × LocalState env ctx :=
  (result.1.bind (fun value => value.get.map LocalValue.clean),LocalState.ofClean result.2)

theorem source_zero {env ctx expr} (proof : Supported env ctx expr)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
    (state : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env) :
    eval proof glob.pipeline 0 (LocalState.ofClean state) =
      cleanOutcome ((Solidity.Source.evalE glob frame 0 expr).run state) := by
  rw [zero]
  rfl

theorem source_local {env ctx} (index : Solidity.Source.Idx ctx Ty) (fuel : Nat)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
    (state : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env) :
    eval (.local index) glob.pipeline (fuel+1) (LocalState.ofClean state) =
      cleanOutcome ((Solidity.Source.evalE glob frame (fuel+1) (.local index)).run state) := by
  change ((Except.ok ((LocalValues.ofClean state.1).get index) : Solidity.Source.R (LocalValue env Ty)),
    LocalState.ofClean state) = (Except.ok (.clean (state.1.get index)),LocalState.ofClean state)
  rw [LocalValues.get_ofClean]

theorem source_assign_error {env ctx} (target : Solidity.Source.Idx ctx Ty)
    (expr : Solidity.Source.RExpr env ctx Ty)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (state next : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env)
    (halt : Solidity.Source.Halt)
    (actual : (Solidity.Source.evalE glob frame fuel expr).run state = (.error halt,next)) :
    (Solidity.Source.evalE glob frame (fuel+1) (.assign (.local target) expr)).run state =
      (.error halt,next) := by
  rw [Solidity.Source.evalE,Solidity.Source.Hoare.run_bind,actual]

theorem source_assign_value {env ctx} (target : Solidity.Source.Idx ctx Ty)
    (expr : Solidity.Source.RExpr env ctx Ty)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (state next : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env)
    (value : Solidity.Source.Val env.layout Ty)
    (actual : (Solidity.Source.evalE glob frame (fuel+1) expr).run state = (.ok (.val value),next)) :
    (Solidity.Source.evalE glob frame (fuel+2) (.assign (.local target) expr)).run state =
      (.ok (.val value),(next.1.set target value,next.2)) := by
  rw [Solidity.Source.evalE,Solidity.Source.Hoare.run_bind,actual]
  rfl

theorem source_pair_legacy {env ctx} (left right : Solidity.Source.RExpr env ctx Ty)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (state : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env)
    (pipeline : glob.pipeline = .legacy) :
    (Solidity.Source.evalPair glob frame (fuel+1) left right).run state =
      (match (Solidity.Source.evalE glob frame fuel right).run state with
       | (.error halt,middle) => (.error halt,middle)
       | (.ok right,middle) =>
           match (Solidity.Source.evalE glob frame fuel left).run middle with
           | (.error halt,next) => (.error halt,next)
           | (.ok left,next) => (.ok (left,right),next)) := by
  rw [Solidity.Source.evalPair,pipeline,Solidity.Source.Hoare.run_bind]
  cases actual : (Solidity.Source.evalE glob frame fuel right).run state with
  | mk result middle =>
      cases result with
      | error halt => rfl
      | ok right =>
          dsimp only
          rw [Solidity.Source.Hoare.run_bind]
          cases nextRun : (Solidity.Source.evalE glob frame fuel left).run middle with
          | mk result next => cases result <;> rfl

theorem source_pair_viaIR {env ctx} (left right : Solidity.Source.RExpr env ctx Ty)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (state : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env)
    (pipeline : glob.pipeline = .viaIR) :
    (Solidity.Source.evalPair glob frame (fuel+1) left right).run state =
      (match (Solidity.Source.evalE glob frame fuel left).run state with
       | (.error halt,middle) => (.error halt,middle)
       | (.ok left,middle) =>
           match (Solidity.Source.evalE glob frame fuel right).run middle with
           | (.error halt,next) => (.error halt,next)
           | (.ok right,next) => (.ok (left,right),next)) := by
  rw [Solidity.Source.evalPair,pipeline,Solidity.Source.Hoare.run_bind]
  cases actual : (Solidity.Source.evalE glob frame fuel left).run state with
  | mk result middle =>
      cases result with
      | error halt => rfl
      | ok left =>
          dsimp only
          rw [Solidity.Source.Hoare.run_bind]
          cases nextRun : (Solidity.Source.evalE glob frame fuel right).run middle with
          | mk result next => cases result <;> rfl

theorem source_add_error {env ctx} (left right : Solidity.Source.RExpr env ctx Ty)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (state next : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env)
    (halt : Solidity.Source.Halt)
    (actual : (Solidity.Source.evalPair glob frame fuel left right).run state = (.error halt,next)) :
    (Solidity.Source.evalE glob frame (fuel+1) (.binary .add left right)).run state =
      (.error halt,next) := by
  rw [Solidity.Source.evalE]
  simp only [reduceCtorEq,decide_false,Bool.false_or,if_false]
  rw [Solidity.Source.Hoare.run_bind,actual]

theorem source_add_values {env ctx} (left right : Solidity.Source.RExpr env ctx Ty)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (state next : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env)
    (leftValue rightValue : Solidity.Source.Val env.layout Ty) (checked : frame.checked = true)
    (actual : (Solidity.Source.evalPair glob frame fuel left right).run state =
      (.ok (.val leftValue,.val rightValue),next)) :
    (Solidity.Source.evalE glob frame (fuel+1) (.binary .add left right)).run state =
      ((Solidity.Source.binVal true .add leftValue rightValue).map Solidity.Source.RVal.val,next) := by
  rw [Solidity.Source.evalE]
  simp only [reduceCtorEq,decide_false,Bool.false_or,if_false]
  rw [Solidity.Source.Hoare.run_bind,actual]
  rw [checked]
  dsimp only
  change (do
    let value ← Solidity.Source.EM.lift (Solidity.Source.binVal true .add leftValue rightValue)
    pure (Solidity.Source.RVal.val value)).run next = _
  cases result : Solidity.Source.binVal true .add leftValue rightValue <;>
    simp only [Solidity.Source.EM.lift] <;> rfl

end Solidity.Yul.LocalU8Expr
