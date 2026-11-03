import Solidity.Yul.LocalBoolExpr
import Solidity.Source.Eval

/-! Direct clean-state agreements with the ACTUAL Source.evalE. The final source_agrees theorem composes every certified tree/horizon.
This does not claim all expressions, dirty compiler or session agreement. -/
namespace Solidity.Yul.LocalBoolExpr

def cleanOutcome {env ctx}
    (result : Solidity.Source.R (Solidity.Source.RVal env.layout .bool) ×
      (Solidity.Source.Locals env.layout ctx × Solidity.Source.St env)) :
    Solidity.Source.R (LocalValue env .bool) × LocalState env ctx :=
  (result.1.bind (fun value => value.get.map LocalValue.clean),LocalState.ofClean result.2)

theorem source_zero {env ctx expr} (proof : Supported env ctx expr)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
    (state : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env) :
    eval proof 0 (LocalState.ofClean state) =
      cleanOutcome ((Solidity.Source.evalE glob frame 0 expr).run state) := by
  rw [zero]
  rfl

theorem source_literal {env ctx} (value : Bool) (fuel : Nat)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
    (state : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env) :
    eval (.literal value) (fuel+1) (LocalState.ofClean state) =
      cleanOutcome ((Solidity.Source.evalE glob frame (fuel+1) (.bool value)).run state) := rfl

theorem source_local {env ctx} (index : Solidity.Source.Idx ctx .bool) (fuel : Nat)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
    (state : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env) :
    eval (.local index) (fuel+1) (LocalState.ofClean state) =
      cleanOutcome ((Solidity.Source.evalE glob frame (fuel+1) (.local index)).run state) := by
  change ((Except.ok ((LocalValues.ofClean state.1).get index) : Solidity.Source.R (LocalValue env .bool)),LocalState.ofClean state) =
    (Except.ok (.clean (state.1.get index)),LocalState.ofClean state)
  rw [LocalValues.get_ofClean]

theorem source_local_run {env ctx} (index : Solidity.Source.Idx ctx .bool) (fuel : Nat)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
    (state : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env) :
    (Solidity.Source.evalE glob frame (fuel+1) (.local index)).run state =
      (.ok (.val (state.1.get index)),state) := rfl

theorem source_not_local_run {env ctx} (index : Solidity.Source.Idx ctx .bool) (fuel : Nat)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
    (state : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env)
    (value : Bool) (actual : state.1.get index = .bool value) :
    (Solidity.Source.evalE glob frame (fuel+2) (.unary .not (.local index))).run state =
      (.ok (.val (.bool (!value))),state) := by
  rw [Solidity.Source.evalE,Solidity.Source.Hoare.run_bind,source_local_run]
  rw [actual]
  rfl

theorem source_not_local {env ctx} (index : Solidity.Source.Idx ctx .bool) (fuel : Nat)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
    (state : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env) :
    eval (.not (.local index)) (fuel+2) (LocalState.ofClean state) =
      cleanOutcome ((Solidity.Source.evalE glob frame (fuel+2) (.unary .not (.local index))).run state) := by
  rw [not_local]
  simp only [LocalState.ofClean,LocalValues.get_ofClean]
  cases actual : state.1.get index with
  | bool value =>
      rw [LocalOperations.boolNot_clean]
      rw [source_not_local_run index fuel glob frame state value actual]
      rfl
  | memRef impossible _ => cases impossible
  | storRef impossible _ => cases impossible
  | cdRef impossible _ => cases impossible

theorem ofClean_set {env : Solidity.Source.Env} {ctx ty} (locals : Solidity.Source.Locals env.layout ctx)
    (index : Solidity.Source.Idx ctx ty) (value : Solidity.Source.Val env.layout ty) :
    LocalValues.ofClean (locals.set index value) =
      (LocalValues.ofClean locals).set index (.clean value) := by
  induction index with
  | here => cases locals; rfl
  | there index ih =>
      cases locals with
      | cons old rest =>
          exact congrArg (fun tail => (LocalValue.clean old,tail)) (ih rest value)

theorem source_assign_local_run {env ctx} (target source : Solidity.Source.Idx ctx .bool)
    (fuel : Nat) (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
    (state : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env) :
    (Solidity.Source.evalE glob frame (fuel+2) (.assign (.local target) (.local source))).run state =
      (.ok (.val (state.1.get source)),(state.1.set target (state.1.get source),state.2)) := by
  rw [Solidity.Source.evalE,Solidity.Source.Hoare.run_bind,source_local_run]
  rfl

theorem source_assign_local {env ctx} (target source : Solidity.Source.Idx ctx .bool)
    (fuel : Nat) (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
    (state : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env) :
    eval (.assign target (.local source)) (fuel+2) (LocalState.ofClean state) =
      cleanOutcome ((Solidity.Source.evalE glob frame (fuel+2)
        (.assign (.local target) (.local source))).run state) := by
  rw [assign_local,source_assign_local_run]
  simp only [cleanOutcome,LocalState.ofClean,LocalValues.get_ofClean,ofClean_set]
  rfl

theorem source_not_error {env ctx} (expr : Solidity.Source.RExpr env ctx .bool)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (state next : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env)
    (halt : Solidity.Source.Halt)
    (actual : (Solidity.Source.evalE glob frame fuel expr).run state = (.error halt,next)) :
    (Solidity.Source.evalE glob frame (fuel+1) (.unary .not expr)).run state =
      (.error halt,next) := by
  rw [Solidity.Source.evalE,Solidity.Source.Hoare.run_bind,actual]

theorem source_not_bool {env ctx} (expr : Solidity.Source.RExpr env ctx .bool)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (state next : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env)
    (value : Bool)
    (actual : (Solidity.Source.evalE glob frame fuel expr).run state = (.ok (.val (.bool value)),next)) :
    (Solidity.Source.evalE glob frame (fuel+1) (.unary .not expr)).run state =
      (.ok (.val (.bool (!value))),next) := by
  rw [Solidity.Source.evalE,Solidity.Source.Hoare.run_bind,actual]
  rfl

theorem source_assign_error {env ctx} (target : Solidity.Source.Idx ctx .bool)
    (expr : Solidity.Source.RExpr env ctx .bool)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (state next : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env)
    (halt : Solidity.Source.Halt)
    (actual : (Solidity.Source.evalE glob frame fuel expr).run state = (.error halt,next)) :
    (Solidity.Source.evalE glob frame (fuel+1) (.assign (.local target) expr)).run state =
      (.error halt,next) := by
  rw [Solidity.Source.evalE,Solidity.Source.Hoare.run_bind,actual]

theorem source_assign_value {env ctx} (target : Solidity.Source.Idx ctx .bool)
    (expr : Solidity.Source.RExpr env ctx .bool)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (state next : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env)
    (value : Solidity.Source.Val env.layout .bool)
    (actual : (Solidity.Source.evalE glob frame (fuel+1) expr).run state = (.ok (.val value),next)) :
    (Solidity.Source.evalE glob frame (fuel+2) (.assign (.local target) expr)).run state =
      (.ok (.val value),(next.1.set target value,next.2)) := by
  rw [Solidity.Source.evalE,Solidity.Source.Hoare.run_bind,actual]
  rfl

/-- Concrete clean-state composition for EVERY tree in this actual Source
certificate, at EVERY horizon, retaining actual Source halt and partial state.
No child-execution theorem, completion, cleanup or state relation is assumed. -/
theorem source_agrees {env ctx expr} (proof : Supported env ctx expr)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (state : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env) :
    eval proof fuel (LocalState.ofClean state) =
      cleanOutcome ((Solidity.Source.evalE glob frame fuel expr).run state) := by
  induction proof generalizing fuel state with
  | literal value =>
      cases fuel with
      | zero => exact source_zero _ glob frame state
      | succ fuel => exact source_literal value fuel glob frame state
  | «local» index =>
      cases fuel with
      | zero => exact source_zero _ glob frame state
      | succ fuel => exact source_local index fuel glob frame state
  | @not inner child ih =>
      cases fuel with
      | zero => exact source_zero _ glob frame state
      | succ fuel =>
          have induct := ih fuel state
          cases actual : (Solidity.Source.evalE glob frame fuel inner).run state with
          | mk result next =>
              rw [actual] at induct
              cases result with
              | error halt =>
                  change eval child fuel (LocalState.ofClean state) =
                    (.error halt,LocalState.ofClean next) at induct
                  rw [not_step,induct,source_not_error inner glob frame fuel state next halt actual]
                  rfl
              | ok value =>
                  cases value with
                  | val value =>
                      cases value with
                      | bool value =>
                          change eval child fuel (LocalState.ofClean state) =
                            (.ok (.clean (.bool value)),LocalState.ofClean next) at induct
                          rw [not_step,induct,source_not_bool inner glob frame fuel state next value actual]
                          simp only [Except.bind]
                          rw [LocalOperations.boolNot_clean]
                          rfl
                      | memRef impossible _ => cases impossible
                      | storRef impossible _ => cases impossible
                      | cdRef impossible _ => cases impossible
  | @assign inner target child ih =>
      cases fuel with
      | zero => exact source_zero _ glob frame state
      | succ fuel =>
          have induct := ih fuel state
          cases actual : (Solidity.Source.evalE glob frame fuel inner).run state with
          | mk result next =>
              rw [actual] at induct
              cases result with
              | error halt =>
                  change eval child fuel (LocalState.ofClean state) =
                    (.error halt,LocalState.ofClean next) at induct
                  rw [assign_step,induct,source_assign_error target inner glob frame fuel state next halt actual]
                  rfl
              | ok value =>
                  cases value with
                  | val value =>
                      change eval child fuel (LocalState.ofClean state) =
                        (.ok (.clean value),LocalState.ofClean next) at induct
                      cases fuel with
                      | zero => cases actual
                      | succ fuel =>
                          rw [assign_step,induct,
                            source_assign_value target inner glob frame fuel state next value actual]
                          simp only [cleanOutcome,LocalState.ofClean,ofClean_set]
                          rfl

end Solidity.Yul.LocalBoolExpr
