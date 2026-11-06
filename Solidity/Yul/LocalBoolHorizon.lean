import Solidity.Yul.LocalBoolControl

/-! Full-run terminal fuel stability for raw-local Boolean execution.
Timeout prefixes remain outside these laws. No cleanup or admission change. -/
namespace Solidity.Yul.LocalBoolHorizon

theorem baseSuccessor : ∀ (env : Solidity.Source.Env) (ctx : Solidity.Source.RCtx)
 (expr : Solidity.Source.RExpr env ctx .bool)
 (proof : Solidity.Yul.LocalBoolExpr.Supported env ctx expr)
 (fuel : Nat) (state : Solidity.Yul.LocalState env ctx),
 (Solidity.Yul.LocalBoolExpr.eval proof fuel state).1 ≠ .error .timeout →
 Solidity.Yul.LocalBoolExpr.eval proof (fuel+1) state =
 Solidity.Yul.LocalBoolExpr.eval proof fuel state := by
  intro env ctx expr proof
  induction proof with
  | literal value =>
    intro fuel state terminal
    cases fuel with
    | zero => exact False.elim (terminal rfl)
    | succ fuel => rfl
  | «local» index =>
    intro fuel state terminal
    cases fuel with
    | zero => exact False.elim (terminal rfl)
    | succ fuel => rfl
  | not child ih =>
    intro fuel state terminal
    cases fuel with
    | zero => exact False.elim (terminal rfl)
    | succ fuel =>
      cases actual : Solidity.Yul.LocalBoolExpr.eval child fuel state with
      | mk result next =>
        cases result with
        | error halt =>
          have ready : (Solidity.Yul.LocalBoolExpr.eval child fuel state).1 ≠ .error .timeout := by
            simpa only [Solidity.Yul.LocalBoolExpr.not_step,actual,Except.bind] using terminal
          simp only [Solidity.Yul.LocalBoolExpr.not_step,ih fuel state ready,actual]
        | ok value =>
          have ready : (Solidity.Yul.LocalBoolExpr.eval child fuel state).1 ≠ .error .timeout := by
            rw [actual]
            intro impossible
            cases impossible
          simp only [Solidity.Yul.LocalBoolExpr.not_step,ih fuel state ready,actual]
  | assign index child ih =>
    intro fuel state terminal
    cases fuel with
    | zero => exact False.elim (terminal rfl)
    | succ fuel =>
      cases actual : Solidity.Yul.LocalBoolExpr.eval child fuel state with
      | mk result next =>
        cases result with
        | error halt =>
          have ready : (Solidity.Yul.LocalBoolExpr.eval child fuel state).1 ≠ .error .timeout := by
            simpa only [Solidity.Yul.LocalBoolExpr.assign_step,actual,Except.bind] using terminal
          simp only [Solidity.Yul.LocalBoolExpr.assign_step,ih fuel state ready,actual]
        | ok value =>
          have ready : (Solidity.Yul.LocalBoolExpr.eval child fuel state).1 ≠ .error .timeout := by
            rw [actual]
            intro impossible
            cases impossible
          simp only [Solidity.Yul.LocalBoolExpr.assign_step,ih fuel state ready,actual]

theorem successor : ∀ (env : Solidity.Source.Env) (ctx : Solidity.Source.RCtx)
 (expr : Solidity.Source.RExpr env ctx .bool)
 (proof : Solidity.Yul.LocalBoolControl.Supported env ctx expr)
 (fuel : Nat) (state : Solidity.Yul.LocalState env ctx),
 (Solidity.Yul.LocalBoolControl.eval proof fuel state).1 ≠ .error .timeout →
 Solidity.Yul.LocalBoolControl.eval proof (fuel+1) state =
 Solidity.Yul.LocalBoolControl.eval proof fuel state := by
  intro env ctx expr proof
  induction proof with
  | base child =>
    intro fuel state terminal
    exact Solidity.Yul.LocalBoolHorizon.baseSuccessor env ctx _ child fuel state terminal
  | not child ih =>
    intro fuel state terminal
    cases fuel with
    | zero => exact False.elim (terminal rfl)
    | succ fuel =>
      cases actual : Solidity.Yul.LocalBoolControl.eval child fuel state with
      | mk result next =>
        cases result with
        | error halt =>
          have ready : (Solidity.Yul.LocalBoolControl.eval child fuel state).1 ≠ .error .timeout := by
            simpa only [Solidity.Yul.LocalBoolControl.not_step,actual,Except.bind] using terminal
          simp only [Solidity.Yul.LocalBoolControl.not_step,ih fuel state ready,actual]
        | ok value =>
          have ready : (Solidity.Yul.LocalBoolControl.eval child fuel state).1 ≠ .error .timeout := by
            rw [actual]
            intro impossible
            cases impossible
          simp only [Solidity.Yul.LocalBoolControl.not_step,ih fuel state ready,actual]
  | assign index child ih =>
    intro fuel state terminal
    cases fuel with
    | zero => exact False.elim (terminal rfl)
    | succ fuel =>
      cases actual : Solidity.Yul.LocalBoolControl.eval child fuel state with
      | mk result next =>
        cases result with
        | error halt =>
          have ready : (Solidity.Yul.LocalBoolControl.eval child fuel state).1 ≠ .error .timeout := by
            simpa only [Solidity.Yul.LocalBoolControl.assign_step,actual,Except.bind] using terminal
          simp only [Solidity.Yul.LocalBoolControl.assign_step,ih fuel state ready,actual]
        | ok value =>
          have ready : (Solidity.Yul.LocalBoolControl.eval child fuel state).1 ≠ .error .timeout := by
            rw [actual]
            intro impossible
            cases impossible
          simp only [Solidity.Yul.LocalBoolControl.assign_step,ih fuel state ready,actual]
  | and one two ihOne ihTwo =>
    intro fuel state terminal
    cases fuel with
    | zero => exact False.elim (terminal rfl)
    | succ fuel =>
      cases actual : Solidity.Yul.LocalBoolControl.eval one fuel state with
      | mk result next =>
        cases result with
        | error halt =>
          have ready : (Solidity.Yul.LocalBoolControl.eval one fuel state).1 ≠ .error .timeout := by
            simpa only [Solidity.Yul.LocalBoolControl.and_step,actual] using terminal
          simp only [Solidity.Yul.LocalBoolControl.and_step,ihOne fuel state ready,actual]
        | ok value =>
          have ready : (Solidity.Yul.LocalBoolControl.eval one fuel state).1 ≠ .error .timeout := by
            rw [actual]
            intro impossible
            cases impossible
          cases choice : Solidity.Yul.LocalBoolControl.truth value with
          | false =>
            simp only [Solidity.Yul.LocalBoolControl.and_step,ihOne fuel state ready,actual,choice,Bool.false_eq_true,if_false]
          | true =>
            have nextReady : (Solidity.Yul.LocalBoolControl.eval two fuel next).1 ≠ .error .timeout := by
              simpa only [Solidity.Yul.LocalBoolControl.and_step,actual,choice] using terminal
            simp only [Solidity.Yul.LocalBoolControl.and_step,ihOne fuel state ready,actual,choice,ihTwo fuel next nextReady]
  | or one two ihOne ihTwo =>
    intro fuel state terminal
    cases fuel with
    | zero => exact False.elim (terminal rfl)
    | succ fuel =>
      cases actual : Solidity.Yul.LocalBoolControl.eval one fuel state with
      | mk result next =>
        cases result with
        | error halt =>
          have ready : (Solidity.Yul.LocalBoolControl.eval one fuel state).1 ≠ .error .timeout := by
            simpa only [Solidity.Yul.LocalBoolControl.or_step,actual] using terminal
          simp only [Solidity.Yul.LocalBoolControl.or_step,ihOne fuel state ready,actual]
        | ok value =>
          have ready : (Solidity.Yul.LocalBoolControl.eval one fuel state).1 ≠ .error .timeout := by
            rw [actual]
            intro impossible
            cases impossible
          cases choice : Solidity.Yul.LocalBoolControl.truth value with
          | false =>
            have nextReady : (Solidity.Yul.LocalBoolControl.eval two fuel next).1 ≠ .error .timeout := by
              simpa only [Solidity.Yul.LocalBoolControl.or_step,actual,choice] using terminal
            simp only [Solidity.Yul.LocalBoolControl.or_step,ihOne fuel state ready,actual,choice,ihTwo fuel next nextReady]
          | true =>
            simp only [Solidity.Yul.LocalBoolControl.or_step,ihOne fuel state ready,actual,choice,if_true]
  | cond test one two ihTest ihOne ihTwo =>
    intro fuel state terminal
    cases fuel with
    | zero => exact False.elim (terminal rfl)
    | succ fuel =>
      cases actual : Solidity.Yul.LocalBoolControl.eval test fuel state with
      | mk result next =>
        cases result with
        | error halt =>
          have ready : (Solidity.Yul.LocalBoolControl.eval test fuel state).1 ≠ .error .timeout := by
            simpa only [Solidity.Yul.LocalBoolControl.cond_step,actual] using terminal
          simp only [Solidity.Yul.LocalBoolControl.cond_step,ihTest fuel state ready,actual]
        | ok value =>
          have ready : (Solidity.Yul.LocalBoolControl.eval test fuel state).1 ≠ .error .timeout := by
            rw [actual]
            intro impossible
            cases impossible
          cases choice : Solidity.Yul.LocalBoolControl.truth value with
          | false =>
            have nextReady : (Solidity.Yul.LocalBoolControl.eval two fuel next).1 ≠ .error .timeout := by
              simpa only [Solidity.Yul.LocalBoolControl.cond_step,actual,choice] using terminal
            simp only [Solidity.Yul.LocalBoolControl.cond_step,ihTest fuel state ready,actual,choice,ihTwo fuel next nextReady,Bool.false_eq_true,if_false]
          | true =>
            have nextReady : (Solidity.Yul.LocalBoolControl.eval one fuel next).1 ≠ .error .timeout := by
              simpa only [Solidity.Yul.LocalBoolControl.cond_step,actual,choice] using terminal
            simp only [Solidity.Yul.LocalBoolControl.cond_step,ihTest fuel state ready,actual,choice,ihOne fuel next nextReady,if_true]

theorem extension : ∀ (env : Solidity.Source.Env) (ctx : Solidity.Source.RCtx)
 (expr : Solidity.Source.RExpr env ctx .bool)
 (proof : Solidity.Yul.LocalBoolControl.Supported env ctx expr)
 (fuel extra : Nat) (state : Solidity.Yul.LocalState env ctx),
 (Solidity.Yul.LocalBoolControl.eval proof fuel state).1 ≠ .error .timeout →
 Solidity.Yul.LocalBoolControl.eval proof (fuel+extra) state =
 Solidity.Yul.LocalBoolControl.eval proof fuel state := by
  intro env ctx expr proof fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have stillTerminal : (Solidity.Yul.LocalBoolControl.eval proof (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (Solidity.Yul.LocalBoolHorizon.successor env ctx expr proof (fuel+extra) state stillTerminal).trans ih

end Solidity.Yul.LocalBoolHorizon
