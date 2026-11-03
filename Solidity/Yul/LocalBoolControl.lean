import Solidity.Yul.LocalBoolAgreement

/-! A concrete control-expression extension over ACTUAL Source.RExpr.
The existing four-form certificate/evaluator/refusal controls remain unchanged.
Base trees delegate to that actual producer; new syntax is certified here,
not renamed to claim general expression or compiler coverage. -/
namespace Solidity.Yul.LocalBoolControl

inductive Supported (env : Solidity.Source.Env) (ctx : Solidity.Source.RCtx) :
    Solidity.Source.RExpr env ctx .bool → Type where
  | base {expr} : LocalBoolExpr.Supported env ctx expr → Supported env ctx expr
  | and {left right} : Supported env ctx left → Supported env ctx right →
      Supported env ctx (.binary .and left right)
  | or {left right} : Supported env ctx left → Supported env ctx right →
      Supported env ctx (.binary .or left right)
  | cond {condition yes no} : Supported env ctx condition → Supported env ctx yes →
      Supported env ctx no → Supported env ctx (.cond condition yes no)
  | not {expr} : Supported env ctx expr → Supported env ctx (.unary .not expr)
  | assign {expr} (index : Solidity.Source.Idx ctx .bool) :
      Supported env ctx expr → Supported env ctx (.assign (.local index) expr)

/-- Branch on nonzero truth while retaining the original full local value. -/
def truth {env} (value : LocalValue env .bool) : Bool :=
  (LocalOperations.scalarWord value (LocalOperations.boolShape env)).val != 0

theorem truth_clean {env} (value : Bool) :
    truth (env := env) (.clean (.bool value)) = value := by cases value <;> rfl
theorem truth_raw {env} (value : Word) :
    truth (.scalar (LocalOperations.boolShape env) value) = (value.val != 0) := rfl

def eval {env ctx expr} (proof : Supported env ctx expr) :
    Nat → LocalState env ctx →
      (Solidity.Source.R (LocalValue env .bool) × LocalState env ctx) := by
  apply Supported.casesOn (motive := fun _ _ =>
    Nat → LocalState env ctx →
      (Solidity.Source.R (LocalValue env .bool) × LocalState env ctx)) proof
  case base =>
    intro expr child
    exact LocalBoolExpr.eval child
  case and =>
    intro left right one two
    exact fun fuel state => match fuel with
      | 0 => (.error .timeout,state)
      | fuel+1 =>
          let (result,next) := eval one fuel state
          match result with
          | .error halt => (.error halt,next)
          | .ok value => if truth value then eval two fuel next else (.ok value,next)
  case or =>
    intro left right one two
    exact fun fuel state => match fuel with
      | 0 => (.error .timeout,state)
      | fuel+1 =>
          let (result,next) := eval one fuel state
          match result with
          | .error halt => (.error halt,next)
          | .ok value => if truth value then (.ok value,next) else eval two fuel next
  case cond =>
    intro condition yes no test one two
    exact fun fuel state => match fuel with
      | 0 => (.error .timeout,state)
      | fuel+1 =>
          let (result,next) := eval test fuel state
          match result with
          | .error halt => (.error halt,next)
          | .ok value => if truth value then eval one fuel next else eval two fuel next
  case not =>
    intro expr child
    exact fun fuel state => match fuel with
      | 0 => (.error .timeout,state)
      | fuel+1 =>
          let (result,next) := eval child fuel state
          (result.bind LocalOperations.boolNot,next)
  case assign =>
    intro expr index child
    exact fun fuel state => match fuel with
      | 0 => (.error .timeout,state)
      | fuel+1 =>
          let (result,next) := eval child fuel state
          match result with
          | .error halt => (.error halt,next)
          | .ok value => (.ok value,(next.1.set index value,next.2))
termination_by structural proof

theorem base {env ctx expr} (proof : LocalBoolExpr.Supported env ctx expr)
    (fuel : Nat) (state : LocalState env ctx) :
    eval (.base proof) fuel state = LocalBoolExpr.eval proof fuel state := rfl

theorem zero {env ctx expr} (proof : Supported env ctx expr) (state : LocalState env ctx) :
    eval proof 0 state = (.error .timeout,state) := by
  cases proof with
  | base proof => exact LocalBoolExpr.zero proof state
  | and _ _ => rfl
  | or _ _ => rfl
  | cond _ _ _ => rfl
  | not _ => rfl
  | assign _ _ => rfl

theorem and_step {env ctx left right} (one : Supported env ctx left)
    (two : Supported env ctx right) (fuel : Nat) (state : LocalState env ctx) :
    eval (.and one two) (fuel+1) state =
      (let (result,next) := eval one fuel state
       match result with
       | .error halt => (.error halt,next)
       | .ok value => if truth value then eval two fuel next else (.ok value,next)) := rfl

theorem or_step {env ctx left right} (one : Supported env ctx left)
    (two : Supported env ctx right) (fuel : Nat) (state : LocalState env ctx) :
    eval (.or one two) (fuel+1) state =
      (let (result,next) := eval one fuel state
       match result with
       | .error halt => (.error halt,next)
       | .ok value => if truth value then (.ok value,next) else eval two fuel next) := rfl

theorem cond_step {env ctx condition yes no} (test : Supported env ctx condition)
    (one : Supported env ctx yes) (two : Supported env ctx no)
    (fuel : Nat) (state : LocalState env ctx) :
    eval (.cond test one two) (fuel+1) state =
      (let (result,next) := eval test fuel state
       match result with
       | .error halt => (.error halt,next)
       | .ok value => if truth value then eval one fuel next else eval two fuel next) := rfl

theorem not_step {env ctx expr} (proof : Supported env ctx expr)
    (fuel : Nat) (state : LocalState env ctx) :
    eval (.not proof) (fuel+1) state =
      (let (result,next) := eval proof fuel state
       (result.bind LocalOperations.boolNot,next)) := rfl

theorem assign_step {env ctx expr} (index : Solidity.Source.Idx ctx .bool)
    (proof : Supported env ctx expr) (fuel : Nat) (state : LocalState env ctx) :
    eval (.assign index proof) (fuel+1) state =
      (let (result,next) := eval proof fuel state
       match result with
       | .error halt => (.error halt,next)
       | .ok value => (.ok value,(next.1.set index value,next.2))) := rfl

theorem world {env ctx expr} (proof : Supported env ctx expr)
    (fuel : Nat) (state : LocalState env ctx) : (eval proof fuel state).2.2 = state.2 := by
  induction proof generalizing fuel state with
  | base proof => exact LocalBoolExpr.world proof fuel state
  | and one two ihOne ihTwo =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          have unchanged := ihOne fuel state
          cases actual : eval one fuel state with
          | mk result next =>
              rw [actual] at unchanged
              rw [and_step,actual]
              cases result with
              | error halt => exact unchanged
              | ok value =>
                  cases choice : truth value with
                  | false =>
                      simp only [choice,Bool.false_eq_true,if_false]
                      exact unchanged
                  | true =>
                      simp only [choice,if_true]
                      exact (ihTwo fuel next).trans unchanged
  | or one two ihOne ihTwo =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          have unchanged := ihOne fuel state
          cases actual : eval one fuel state with
          | mk result next =>
              rw [actual] at unchanged
              rw [or_step,actual]
              cases result with
              | error halt => exact unchanged
              | ok value =>
                  cases choice : truth value with
                  | false =>
                      simp only [choice,Bool.false_eq_true,if_false]
                      exact (ihTwo fuel next).trans unchanged
                  | true =>
                      simp only [choice,if_true]
                      exact unchanged
  | cond test one two ihTest ihOne ihTwo =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          have unchanged := ihTest fuel state
          cases actual : eval test fuel state with
          | mk result next =>
              rw [actual] at unchanged
              rw [cond_step,actual]
              cases result with
              | error halt => exact unchanged
              | ok value =>
                  cases choice : truth value with
                  | false =>
                      simp only [choice,Bool.false_eq_true,if_false]
                      exact (ihTwo fuel next).trans unchanged
                  | true =>
                      simp only [choice,if_true]
                      exact (ihOne fuel next).trans unchanged
  | not child ih =>
      cases fuel with
      | zero => rfl
      | succ fuel => exact ih fuel state
  | assign index child ih =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          have unchanged := ih fuel state
          cases actual : eval child fuel state with
          | mk result next =>
              rw [actual] at unchanged
              rw [assign_step,actual]
              cases result <;> exact unchanged

end Solidity.Yul.LocalBoolControl
