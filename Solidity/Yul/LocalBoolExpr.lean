import Solidity.Yul.LocalOperations
import Solidity.Yul.LocalState

/-! A certificate over the ACTUAL intrinsic Source.RExpr, not a second AST.
This first LOCAL consumer slice supports bool literals, actual indexed locals,
!, and assignment to an actual indexed bool local. Its horizon returns the
actual Source Halt.timeout and preserves the partial LOCAL state.
Clean Source.evalE agreement for this certificate is proved in
LocalBoolAgreement; general expression/control/session and dirty agreement are
separate obligations; no unsupported expression is admitted by this certificate. -/
namespace Solidity.Yul.LocalBoolExpr

inductive Supported (env : Solidity.Source.Env) (ctx : Solidity.Source.RCtx) :
    Solidity.Source.RExpr env ctx .bool → Type where
  | literal (value : Bool) : Supported env ctx (.bool value)
  | local (index : Solidity.Source.Idx ctx .bool) : Supported env ctx (.local index)
  | not {expr} : Supported env ctx expr → Supported env ctx (.unary .not expr)
  | assign {expr} (index : Solidity.Source.Idx ctx .bool) :
      Supported env ctx expr → Supported env ctx (.assign (.local index) expr)

def eval {env ctx expr} (proof : Supported env ctx expr) :
    Nat → LocalState env ctx →
      (Solidity.Source.R (LocalValue env .bool) × LocalState env ctx) := by
  apply Supported.casesOn (motive := fun _ _ =>
    Nat → LocalState env ctx →
      (Solidity.Source.R (LocalValue env .bool) × LocalState env ctx)) proof
  case literal =>
    intro value
    exact fun fuel state => match fuel with
      | 0 => (.error .timeout,state)
      | _+1 => (.ok (.clean (.bool value)),state)
  case «local» =>
    intro index
    exact fun fuel state => match fuel with
      | 0 => (.error .timeout,state)
      | _+1 => (.ok (state.1.get index),state)
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

theorem zero {env ctx expr} (proof : Supported env ctx expr) (state : LocalState env ctx) :
    eval proof 0 state = (.error .timeout,state) := by
  cases proof <;> rfl

theorem local_read {env ctx} (index : Solidity.Source.Idx ctx .bool)
    (fuel : Nat) (state : LocalState env ctx) :
    eval (.local index) (fuel+1) state = (.ok (state.1.get index),state) := rfl

theorem assign_local {env ctx} (target source : Solidity.Source.Idx ctx .bool)
    (fuel : Nat) (state : LocalState env ctx) :
    eval (.assign target (.local source)) (fuel+2) state =
      (.ok (state.1.get source),(state.1.set target (state.1.get source),state.2)) := rfl

theorem not_local {env ctx} (index : Solidity.Source.Idx ctx .bool)
    (fuel : Nat) (state : LocalState env ctx) :
    eval (.not (.local index)) (fuel+2) state =
      (LocalOperations.boolNot (state.1.get index),state) := rfl

theorem not_step {env ctx expr} (child : Supported env ctx expr)
    (fuel : Nat) (state : LocalState env ctx) :
    eval (.not child) (fuel+1) state =
      (let (result,next) := eval child fuel state
       (result.bind LocalOperations.boolNot,next)) := rfl

theorem assign_step {env ctx expr} (target : Solidity.Source.Idx ctx .bool)
    (child : Supported env ctx expr) (fuel : Nat) (state : LocalState env ctx) :
    eval (.assign target child) (fuel+1) state =
      (let (result,next) := eval child fuel state
       match result with
       | .error halt => (.error halt,next)
       | .ok value => (.ok value,(next.1.set target value,next.2))) := rfl

theorem world {env ctx expr} (proof : Supported env ctx expr)
    (fuel : Nat) (state : LocalState env ctx) : (eval proof fuel state).2.2 = state.2 := by
  induction proof generalizing fuel state with
  | literal value => cases fuel <;> rfl
  | «local» index => cases fuel <;> rfl
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
              change ((match eval child fuel state with
                | (result,next) => match result with
                  | .error halt => (.error halt,next)
                  | .ok value => (.ok value,(next.1.set index value,next.2))) :
                Solidity.Source.R (LocalValue env .bool) × LocalState env ctx).2.2 = state.2
              rw [actual]
              cases result <;> exact unchanged

/-- The original four-form certificate has unique evidence for its actual
Source expression. This does not concern other Yul certificate families. -/
theorem evidence_unique {env ctx expr} (one two : Supported env ctx expr) : one = two := by
  induction one with
  | literal value => cases two; rfl
  | «local» index => cases two; rfl
  | not child ih =>
      cases two with
      | not other => exact congrArg Supported.not (ih other)
  | assign index child ih =>
      cases two with
      | assign _ other => exact congrArg (Supported.assign index) (ih other)

end Solidity.Yul.LocalBoolExpr
