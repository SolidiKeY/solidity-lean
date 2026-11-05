import Solidity.Yul.LocalBoolControl

/-! Failure classification for actual certified local Boolean expressions.
No runtime definition or Source type is changed. -/
namespace Solidity.Yul.LocalBoolFailure

theorem expression : ∀ (env : Solidity.Source.Env) (ctx : Solidity.Source.RCtx)
 (expr : Solidity.Source.RExpr env ctx .bool)
 (proof : Solidity.Yul.LocalBoolExpr.Supported env ctx expr) (fuel : Nat)
 (state : Solidity.Yul.LocalState env ctx) (halt : Solidity.Source.Halt),
 (Solidity.Yul.LocalBoolExpr.eval proof fuel state).1 = .error halt → halt = .timeout := by

  intro env ctx expr proof
  induction proof with
  | literal value =>
    intro fuel state halt failed
    cases fuel <;> cases failed <;> rfl
  | «local» index =>
    intro fuel state halt failed
    cases fuel <;> cases failed <;> rfl
  | not child ih =>
    intro fuel state halt failed
    cases fuel with
    | zero => cases failed; rfl
    | succ fuel =>
      rw [Solidity.Yul.LocalBoolExpr.not_step] at failed
      cases actual : Solidity.Yul.LocalBoolExpr.eval child fuel state with
      | mk result next =>
        rw [actual] at failed
        cases result with
        | error error =>
          have same := ih fuel state error (congrArg Prod.fst actual)
          change (Except.error error : Solidity.Source.R (Solidity.Yul.LocalValue env .bool)) = .error halt at failed
          cases failed
          exact same
        | ok value =>
          change Solidity.Yul.LocalOperations.boolNot value = .error halt at failed
          simp only [Solidity.Yul.LocalOperations.boolNot,Solidity.Yul.LocalOperations.boolInput,
            Solidity.Source.unaryVal,Except.map] at failed
          cases failed
  | assign index child ih =>
    intro fuel state halt failed
    cases fuel with
    | zero => cases failed; rfl
    | succ fuel =>
      rw [Solidity.Yul.LocalBoolExpr.assign_step] at failed
      cases actual : Solidity.Yul.LocalBoolExpr.eval child fuel state with
      | mk result next =>
        rw [actual] at failed
        cases result with
        | error error =>
          have same := ih fuel state error (congrArg Prod.fst actual)
          change (Except.error error : Solidity.Source.R (Solidity.Yul.LocalValue env .bool)) = .error halt at failed
          cases failed
          exact same
        | ok value => cases failed

theorem control : ∀ (env : Solidity.Source.Env) (ctx : Solidity.Source.RCtx)
 (expr : Solidity.Source.RExpr env ctx .bool)
 (proof : Solidity.Yul.LocalBoolControl.Supported env ctx expr) (fuel : Nat)
 (state : Solidity.Yul.LocalState env ctx) (halt : Solidity.Source.Halt),
 (Solidity.Yul.LocalBoolControl.eval proof fuel state).1 = .error halt → halt = .timeout := by

  intro env ctx expr proof
  induction proof with
  | base child => exact Solidity.Yul.LocalBoolFailure.expression env ctx _ child
  | and one two ihOne ihTwo =>
    intro fuel state halt failed
    cases fuel with
    | zero => cases failed; rfl
    | succ fuel =>
      rw [Solidity.Yul.LocalBoolControl.and_step] at failed
      cases actual : Solidity.Yul.LocalBoolControl.eval one fuel state with
      | mk result next =>
        rw [actual] at failed
        cases result with
        | error error =>
          have same := ihOne fuel state error (congrArg Prod.fst actual)
          change (Except.error error : Solidity.Source.R (Solidity.Yul.LocalValue env .bool)) = .error halt at failed
          cases failed
          exact same
        | ok value =>
          dsimp only [] at failed
          split at failed
          · exact ihTwo fuel next halt failed
          · cases failed
  | or one two ihOne ihTwo =>
    intro fuel state halt failed
    cases fuel with
    | zero => cases failed; rfl
    | succ fuel =>
      rw [Solidity.Yul.LocalBoolControl.or_step] at failed
      cases actual : Solidity.Yul.LocalBoolControl.eval one fuel state with
      | mk result next =>
        rw [actual] at failed
        cases result with
        | error error =>
          have same := ihOne fuel state error (congrArg Prod.fst actual)
          change (Except.error error : Solidity.Source.R (Solidity.Yul.LocalValue env .bool)) = .error halt at failed
          cases failed
          exact same
        | ok value =>
          dsimp only [] at failed
          split at failed
          · cases failed
          · exact ihTwo fuel next halt failed
  | cond test one two ihTest ihOne ihTwo =>
    intro fuel state halt failed
    cases fuel with
    | zero => cases failed; rfl
    | succ fuel =>
      rw [Solidity.Yul.LocalBoolControl.cond_step] at failed
      cases actual : Solidity.Yul.LocalBoolControl.eval test fuel state with
      | mk result next =>
        rw [actual] at failed
        cases result with
        | error error =>
          have same := ihTest fuel state error (congrArg Prod.fst actual)
          change (Except.error error : Solidity.Source.R (Solidity.Yul.LocalValue env .bool)) = .error halt at failed
          cases failed
          exact same
        | ok value =>
          dsimp only [] at failed
          split at failed
          · exact ihOne fuel next halt failed
          · exact ihTwo fuel next halt failed
  | not child ih =>
    intro fuel state halt failed
    cases fuel with
    | zero => cases failed; rfl
    | succ fuel =>
      rw [Solidity.Yul.LocalBoolControl.not_step] at failed
      cases actual : Solidity.Yul.LocalBoolControl.eval child fuel state with
      | mk result next =>
        rw [actual] at failed
        cases result with
        | error error =>
          have same := ih fuel state error (congrArg Prod.fst actual)
          change (Except.error error : Solidity.Source.R (Solidity.Yul.LocalValue env .bool)) = .error halt at failed
          cases failed
          exact same
        | ok value =>
          change Solidity.Yul.LocalOperations.boolNot value = .error halt at failed
          simp only [Solidity.Yul.LocalOperations.boolNot,Solidity.Yul.LocalOperations.boolInput,
            Solidity.Source.unaryVal,Except.map] at failed
          cases failed
  | assign index child ih =>
    intro fuel state halt failed
    cases fuel with
    | zero => cases failed; rfl
    | succ fuel =>
      rw [Solidity.Yul.LocalBoolControl.assign_step] at failed
      cases actual : Solidity.Yul.LocalBoolControl.eval child fuel state with
      | mk result next =>
        rw [actual] at failed
        cases result with
        | error error =>
          have same := ih fuel state error (congrArg Prod.fst actual)
          change (Except.error error : Solidity.Source.R (Solidity.Yul.LocalValue env .bool)) = .error halt at failed
          cases failed
          exact same
        | ok value => cases failed

end Solidity.Yul.LocalBoolFailure
