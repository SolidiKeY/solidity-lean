import Solidity.Yul.LocalBoolFailure
import Solidity.Yul.LocalDefaultItems

/-! Error classification for actual context-growing local statement runners. -/
namespace Solidity.Yul.LocalItemFailure

theorem statement : ∀ (env : Solidity.Source.Env) (types : Solidity.Source.RCtx) (expr : Solidity.Source.RExpr env types .bool)
 (proof : Solidity.Yul.LocalBoolControl.Supported env types expr) (fuel : Nat)
 (state : Solidity.Yul.LocalState env types) (halt : Solidity.Source.Halt),
 (Solidity.Yul.LocalExprStatement.discard (Solidity.Yul.LocalBoolControl.eval proof) fuel state).1 = .error halt →
 halt = .timeout := by

  intro env types expr proof fuel state halt failed
  cases fuel with
  | zero => cases failed; rfl
  | succ fuel =>
      rw [Solidity.Yul.LocalExprStatement.discard_step] at failed
      cases actual : Solidity.Yul.LocalBoolControl.eval proof fuel state with
      | mk result next =>
        rw [actual] at failed
        cases result with
        | error error =>
          have same := Solidity.Yul.LocalBoolFailure.control env types expr proof fuel state error (congrArg Prod.fst actual)
          cases failed
          exact same
        | ok value => cases failed

theorem initialization : ∀ (env : Solidity.Source.Env) (types : Solidity.Source.RCtx) (expr : Solidity.Source.RExpr env types .bool)
 (proof : Solidity.Yul.LocalBoolControl.Supported env types expr) (fuel : Nat)
 (state previous : Solidity.Yul.LocalState env types) (halt : Solidity.Source.Halt),
 Solidity.Yul.LocalBoolInitialization.run proof fuel state = .halted halt previous → halt = .timeout := by

  intro env types expr proof fuel state previous halt failed
  cases fuel with
  | zero => cases failed; rfl
  | succ fuel =>
      change Solidity.Yul.LocalBoolInitialization.finish (Solidity.Yul.LocalBoolControl.eval proof fuel state) = .halted halt previous at failed
      cases actual : Solidity.Yul.LocalBoolControl.eval proof fuel state with
      | mk result next =>
        rw [actual] at failed
        cases result with
        | error error =>
          have same := Solidity.Yul.LocalBoolFailure.control env types expr proof fuel state error (congrArg Prod.fst actual)
          cases failed
          exact same
        | ok value => cases failed

theorem booleanItems : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy) (modifier : Bool)
 (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalBoolItems.Supported env returns modifier control items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types) (reached : Solidity.Source.RCtx)
 (halt : Solidity.Source.Halt) (next : Solidity.Yul.LocalState env reached),
 Solidity.Yul.LocalBoolItems.run proof fuel state = .halted halt next → halt = .timeout := by

  intro env returns modifier control types out items proof
  induction proof with
  | nil =>
    intro fuel state reached halt next failed
    cases fuel <;> cases failed <;> rfl
  | expression one tail ih =>
    intro fuel state reached halt next failed
    cases fuel with
    | zero => cases failed; rfl
    | succ fuel =>
      rw [Solidity.Yul.LocalBoolItems.run] at failed
      dsimp only [] at failed
      cases actual : Solidity.Yul.LocalExprStatement.discard (Solidity.Yul.LocalBoolControl.eval one) fuel state with
      | mk result after =>
        rw [actual] at failed
        cases result with
        | error error =>
          have same := Solidity.Yul.LocalItemFailure.statement env _ _ one fuel state error (congrArg Prod.fst actual)
          cases failed
          exact same
        | ok _unit => exact ih fuel after reached halt next failed
  | declaration one tail ih =>
    intro fuel state reached halt next failed
    cases fuel with
    | zero => cases failed; rfl
    | succ fuel =>
      rw [Solidity.Yul.LocalBoolItems.run] at failed
      dsimp only [] at failed
      cases actual : Solidity.Yul.LocalBoolInitialization.run one fuel state with
      | normal extended =>
        rw [actual] at failed
        exact ih fuel extended reached halt next failed
      | halted error previous =>
        rw [actual] at failed
        have same := Solidity.Yul.LocalItemFailure.initialization env _ _ one fuel state previous error actual
        cases failed
        exact same

theorem defaultItems : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy) (modifier : Bool)
 (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalDefaultItems.Supported env returns modifier control items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types) (reached : Solidity.Source.RCtx)
 (halt : Solidity.Source.Halt) (next : Solidity.Yul.LocalState env reached),
 Solidity.Yul.LocalDefaultItems.run proof fuel state = .halted halt next → halt = .timeout := by

  intro env returns modifier control types out items proof
  induction proof with
  | body body => exact Solidity.Yul.LocalItemFailure.booleanItems env returns modifier control _ _ _ body
  | declaration value tail ih =>
    intro fuel state reached halt next failed
    cases fuel with
    | zero => cases failed; rfl
    | succ fuel =>
      cases fuel with
      | zero => cases failed; rfl
      | succ fuel =>
        cases fuel with
        | zero => cases failed; rfl
        | succ fuel =>
          exact ih (fuel+2) ((.clean value.value,state.1),state.2) reached halt next failed

end Solidity.Yul.LocalItemFailure
