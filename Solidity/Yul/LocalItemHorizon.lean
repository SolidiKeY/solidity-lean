import Solidity.Yul.LocalBoolItems
import Solidity.Yul.LocalBoolHorizon

/-! Exact completed-run fuel stability for context-growing Boolean item lists.
Uses existing intrinsic syntax and raw frames; timeout prefixes may differ. -/
namespace Solidity.Yul.LocalItemHorizon

theorem successor : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalBoolItems.Supported env returns modifier control items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types) (final : Solidity.Yul.LocalState env out),
 Solidity.Yul.LocalBoolItems.run proof fuel state = .normal final →
 Solidity.Yul.LocalBoolItems.run proof (fuel+1) state = .normal final := by
  intro env returns modifier control types out items proof
  induction proof with
  | nil =>
    intro fuel state final completed
    cases fuel with
    | zero => cases completed
    | succ fuel =>
      cases completed
      rfl
  | expression one tail ih =>
    intro fuel state final completed
    cases fuel with
    | zero => cases completed
    | succ fuel =>
      cases fuel with
      | zero => cases completed
      | succ fuel =>
        cases actual : Solidity.Yul.LocalBoolControl.eval one fuel state with
        | mk result next =>
          cases result with
          | error halt =>
            rw [Solidity.Yul.LocalBoolItems.run] at completed
            dsimp only [Solidity.Yul.LocalExprStatement.discard] at completed
            rw [actual] at completed
            cases completed
          | ok value =>
            have ready : (Solidity.Yul.LocalBoolControl.eval one fuel state).1 ≠ .error .timeout := by
              rw [actual]
              intro impossible
              cases impossible
            have same := Solidity.Yul.LocalBoolHorizon.successor env _ _ one fuel state ready
            have tailDone : Solidity.Yul.LocalBoolItems.run tail (fuel+1) next = .normal final := by
              rw [Solidity.Yul.LocalBoolItems.run] at completed
              dsimp only [Solidity.Yul.LocalExprStatement.discard] at completed
              rw [actual] at completed
              exact completed
            have tailNext := ih (fuel+1) next final tailDone
            rw [Solidity.Yul.LocalBoolItems.run]
            dsimp only [Solidity.Yul.LocalExprStatement.discard]
            rw [same,actual]
            exact tailNext
  | declaration one tail ih =>
    intro fuel state final completed
    cases fuel with
    | zero => cases completed
    | succ fuel =>
      cases fuel with
      | zero => cases completed
      | succ fuel =>
        cases actual : Solidity.Yul.LocalBoolControl.eval one fuel state with
        | mk result next =>
          cases result with
          | error halt =>
            rw [Solidity.Yul.LocalBoolItems.run] at completed
            dsimp only [Solidity.Yul.LocalBoolInitialization.run,Solidity.Yul.LocalBoolInitialization.finish] at completed
            rw [actual] at completed
            cases completed
          | ok value =>
            have ready : (Solidity.Yul.LocalBoolControl.eval one fuel state).1 ≠ .error .timeout := by
              rw [actual]
              intro impossible
              cases impossible
            have same := Solidity.Yul.LocalBoolHorizon.successor env _ _ one fuel state ready
            have tailDone : Solidity.Yul.LocalBoolItems.run tail (fuel+1) ((value,next.1),next.2) = .normal final := by
              rw [Solidity.Yul.LocalBoolItems.run] at completed
              dsimp only [Solidity.Yul.LocalBoolInitialization.run,Solidity.Yul.LocalBoolInitialization.finish] at completed
              rw [actual] at completed
              exact completed
            have tailNext := ih (fuel+1) ((value,next.1),next.2) final tailDone
            rw [Solidity.Yul.LocalBoolItems.run]
            dsimp only [Solidity.Yul.LocalBoolInitialization.run,Solidity.Yul.LocalBoolInitialization.finish]
            rw [same,actual]
            exact tailNext

theorem extension : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalBoolItems.Supported env returns modifier control items)
 (fuel extra : Nat) (state : Solidity.Yul.LocalState env types) (final : Solidity.Yul.LocalState env out),
 Solidity.Yul.LocalBoolItems.run proof fuel state = .normal final →
 Solidity.Yul.LocalBoolItems.run proof (fuel+extra) state = .normal final := by
  intro env returns modifier control types out items proof fuel extra state final completed
  induction extra with
  | zero => exact completed
  | succ extra ih =>
    exact Solidity.Yul.LocalItemHorizon.successor env returns modifier control types out items proof (fuel+extra) state final ih

end Solidity.Yul.LocalItemHorizon
