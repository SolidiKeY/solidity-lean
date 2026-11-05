import Solidity.Yul.LocalDefaultIfElse
import Solidity.Yul.LocalDefaultHorizon
import Solidity.Yul.LocalBoolHorizon

/-! Completed-run fuel stability for independently indexed default-item branches.
Concrete guard and selected restored-block producers are composed here. -/
namespace Solidity.Yul.LocalIfHorizon

theorem successor : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types yesOut noOut : Solidity.Source.RCtx)
 (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (yesItems : Solidity.Source.RItems env returns modifier control types yesOut)
 (yes : Solidity.Yul.LocalDefaultItems.Supported env returns modifier control yesItems)
 (noItems : Solidity.Source.RItems env returns modifier control types noOut)
 (no : Solidity.Yul.LocalDefaultItems.Supported env returns modifier control noItems)
 (fuel : Nat) (state final : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalDefaultIfElse.run test yes no fuel state = .normal final →
 Solidity.Yul.LocalDefaultIfElse.run test yes no (fuel+1) state = .normal final := by
  intro env returns modifier control types yesOut noOut condition test yesItems yes noItems no fuel state final completed
  cases fuel with
  | zero => cases completed
  | succ fuel =>
    cases actual : Solidity.Yul.LocalBoolControl.eval test fuel state with
    | mk result next =>
      cases result with
      | error halt =>
        simp only [Solidity.Yul.LocalDefaultIfElse.run,actual] at completed
        cases completed
      | ok value =>
        have ready : (Solidity.Yul.LocalBoolControl.eval test fuel state).1 ≠ .error .timeout := by
          rw [actual]
          intro impossible
          cases impossible
        have same := Solidity.Yul.LocalBoolHorizon.successor env types condition test fuel state ready
        cases choice : Solidity.Yul.LocalBoolControl.truth value with
        | false =>
          have branchDone : Solidity.Yul.LocalDefaultItems.blockRun no fuel next = .normal final := by
            simpa only [Solidity.Yul.LocalDefaultIfElse.run,actual,choice] using completed
          have branchNext := Solidity.Yul.LocalDefaultHorizon.blockSuccessor env returns modifier control types noOut noItems no fuel next final branchDone
          simpa only [Solidity.Yul.LocalDefaultIfElse.run,same,actual,choice,Bool.false_eq_true,if_false] using branchNext
        | true =>
          have branchDone : Solidity.Yul.LocalDefaultItems.blockRun yes fuel next = .normal final := by
            simpa only [Solidity.Yul.LocalDefaultIfElse.run,actual,choice] using completed
          have branchNext := Solidity.Yul.LocalDefaultHorizon.blockSuccessor env returns modifier control types yesOut yesItems yes fuel next final branchDone
          simpa only [Solidity.Yul.LocalDefaultIfElse.run,same,actual,choice,if_true] using branchNext

theorem extension : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types yesOut noOut : Solidity.Source.RCtx)
 (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (yesItems : Solidity.Source.RItems env returns modifier control types yesOut)
 (yes : Solidity.Yul.LocalDefaultItems.Supported env returns modifier control yesItems)
 (noItems : Solidity.Source.RItems env returns modifier control types noOut)
 (no : Solidity.Yul.LocalDefaultItems.Supported env returns modifier control noItems)
 (fuel extra : Nat) (state final : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalDefaultIfElse.run test yes no fuel state = .normal final →
 Solidity.Yul.LocalDefaultIfElse.run test yes no (fuel+extra) state = .normal final := by
  intro env returns modifier control types yesOut noOut condition test yesItems yes noItems no fuel extra state final completed
  induction extra with
  | zero => exact completed
  | succ extra ih =>
    exact Solidity.Yul.LocalIfHorizon.successor env returns modifier control types yesOut noOut condition test yesItems yes noItems no (fuel+extra) state final ih

end Solidity.Yul.LocalIfHorizon
