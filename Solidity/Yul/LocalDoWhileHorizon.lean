import Solidity.Yul.LocalDefaultDoWhile
import Solidity.Yul.LocalDefaultHorizon
import Solidity.Yul.LocalBoolHorizon

/-! Exact completed-run fuel stability for actual body-first recursive do/while.
Concrete restored-body and guard laws fix the real recursive intermediate state. -/
namespace Solidity.Yul.LocalDoWhileHorizon

theorem successor : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state final : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalDefaultDoWhile.run test body fuel state = .normal final →
 Solidity.Yul.LocalDefaultDoWhile.run test body (fuel+1) state = .normal final := by
  intro env returns modifier u types out condition test items body fuel
  induction fuel with
  | zero =>
    intro state final completed
    cases completed
  | succ fuel ih =>
    intro state final completed
    cases bodyRun : Solidity.Yul.LocalDefaultItems.blockRun body fuel state with
    | halted halt previous =>
      rw [Solidity.Yul.LocalDefaultDoWhile.run,bodyRun] at completed
      cases completed
    | normal next =>
      have bodySame := Solidity.Yul.LocalDefaultHorizon.blockSuccessor env returns modifier ⟨true,u⟩ types out items body fuel state next bodyRun
      rw [Solidity.Yul.LocalDefaultDoWhile.run,bodyRun] at completed
      rw [Solidity.Yul.LocalDefaultDoWhile.run,bodySame]
      dsimp only at completed ⊢
      cases actual : Solidity.Yul.LocalBoolControl.eval test fuel next with
      | mk result after =>
        cases result with
        | error halt =>
          rw [actual] at completed
          cases completed
        | ok value =>
          have ready : (Solidity.Yul.LocalBoolControl.eval test fuel next).1 ≠ .error .timeout := by
            rw [actual]
            intro impossible
            cases impossible
          have same := Solidity.Yul.LocalBoolHorizon.successor env types condition test fuel next ready
          rw [actual] at completed
          rw [same,actual]
          dsimp only at completed ⊢
          cases choice : Solidity.Yul.LocalBoolControl.truth value with
          | false =>
            simpa only [choice,Bool.false_eq_true,if_false] using completed
          | true =>
            simp only [choice,if_true] at completed ⊢
            exact ih after final completed

theorem extension : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel extra : Nat) (state final : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalDefaultDoWhile.run test body fuel state = .normal final →
 Solidity.Yul.LocalDefaultDoWhile.run test body (fuel+extra) state = .normal final := by
  intro env returns modifier u types out condition test items body fuel extra state final completed
  induction extra with
  | zero => exact completed
  | succ extra ih =>
    exact Solidity.Yul.LocalDoWhileHorizon.successor env returns modifier u types out condition test items body (fuel+extra) state final ih

end Solidity.Yul.LocalDoWhileHorizon
