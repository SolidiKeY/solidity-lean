import Solidity.Yul.LocalDefaultWhile
import Solidity.Yul.LocalDefaultHorizon
import Solidity.Yul.LocalBoolHorizon

/-! Exact completed-run fuel stability for the actual recursive default-scoped while.
Concrete guard/block laws fix each iteration; timeout prefixes may differ. -/
namespace Solidity.Yul.LocalWhileHorizon

theorem successor : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state final : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalDefaultWhile.run test body fuel state = .normal final →
 Solidity.Yul.LocalDefaultWhile.run test body (fuel+1) state = .normal final := by
  intro env returns modifier u types out condition test items body fuel
  induction fuel with
  | zero =>
    intro state final completed
    cases completed
  | succ fuel ih =>
    intro state final completed
    cases actual : Solidity.Yul.LocalBoolControl.eval test fuel state with
    | mk result next =>
      cases result with
      | error halt =>
        rw [Solidity.Yul.LocalDefaultWhile.run,actual] at completed
        cases completed
      | ok value =>
        have ready : (Solidity.Yul.LocalBoolControl.eval test fuel state).1 ≠ .error .timeout := by
          rw [actual]
          intro impossible
          cases impossible
        have same := Solidity.Yul.LocalBoolHorizon.successor env types condition test fuel state ready
        rw [Solidity.Yul.LocalDefaultWhile.run,actual] at completed
        rw [Solidity.Yul.LocalDefaultWhile.run,same,actual]
        dsimp only at completed ⊢
        cases choice : Solidity.Yul.LocalBoolControl.truth value with
        | false =>
          simpa only [choice,Bool.false_eq_true,if_false] using completed
        | true =>
          simp only [choice,if_true] at completed ⊢
          cases bodyRun : Solidity.Yul.LocalDefaultItems.blockRun body fuel next with
          | halted halt previous =>
            rw [bodyRun] at completed
            cases completed
          | normal middle =>
            rw [bodyRun] at completed
            have bodySame := Solidity.Yul.LocalDefaultHorizon.blockSuccessor env returns modifier ⟨true,u⟩ types out items body fuel next middle bodyRun
            rw [bodySame]
            exact ih middle final completed

theorem extension : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel extra : Nat) (state final : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalDefaultWhile.run test body fuel state = .normal final →
 Solidity.Yul.LocalDefaultWhile.run test body (fuel+extra) state = .normal final := by
  intro env returns modifier u types out condition test items body fuel extra state final completed
  induction extra with
  | zero => exact completed
  | succ extra ih =>
    exact Solidity.Yul.LocalWhileHorizon.successor env returns modifier u types out condition test items body (fuel+extra) state final ih

end Solidity.Yul.LocalWhileHorizon
