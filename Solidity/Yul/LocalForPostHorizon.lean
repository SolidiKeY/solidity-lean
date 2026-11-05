import Solidity.Yul.LocalDefaultPostIter
import Solidity.Yul.LocalDefaultHorizon
import Solidity.Yul.LocalBoolHorizon

/-! Exact completed-run fuel stability for actual guard/body/post iterations.
Post values are discarded by the existing runner; raw post state is retained. -/
namespace Solidity.Yul.LocalForPostHorizon

theorem successor : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (post : Solidity.Source.RExpr env types .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported env types post)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state final : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalDefaultPostIter.run test step body fuel state = .normal final →
 Solidity.Yul.LocalDefaultPostIter.run test step body (fuel+1) state = .normal final := by
  intro env returns modifier u types out condition test post step items body fuel
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
        rw [Solidity.Yul.LocalDefaultPostIter.run,actual] at completed
        cases completed
      | ok value =>
        have ready : (Solidity.Yul.LocalBoolControl.eval test fuel state).1 ≠ .error .timeout := by
          rw [actual]
          intro impossible
          cases impossible
        have same := Solidity.Yul.LocalBoolHorizon.successor env types condition test fuel state ready
        rw [Solidity.Yul.LocalDefaultPostIter.run,actual] at completed
        rw [Solidity.Yul.LocalDefaultPostIter.run,same,actual]
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
            dsimp only at completed ⊢
            cases updated : Solidity.Yul.LocalBoolControl.eval step fuel middle with
            | mk postResult after =>
              cases postResult with
              | error halt =>
                rw [updated] at completed
                cases completed
              | ok _value =>
                have postReady : (Solidity.Yul.LocalBoolControl.eval step fuel middle).1 ≠ .error .timeout := by
                  rw [updated]
                  intro impossible
                  cases impossible
                have postSame := Solidity.Yul.LocalBoolHorizon.successor env types post step fuel middle postReady
                rw [updated] at completed
                rw [postSame,updated]
                exact ih after final completed

theorem extension : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (post : Solidity.Source.RExpr env types .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported env types post)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel extra : Nat) (state final : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalDefaultPostIter.run test step body fuel state = .normal final →
 Solidity.Yul.LocalDefaultPostIter.run test step body (fuel+extra) state = .normal final := by
  intro env returns modifier u types out condition test post step items body fuel extra state final completed
  induction extra with
  | zero => exact completed
  | succ extra ih =>
    exact Solidity.Yul.LocalForPostHorizon.successor env returns modifier u types out condition test post step items body (fuel+extra) state final ih

end Solidity.Yul.LocalForPostHorizon
