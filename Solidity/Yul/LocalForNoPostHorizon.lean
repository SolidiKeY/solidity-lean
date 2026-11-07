import Solidity.Yul.LocalForInitHorizon
import Solidity.Yul.LocalWhileHorizon

/-! Exact Boolean/default while agreement and completed no-post for horizons.
Uses existing scope, initializer and concrete while horizon producers. -/
namespace Solidity.Yul.LocalForNoPostHorizon

theorem iteration_agrees : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolWhile.run test body fuel state =
 Solidity.Yul.LocalDefaultWhile.run test (.body body) fuel state := by
  intro env returns modifier u types out condition test items body fuel
  induction fuel with
  | zero => intro state; rfl
  | succ fuel ih =>
    intro state
    rw [Solidity.Yul.LocalBoolWhile.run,Solidity.Yul.LocalDefaultWhile.run]
    cases actual : Solidity.Yul.LocalBoolControl.eval test fuel state with
    | mk result next =>
      cases result with
      | error halt => rfl
      | ok value =>
        dsimp only
        rw [Solidity.Yul.LocalForInitHorizon.scope_agrees env returns modifier ⟨true,u⟩ types out items body fuel next]
        cases choice : Solidity.Yul.LocalBoolControl.truth value with
        | false => simp only [choice,Bool.false_eq_true,if_false]
        | true =>
          simp only [choice,if_true]
          cases bodyRun : Solidity.Yul.LocalDefaultItems.blockRun (.body body) fuel next with
          | halted halt previous => rfl
          | normal middle => exact ih middle


theorem iterationSuccessor : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state final : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolWhile.run test body fuel state = .normal final →
 Solidity.Yul.LocalBoolWhile.run test body (fuel+1) state = .normal final := by
  intro env returns modifier u types out condition test items body fuel state final completed
  have before : Solidity.Yul.LocalDefaultWhile.run test (.body body) fuel state = .normal final :=
    (Solidity.Yul.LocalForNoPostHorizon.iteration_agrees env returns modifier u types out condition test items body fuel state).symm.trans completed
  have after := Solidity.Yul.LocalWhileHorizon.successor env returns modifier u types out condition test items (.body body) fuel state final before
  exact (Solidity.Yul.LocalForNoPostHorizon.iteration_agrees env returns modifier u types out condition test items body (fuel+1) state).trans after


theorem successor : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (init : Solidity.Source.RExpr env types .bool)
 (initializer : Solidity.Yul.LocalBoolControl.Supported env types init)
 (condition : Solidity.Source.RExpr env (.bool :: types) .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env (.bool :: types) condition)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ (.bool :: types) out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state final : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolFor.run initializer test body fuel state = .normal final →
 Solidity.Yul.LocalBoolFor.run initializer test body (fuel+1) state = .normal final := by
  intro env returns modifier u types out init initializer condition test items body fuel state final completed
  cases fuel with
  | zero => cases completed
  | succ fuel =>
    cases initialized : Solidity.Yul.LocalBoolInitialization.run initializer fuel state with
    | halted halt previous =>
      rw [Solidity.Yul.LocalBoolFor.run,initialized] at completed
      cases completed
    | normal next =>
      have initSame := Solidity.Yul.LocalForInitHorizon.initializerSuccessor env types init initializer fuel state next initialized
      rw [Solidity.Yul.LocalBoolFor.run,initialized] at completed
      rw [Solidity.Yul.LocalBoolFor.run,initSame]
      dsimp only at completed ⊢
      cases iterated : Solidity.Yul.LocalBoolWhile.run test body fuel next with
      | halted halt previous =>
        rw [iterated] at completed
        simp only [Solidity.Yul.LocalBoolFor.close] at completed
        cases completed
      | normal middle =>
        rw [iterated] at completed
        have loopSame := Solidity.Yul.LocalForNoPostHorizon.iterationSuccessor env returns modifier u (.bool :: types) out condition test items body fuel next middle iterated
        rw [loopSame]
        exact completed

theorem extension : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (init : Solidity.Source.RExpr env types .bool)
 (initializer : Solidity.Yul.LocalBoolControl.Supported env types init)
 (condition : Solidity.Source.RExpr env (.bool :: types) .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env (.bool :: types) condition)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ (.bool :: types) out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel extra : Nat) (state final : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolFor.run initializer test body fuel state = .normal final →
 Solidity.Yul.LocalBoolFor.run initializer test body (fuel+extra) state = .normal final := by
  intro env returns modifier u types out init initializer condition test items body fuel extra state final completed
  induction extra with
  | zero => exact completed
  | succ extra ih =>
    exact Solidity.Yul.LocalForNoPostHorizon.successor env returns modifier u types out init initializer condition test items body (fuel+extra) state final ih

end Solidity.Yul.LocalForNoPostHorizon
