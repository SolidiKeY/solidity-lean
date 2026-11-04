import Solidity.Yul.LocalBoolForPost
import Solidity.Yul.LocalForPostHorizon

/-! Concrete scope/iteration agreement and completed full for-statement horizons.
Initializer growth and final caller restoration retain exact raw frames. -/
namespace Solidity.Yul.LocalForInitHorizon


theorem scope_agrees : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier control types out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier control items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolItemScope.run body fuel state =
 Solidity.Yul.LocalDefaultItems.blockRun (.body body) fuel state := by
  intro env returns modifier control types out items body fuel state
  cases fuel <;> rfl

theorem initializerSuccessor : ∀ (env : Solidity.Source.Env) (types : Solidity.Source.RCtx)
 (expr : Solidity.Source.RExpr env types .bool)
 (proof : Solidity.Yul.LocalBoolControl.Supported env types expr)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types)
 (final : Solidity.Yul.LocalState env (.bool :: types)),
 Solidity.Yul.LocalBoolInitialization.run proof fuel state = .normal final →
 Solidity.Yul.LocalBoolInitialization.run proof (fuel+1) state = .normal final := by
  intro env types expr proof fuel state final completed
  cases fuel with
  | zero => cases completed
  | succ fuel =>
    cases actual : Solidity.Yul.LocalBoolControl.eval proof fuel state with
    | mk result next =>
      cases result with
      | error halt =>
        simp only [Solidity.Yul.LocalBoolInitialization.run,actual,Solidity.Yul.LocalBoolInitialization.finish] at completed
        cases completed
      | ok value =>
        have ready : (Solidity.Yul.LocalBoolControl.eval proof fuel state).1 ≠ .error .timeout := by
          rw [actual]
          intro impossible
          cases impossible
        have same := Solidity.Yul.LocalBoolHorizon.successor env types expr proof fuel state ready
        simpa only [Solidity.Yul.LocalBoolInitialization.run,same,actual,Solidity.Yul.LocalBoolInitialization.finish] using completed


theorem iteration_agrees : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (post : Solidity.Source.RExpr env types .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported env types post)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolPostIter.run test step body fuel state =
 Solidity.Yul.LocalDefaultPostIter.run test step (.body body) fuel state := by
  intro env returns modifier u types out condition test post step items body fuel
  induction fuel with
  | zero => intro state; rfl
  | succ fuel ih =>
    intro state
    rw [Solidity.Yul.LocalBoolPostIter.run,Solidity.Yul.LocalDefaultPostIter.run]
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
          | normal middle =>
            dsimp only
            cases updated : Solidity.Yul.LocalBoolControl.eval step fuel middle with
            | mk postResult after =>
              cases postResult with
              | error halt => rfl
              | ok _value =>
                exact ih after


theorem iterationSuccessor : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (post : Solidity.Source.RExpr env types .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported env types post)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state final : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolPostIter.run test step body fuel state = .normal final →
 Solidity.Yul.LocalBoolPostIter.run test step body (fuel+1) state = .normal final := by
  intro env returns modifier u types out condition test post step items body fuel state final completed
  have before : Solidity.Yul.LocalDefaultPostIter.run test step (.body body) fuel state = .normal final :=
    (Solidity.Yul.LocalForInitHorizon.iteration_agrees env returns modifier u types out condition test post step items body fuel state).symm.trans completed
  have after := Solidity.Yul.LocalForPostHorizon.successor env returns modifier u types out condition test post step items (.body body) fuel state final before
  exact (Solidity.Yul.LocalForInitHorizon.iteration_agrees env returns modifier u types out condition test post step items body (fuel+1) state).trans after

theorem successor : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (init : Solidity.Source.RExpr env types .bool)
 (initializer : Solidity.Yul.LocalBoolControl.Supported env types init)
 (condition : Solidity.Source.RExpr env (.bool :: types) .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env (.bool :: types) condition)
 (post : Solidity.Source.RExpr env (.bool :: types) .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported env (.bool :: types) post)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ (.bool :: types) out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state final : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolForPost.run initializer test step body fuel state = .normal final →
 Solidity.Yul.LocalBoolForPost.run initializer test step body (fuel+1) state = .normal final := by
  intro env returns modifier u types out init initializer condition test post step items body fuel state final completed
  cases fuel with
  | zero => cases completed
  | succ fuel =>
    cases initialized : Solidity.Yul.LocalBoolInitialization.run initializer fuel state with
    | halted halt previous =>
      rw [Solidity.Yul.LocalBoolForPost.run,initialized] at completed
      cases completed
    | normal next =>
      have initSame := Solidity.Yul.LocalForInitHorizon.initializerSuccessor env types init initializer fuel state next initialized
      rw [Solidity.Yul.LocalBoolForPost.run,initialized] at completed
      rw [Solidity.Yul.LocalBoolForPost.run,initSame]
      dsimp only at completed ⊢
      cases iterated : Solidity.Yul.LocalBoolPostIter.run test step body fuel next with
      | halted halt previous =>
        rw [iterated] at completed
        simp only [Solidity.Yul.LocalBoolFor.close] at completed
        cases completed
      | normal middle =>
        rw [iterated] at completed
        have loopSame := Solidity.Yul.LocalForInitHorizon.iterationSuccessor env returns modifier u (.bool :: types) out condition test post step items body fuel next middle iterated
        rw [loopSame]
        exact completed

theorem extension : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (init : Solidity.Source.RExpr env types .bool)
 (initializer : Solidity.Yul.LocalBoolControl.Supported env types init)
 (condition : Solidity.Source.RExpr env (.bool :: types) .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env (.bool :: types) condition)
 (post : Solidity.Source.RExpr env (.bool :: types) .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported env (.bool :: types) post)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ (.bool :: types) out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel extra : Nat) (state final : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolForPost.run initializer test step body fuel state = .normal final →
 Solidity.Yul.LocalBoolForPost.run initializer test step body (fuel+extra) state = .normal final := by
  intro env returns modifier u types out init initializer condition test post step items body fuel extra state final completed
  induction extra with
  | zero => exact completed
  | succ extra ih =>
    exact Solidity.Yul.LocalForInitHorizon.successor env returns modifier u types out init initializer condition test post step items body (fuel+extra) state final ih

end Solidity.Yul.LocalForInitHorizon
