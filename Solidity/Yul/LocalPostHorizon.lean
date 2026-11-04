import Solidity.Yul.LocalLoopFailure
import Solidity.Yul.LocalDefaultDoWhile

/-! Concrete post-iteration and body-first finite-horizon laws. -/
namespace Solidity.Yul.LocalPostHorizon

theorem postIteration : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (types out : Solidity.Source.RCtx) (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (post : Solidity.Source.RExpr env types .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported env types post)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types) (reached : Solidity.Source.RCtx)
 (halt : Solidity.Source.Halt) (next : Solidity.Yul.LocalState env reached),
 Solidity.Yul.LocalDefaultPostIter.run test step body fuel state = .halted halt next → halt = .timeout := by

  intro env returns modifier u types out condition test post step items body fuel
  induction fuel with
  | zero => intro state reached halt next failed; cases failed; rfl
  | succ fuel ih =>
    intro state reached halt next failed
    rw [Solidity.Yul.LocalDefaultPostIter.run] at failed
    cases actual : Solidity.Yul.LocalBoolControl.eval test fuel state with
    | mk result after =>
      rw [actual] at failed
      cases result with
      | error error =>
        have same := Solidity.Yul.LocalBoolFailure.control env types condition test fuel state error (congrArg Prod.fst actual)
        cases failed
        exact same
      | ok value =>
        dsimp only [] at failed
        split at failed
        · cases actualBody : Solidity.Yul.LocalDefaultItems.blockRun body fuel after with
          | normal final =>
            rw [actualBody] at failed
            dsimp only [] at failed
            cases updated : Solidity.Yul.LocalBoolControl.eval step fuel final with
            | mk postResult afterPost =>
              rw [updated] at failed
              cases postResult with
              | error error =>
                have same := Solidity.Yul.LocalBoolFailure.control env types post step fuel final error (congrArg Prod.fst updated)
                cases failed
                exact same
              | ok _value => exact ih afterPost reached halt next failed
          | halted error final =>
            rw [actualBody] at failed
            have same := Solidity.Yul.LocalLoopFailure.block env returns modifier ⟨true,u⟩ types out items body fuel after _ error final actualBody
            cases failed
            exact same
        · cases failed

theorem doWhileLoop : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (types out : Solidity.Source.RCtx) (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types) (reached : Solidity.Source.RCtx)
 (halt : Solidity.Source.Halt) (next : Solidity.Yul.LocalState env reached),
 Solidity.Yul.LocalDefaultDoWhile.run test body fuel state = .halted halt next → halt = .timeout := by

  intro env returns modifier u types out condition test items body fuel
  induction fuel with
  | zero => intro state reached halt next failed; cases failed; rfl
  | succ fuel ih =>
    intro state reached halt next failed
    rw [Solidity.Yul.LocalDefaultDoWhile.run] at failed
    cases actualBody : Solidity.Yul.LocalDefaultItems.blockRun body fuel state with
    | normal after =>
      rw [actualBody] at failed
      dsimp only [] at failed
      cases actual : Solidity.Yul.LocalBoolControl.eval test fuel after with
      | mk result final =>
        rw [actual] at failed
        cases result with
        | error error =>
          have same := Solidity.Yul.LocalBoolFailure.control env types condition test fuel after error (congrArg Prod.fst actual)
          cases failed
          exact same
        | ok value =>
          dsimp only [] at failed
          split at failed
          · exact ih final reached halt next failed
          · cases failed
    | halted error after =>
      rw [actualBody] at failed
      have same := Solidity.Yul.LocalLoopFailure.block env returns modifier ⟨true,u⟩ types out items body fuel state _ error after actualBody
      cases failed
      exact same

theorem omittedPostTimeout : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (types out : Solidity.Source.RCtx) (post : Solidity.Source.RExpr env types .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported env types post)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types),
 ∃ (reached : Solidity.Source.RCtx) (next : Solidity.Yul.LocalState env reached),
 Solidity.Yul.LocalDefaultNoGuard.run step body fuel state = .halted .timeout next := by

  intro env returns modifier u types out post step items body fuel state
  cases actual : Solidity.Yul.LocalDefaultNoGuard.run step body fuel state with
  | normal next =>
    exact False.elim (Solidity.Yul.LocalDefaultNoGuard.no_normal env returns modifier u types out post step items body fuel state next actual)
  | halted halt next =>
    have same := Solidity.Yul.LocalPostHorizon.postIteration env returns modifier u types out (.bool true) (.base (.literal true)) post step items body fuel state _ halt next actual
    cases same
    exact ⟨_,next,rfl⟩

theorem sourcePostTimeout : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (types out : Solidity.Source.RCtx) (post : Solidity.Source.RExpr env types .bool)
 (_step : Solidity.Yul.LocalBoolControl.Supported env types post)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (_body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph env)) (locals : Solidity.Source.Locals env.layout types)
 (world : Solidity.Source.St env),
 (Solidity.Source.forIter glob frame fuel nps ph .none (.some post) (.block items) locals).run
 (Solidity.Source.L0 env,world) = (.error .timeout,(Solidity.Source.L0 env,world)) := by

  intro env returns modifier u types out post step items body glob frame fuel nps ph locals world
  have agreement := Solidity.Yul.LocalDefaultNoGuard.source_agrees env returns modifier u types out post step items body glob frame fuel nps ph locals world
  obtain ⟨reached,next,actual⟩ := Solidity.Yul.LocalPostHorizon.omittedPostTimeout env returns modifier u types out post step items body fuel (Solidity.Yul.LocalState.ofClean (locals,world))
  have unchanged := Solidity.Yul.LocalDefaultNoGuard.world env returns modifier u types out post step items body fuel (Solidity.Yul.LocalState.ofClean (locals,world))
  rw [actual] at agreement unchanged
  change next.2 = world at unchanged
  change some ((Except.error Solidity.Source.Halt.timeout : Solidity.Source.R (Solidity.Source.Out env.layout types types)),(Solidity.Source.L0 env,next.2)) = some _ at agreement
  rw [unchanged] at agreement
  exact (Option.some.inj agreement).symm

end Solidity.Yul.LocalPostHorizon
