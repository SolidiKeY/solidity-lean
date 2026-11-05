import Solidity.Yul.LocalItemFailure
import Solidity.Yul.LocalDefaultNoGuard

/-! Concrete finite-horizon failure laws; actual runners and Source types are unchanged. -/
namespace Solidity.Yul.LocalLoopFailure

theorem block : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy) (modifier : Bool)
 (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalDefaultItems.Supported env returns modifier control items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types) (reached : Solidity.Source.RCtx)
 (halt : Solidity.Source.Halt) (next : Solidity.Yul.LocalState env reached),
 Solidity.Yul.LocalDefaultItems.blockRun proof fuel state = .halted halt next → halt = .timeout := by

  intro env returns modifier control types out items proof fuel state reached halt next failed
  cases fuel with
  | zero => cases failed; rfl
  | succ fuel =>
    change Solidity.Yul.LocalDefaultItems.close proof (Solidity.Yul.LocalDefaultItems.run proof fuel state) = .halted halt next at failed
    cases actual : Solidity.Yul.LocalDefaultItems.run proof fuel state with
    | normal after =>
      rw [actual] at failed
      cases failed
    | halted error after =>
      rw [actual] at failed
      have same := Solidity.Yul.LocalItemFailure.defaultItems env returns modifier control types out items proof fuel state _ error after actual
      cases failed
      exact same

theorem whileLoop : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (types out : Solidity.Source.RCtx) (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types) (reached : Solidity.Source.RCtx)
 (halt : Solidity.Source.Halt) (next : Solidity.Yul.LocalState env reached),
 Solidity.Yul.LocalDefaultWhile.run test body fuel state = .halted halt next → halt = .timeout := by

  intro env returns modifier u types out condition test items body fuel
  induction fuel with
  | zero =>
    intro state reached halt next failed
    cases failed
    rfl
  | succ fuel ih =>
    intro state reached halt next failed
    rw [Solidity.Yul.LocalDefaultWhile.run] at failed
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
            exact ih final reached halt next failed
          | halted error final =>
            rw [actualBody] at failed
            have same := Solidity.Yul.LocalLoopFailure.block env returns modifier ⟨true,u⟩ types out items body fuel after _ error final actualBody
            cases failed
            exact same
        · cases failed

theorem noPostTimeout : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types),
 ∃ (reached : Solidity.Source.RCtx) (next : Solidity.Yul.LocalState env reached),
 Solidity.Yul.LocalDefaultNoGuard.runNoPost body fuel state = .halted .timeout next := by

  intro env returns modifier u types out items body fuel state
  cases actual : Solidity.Yul.LocalDefaultNoGuard.runNoPost body fuel state with
  | normal next =>
    exact False.elim (Solidity.Yul.LocalDefaultNoGuard.no_normal_no_post env returns modifier u types out items body fuel state next actual)
  | halted halt next =>
    have same := Solidity.Yul.LocalLoopFailure.whileLoop env returns modifier u types out (.bool true) (.base (.literal true)) items body fuel state _ halt next actual
    cases same
    exact ⟨_,next,rfl⟩

theorem sourceNoPostTimeout : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (_body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph env)) (locals : Solidity.Source.Locals env.layout types)
 (world : Solidity.Source.St env),
 (Solidity.Source.forIter glob frame fuel nps ph .none .none (.block items) locals).run
 (Solidity.Source.L0 env,world) = (.error .timeout,(Solidity.Source.L0 env,world)) := by

  intro env returns modifier u types out items body glob frame fuel nps ph locals world
  have agreement := Solidity.Yul.LocalDefaultNoGuard.source_no_post_agrees env returns modifier u types out items body glob frame fuel nps ph locals world
  obtain ⟨reached,next,actual⟩ := Solidity.Yul.LocalLoopFailure.noPostTimeout env returns modifier u types out items body fuel (Solidity.Yul.LocalState.ofClean (locals,world))
  have unchanged := Solidity.Yul.LocalDefaultNoGuard.world_no_post env returns modifier u types out items body fuel (Solidity.Yul.LocalState.ofClean (locals,world))
  rw [actual] at agreement unchanged
  change next.2 = world at unchanged
  change some ((Except.error Solidity.Source.Halt.timeout : Solidity.Source.R (Solidity.Source.Out env.layout types types)),(Solidity.Source.L0 env,next.2)) = some _ at agreement
  rw [unchanged] at agreement
  exact (Option.some.inj agreement).symm

end Solidity.Yul.LocalLoopFailure
