import Solidity.Yul.LocalPostHorizon

/-! Exact reductions and finite-horizon results for certified constant loop expressions. -/
namespace Solidity.Yul.LocalLoopReductions

theorem falseDoWhile : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalDefaultDoWhile.run (.base (.literal false)) body (fuel+2) state =
 Solidity.Yul.LocalDefaultItems.blockRun body (fuel+1) state := by

  intro env returns modifier u types out items body fuel state
  rw [Solidity.Yul.LocalDefaultDoWhile.run]
  cases actual : Solidity.Yul.LocalDefaultItems.blockRun body (fuel+1) state <;> rfl

theorem literalPost : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (types out : Solidity.Source.RCtx) (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalDefaultPostIter.run test (.base (.literal false)) body fuel state =
 Solidity.Yul.LocalDefaultPostIter.run test (.base (.literal true)) body fuel state := by

  intro env returns modifier u types out condition test items body fuel
  induction fuel with
  | zero => intro state; rfl
  | succ fuel ih =>
    intro state
    conv =>
      lhs
      rw [Solidity.Yul.LocalDefaultPostIter.run]
    conv =>
      rhs
      rw [Solidity.Yul.LocalDefaultPostIter.run]
    cases actual : Solidity.Yul.LocalBoolControl.eval test fuel state with
    | mk result after =>
      dsimp only []
      cases result with
      | error error => rfl
      | ok value =>
        dsimp only []
        cases choice : Solidity.Yul.LocalBoolControl.truth value with
        | false => simp only [Bool.false_eq_true,if_false]
        | true =>
          simp only [if_true]
          cases actualBody : Solidity.Yul.LocalDefaultItems.blockRun body fuel after with
          | halted error final => rfl
          | normal final =>
            cases fuel with
            | zero => rfl
            | succ fuel => exact ih final

theorem trueDoWhileTimeout : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types),
 ∃ (reached : Solidity.Source.RCtx) (next : Solidity.Yul.LocalState env reached),
 Solidity.Yul.LocalDefaultDoWhile.run (.base (.literal true)) body fuel state = .halted .timeout next := by

  intro env returns modifier u types out items body fuel state
  cases actual : Solidity.Yul.LocalDefaultDoWhile.run (.base (.literal true)) body fuel state with
  | normal next =>
    exact False.elim (Solidity.Yul.LocalDefaultDoWhile.no_normal env returns modifier u types out items body fuel state next actual)
  | halted halt next =>
    have same := Solidity.Yul.LocalPostHorizon.doWhileLoop env returns modifier u types out (.bool true) (.base (.literal true)) items body fuel state _ halt next actual
    cases same
    exact ⟨_,next,rfl⟩

theorem sourceTrueDoWhileTimeout : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy) (modifier l u : Bool)
 (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (_body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph env)) (locals : Solidity.Source.Locals env.layout types)
 (world : Solidity.Source.St env),
 (Solidity.Source.execS glob frame fuel nps ph (.doWhile (l := l) (.block items) (.bool true)) locals).run
 (Solidity.Source.L0 env,world) = (.error .timeout,(Solidity.Source.L0 env,world)) := by

  intro env returns modifier l u types out items body glob frame fuel nps ph locals world
  have agreement := Solidity.Yul.LocalDefaultDoWhile.source_agrees env returns modifier l u types out (.bool true) (.base (.literal true)) items body glob frame fuel nps ph locals world
  obtain ⟨reached,next,actual⟩ := Solidity.Yul.LocalLoopReductions.trueDoWhileTimeout env returns modifier u types out items body fuel (Solidity.Yul.LocalState.ofClean (locals,world))
  have unchanged := Solidity.Yul.LocalDefaultDoWhile.world env returns modifier u types out (.bool true) (.base (.literal true)) items body fuel (Solidity.Yul.LocalState.ofClean (locals,world))
  rw [actual] at agreement unchanged
  change next.2 = world at unchanged
  change some ((Except.error Solidity.Source.Halt.timeout : Solidity.Source.R (Solidity.Source.Out env.layout types types)),(Solidity.Source.L0 env,next.2)) = some _ at agreement
  rw [unchanged] at agreement
  exact (Option.some.inj agreement).symm

end Solidity.Yul.LocalLoopReductions
