import Solidity.Yul.LocalBoolDoWhile

/-! No finite normal completion for constant-true certified do/while loops. -/
namespace Solidity.Yul.LocalBoolDoDivergence

theorem no_normal : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state next : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolDoWhile.run (.base (.literal true)) body fuel state ≠ .normal next := by

  intro env returns modifier u types out items body fuel
  induction fuel with
  | zero =>
    intro state next bad
    cases bad
  | succ fuel ih =>
    intro state next
    rw [Solidity.Yul.LocalBoolDoWhile.run]
    cases actual : Solidity.Yul.LocalBoolItemScope.run body fuel state with
    | halted halt after =>
      intro bad
      cases bad
    | normal after =>
      cases fuel with
      | zero =>
        intro bad
        cases bad
      | succ fuel =>
        change Solidity.Yul.LocalBoolDoWhile.run (.base (.literal true)) body (fuel+1) after ≠ .normal next
        exact ih after next


/-- Actual Source noncompletion from a clean frame; no halt classification or dirty correspondence. -/
theorem source_no_normal : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l u : Bool) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals next : Solidity.Source.Locals env.layout types) (world finalWorld : Solidity.Source.St env),
 (Solidity.Source.execS glob frame fuel nps ph
   (.doWhile (l := l) (.block items) (.bool true)) locals).run
   (Solidity.Source.L0 env,world) ≠ (.ok (.normal next),(Solidity.Source.L0 env,finalWorld)) := by


  intro env returns modifier l u types out items body glob frame fuel nps ph locals next world finalWorld
  have agreement := Solidity.Yul.LocalBoolDoWhile.source_agrees env returns modifier l u types out
    (.bool true) (.base (.literal true)) items body glob frame fuel nps ph locals world
  cases actual : Solidity.Yul.LocalBoolDoWhile.run (.base (.literal true)) body fuel
    (Solidity.Yul.LocalState.ofClean (locals,world)) with
  | normal after =>
    exact False.elim (Solidity.Yul.LocalBoolDoDivergence.no_normal env returns modifier u types out
      items body fuel (Solidity.Yul.LocalState.ofClean (locals,world)) after actual)
  | halted halt after =>
    rw [actual] at agreement
    change some ((Except.error halt : Solidity.Source.R (Solidity.Source.Out env.layout types types)),
      (Solidity.Source.L0 env,after.2)) = some _ at agreement
    intro bad
    rw [bad] at agreement
    cases agreement


end Solidity.Yul.LocalBoolDoDivergence
