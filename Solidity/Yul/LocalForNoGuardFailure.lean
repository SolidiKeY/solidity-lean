import Solidity.Yul.LocalBoolForNoGuard
import Solidity.Yul.LocalForInitHorizon
import Solidity.Yul.LocalBoolDivergence

/-! Finite noncompletion of initialized omitted-guard Boolean for adapters.
Certified bodies have no break/return. Halts are not classified here. -/
namespace Solidity.Yul.LocalForNoGuardFailure

theorem no_normal : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (init : Solidity.Source.RExpr env types .bool)
 (initializer : Solidity.Yul.LocalBoolControl.Supported env types init)
 (post : Solidity.Source.RExpr env (.bool :: types) .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported env (.bool :: types) post)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ (.bool :: types) out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state next : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolForNoGuard.run initializer step body fuel state ≠ .normal next := by
  intro env returns modifier u types out init initializer post step items body fuel state next bad
  cases fuel with
  | zero => cases bad
  | succ fuel =>
    unfold Solidity.Yul.LocalBoolForNoGuard.run at bad
    rw [Solidity.Yul.LocalBoolForPost.run] at bad
    cases initialized : Solidity.Yul.LocalBoolInitialization.run initializer fuel state with
    | halted halt previous =>
      rw [initialized] at bad
      cases bad
    | normal entered =>
      rw [initialized] at bad
      dsimp only at bad
      cases iterated : Solidity.Yul.LocalBoolPostIter.run (.base (.literal true)) step body fuel entered with
      | halted halt previous =>
        rw [iterated] at bad
        cases bad
      | normal after =>
        have agrees := Solidity.Yul.LocalForInitHorizon.iteration_agrees env returns modifier u
          (.bool :: types) out (.bool true) (.base (.literal true)) post step items body fuel entered
        exact Solidity.Yul.LocalDefaultPostIter.no_normal env returns modifier u
          (.bool :: types) out post step items (.body body) fuel entered after
          (agrees.symm.trans iterated)

theorem no_post_normal : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (init : Solidity.Source.RExpr env types .bool)
 (initializer : Solidity.Yul.LocalBoolControl.Supported env types init)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ (.bool :: types) out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state next : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolForNoGuard.runNoPost initializer body fuel state ≠ .normal next := by
  intro env returns modifier u types out init initializer items body fuel state next bad
  cases fuel with
  | zero => cases bad
  | succ fuel =>
    unfold Solidity.Yul.LocalBoolForNoGuard.runNoPost at bad
    rw [Solidity.Yul.LocalBoolFor.run] at bad
    cases initialized : Solidity.Yul.LocalBoolInitialization.run initializer fuel state with
    | halted halt previous =>
      rw [initialized] at bad
      cases bad
    | normal entered =>
      rw [initialized] at bad
      dsimp only at bad
      cases iterated : Solidity.Yul.LocalBoolWhile.run (.base (.literal true)) body fuel entered with
      | halted halt previous =>
        rw [iterated] at bad
        cases bad
      | normal after =>
        exact Solidity.Yul.LocalBoolDivergence.no_normal env returns modifier u
          (.bool :: types) out items body fuel entered after iterated

/-- Concrete clean-input Source noncompletion; no dirty readback adequacy. -/
theorem source_no_normal : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l u : Bool) (types out : Solidity.Source.RCtx)
 (init : Solidity.Source.RExpr env types .bool)
 (initializer : Solidity.Yul.LocalBoolControl.Supported env types init)
 (post : Solidity.Source.RExpr env (.bool :: types) .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported env (.bool :: types) post)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ (.bool :: types) out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals next : Solidity.Source.Locals env.layout types) (world finalWorld : Solidity.Source.St env),
 (Solidity.Source.execS glob frame fuel nps ph
   (.forLoop (l := l) (.declInit (τ := .bool) init (by rfl)) .none (.some post) (.block items)) locals).run
   (Solidity.Source.L0 env,world) ≠ (.ok (.normal next),(Solidity.Source.L0 env,finalWorld)) := by
  intro env returns modifier l u types out init initializer post step items body glob frame fuel nps ph locals next world finalWorld
  have agreement := Solidity.Yul.LocalBoolForNoGuard.source_agrees env returns modifier l u types out
    init initializer post step items body glob frame fuel nps ph locals world
  cases actual : Solidity.Yul.LocalBoolForNoGuard.run initializer step body fuel
    (Solidity.Yul.LocalState.ofClean (locals,world)) with
  | normal after =>
    exact False.elim (Solidity.Yul.LocalForNoGuardFailure.no_normal env returns modifier u types out
      init initializer post step items body fuel (Solidity.Yul.LocalState.ofClean (locals,world)) after actual)
  | halted halt after =>
    rw [actual] at agreement
    change some ((Except.error halt : Solidity.Source.R (Solidity.Source.Out env.layout types types)),
      (Solidity.Source.L0 env,after.2)) = some _ at agreement
    intro bad
    rw [bad] at agreement
    cases agreement


/-- Concrete clean-input Source noncompletion; no dirty readback adequacy. -/
theorem source_no_post_normal : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l u : Bool) (types out : Solidity.Source.RCtx)
 (init : Solidity.Source.RExpr env types .bool)
 (initializer : Solidity.Yul.LocalBoolControl.Supported env types init)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ (.bool :: types) out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals next : Solidity.Source.Locals env.layout types) (world finalWorld : Solidity.Source.St env),
 (Solidity.Source.execS glob frame fuel nps ph
   (.forLoop (l := l) (.declInit (τ := .bool) init (by rfl)) .none .none (.block items)) locals).run
   (Solidity.Source.L0 env,world) ≠ (.ok (.normal next),(Solidity.Source.L0 env,finalWorld)) := by
  intro env returns modifier l u types out init initializer items body glob frame fuel nps ph locals next world finalWorld
  have agreement := Solidity.Yul.LocalBoolForNoGuard.source_no_post_agrees env returns modifier l u types out
    init initializer items body glob frame fuel nps ph locals world
  cases actual : Solidity.Yul.LocalBoolForNoGuard.runNoPost initializer body fuel
    (Solidity.Yul.LocalState.ofClean (locals,world)) with
  | normal after =>
    exact False.elim (Solidity.Yul.LocalForNoGuardFailure.no_post_normal env returns modifier u types out
      init initializer items body fuel (Solidity.Yul.LocalState.ofClean (locals,world)) after actual)
  | halted halt after =>
    rw [actual] at agreement
    change some ((Except.error halt : Solidity.Source.R (Solidity.Source.Out env.layout types types)),
      (Solidity.Source.L0 env,after.2)) = some _ at agreement
    intro bad
    rw [bad] at agreement
    cases agreement

end Solidity.Yul.LocalForNoGuardFailure
