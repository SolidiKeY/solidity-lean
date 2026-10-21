import Lean

/-!
# Equation lemmas named by hand

`attribute [sol_eqns f_c₁ … f_cₙ] f` makes `f_c₁ … f_cₙ` the equation lemmas of
`f`: what `simp only [f]` and `rw [f]` rewrite with.

It is for the definitions the kernel evaluates, written with a recursor
rather than by `match` (`docs/intrinsic.md`, Gate G0, conditions 1 and 2):
Lean generates no per-constructor equations for them, only the unfolding to
the recursor.  Each such definition states its equations by `rfl` and is
then marked `@[irreducible]`, so that `simp` rewrites a constructor
application by its equation and leaves every other application alone
(`simp` never unfolds an irreducible definition); the kernel ignores the
attribute and still reduces it.  The equations must be named before
anything asks for them: Lean caches the first answer.

It is Mathlib's `@[eqns]` (`Mathlib/Tactic/Eqns.lean`), which this package
does not import; named apart so that a package importing both (`Bridge/`)
loads: two attributes of one name cannot be registered together.
-/

namespace Solidity

open Lean Meta Elab

/-- `@[sol_eqns l₁ … lₙ]`: the equation lemmas of a definition, named by hand. -/
syntax (name := sol_eqns) "sol_eqns" (ppSpace ident)* : attr

/-- The hand-named equation lemmas of each definition that has them. -/
initialize eqnsAttr : ParametricAttribute (Array Name) ←
  registerParametricAttribute {
    name := `sol_eqns
    descr := "the equation lemmas of a definition written with a recursor, named by hand"
    getParam := fun _ stx => do
      match stx with
      | `(attr| sol_eqns $names*) => names.mapM realizeGlobalConstNoOverloadWithInfo
      | _ => throwUnsupportedSyntax
  }

initialize registerGetEqnsFn fun declName => do
  return eqnsAttr.getParam? (← getEnv) declName

end Solidity
