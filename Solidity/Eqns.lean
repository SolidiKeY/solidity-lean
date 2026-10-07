import Lean

/-!
# Equation lemmas named by hand

`attribute [eqns f_c₁ … f_cₙ] f` makes `f_c₁ … f_cₙ` the equation lemmas of
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
-/

namespace Solidity

open Lean Meta Elab

/-- `@[eqns l₁ … lₙ]`: the equation lemmas of a definition, named by hand. -/
syntax (name := eqns) "eqns" (ppSpace ident)* : attr

/-- The hand-named equation lemmas of each definition that has them. -/
initialize eqnsAttr : ParametricAttribute (Array Name) ←
  registerParametricAttribute {
    name := `eqns
    descr := "the equation lemmas of a definition written with a recursor, named by hand"
    getParam := fun _ stx => do
      match stx with
      | `(attr| eqns $names*) => names.mapM realizeGlobalConstNoOverloadWithInfo
      | _ => throwUnsupportedSyntax
  }

initialize registerGetEqnsFn fun declName => do
  return eqnsAttr.getParam? (← getEnv) declName

end Solidity
