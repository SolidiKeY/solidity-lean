import Solidity.Calculus.Derive
import Solidity.Calculus.Spec
import Solidity.Calculus.SurfaceSpec

/-!
# `sol_spec` on a scoped obligation: `⊨ cspec!{f}`

`Calculus/SurfaceSpec.lean`'s `sol_spec` (`sol_symex; sol_spec_close`) on a scoped
goal `Valid φ`, `φ` a specification's obligation (`cspec!{f}`,
`Calculus/Spec.lean`): `sol_symex` runs the scoped strategy
(`Calculus/Symex.lean`), and each leaf it leaves is erased
(`Valid.of_erase`, where `Fml.posB` takes its hidden binders) and handed to
today's `sol_spec_prep` and `sol_spec_finish`.  The text is today's:
`sol_spec_prep` takes a scoped goal by this second elaborator, so
`sol_spec`, `sol_spec_close` and `sol_spec_try` work on either side.
-/

namespace Solidity

open Lean Elab Tactic Meta

/-- The scoped leaf `g : Valid ψ` as today's goal `Valid (ψ.erase [])`,
computed (`Valid.of_erase`, `Fml.posB` checked by the kernel). -/
def eraseLeaf (g : MVarId) : TacticM (Option MVarId) := g.withContext do
  let some (C, ψ) ← Symex.validGoal? g | return none
  let bool := mkConst ``Bool
  let nilCtx := mkApp (mkConst ``List.nil [0]) (mkConst ``LTy)
  let nilVar := mkApp (mkConst ``List.nil [0]) (mkConst ``Var)
  let hpTy := mkApp3 (mkConst ``Eq [1]) bool
    (mkApp2 (mkConst ``Option.isSome [0]) (mkApp (mkConst ``List [0]) (mkConst ``Var))
      (mkAppN (mkConst ``Fml.posB) #[C, nilCtx, ψ, nilVar])) (mkConst ``Bool.true)
  let hp ← try NFml.Derive.kernelLemma hpTy (mkApp2 (mkConst ``Eq.refl [1]) bool (mkConst ``Bool.true))
    catch _ => throwError "sol_spec: the leaf is not one its erasure closes (`Fml.posB`): a \
      hidden binder under a negation, a precondition or a modality, or named twice"
  let erased := mkAppN (mkConst ``Fml.erase) #[C, nilCtx, nilVar, ψ]
  let g' ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``NFml.Valid) C erased) (← g.getTag)
  g.assign (mkAppN (mkConst ``Valid.of_erase) #[C, ψ, hp, g'])
  return some (← Solidity.normValid g'.mvarId!)

/-- `sol_spec_prep` on a scoped leaf: erased, then today's. -/
@[tactic Solidity.tacticSol_spec_prep]
def evalSolSpecPrepCore : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let some g' ← eraseLeaf g | throwUnsupportedSyntax
  replaceMainGoal [g']
  evalTactic (← `(tactic| sol_spec_prep))

end Solidity
