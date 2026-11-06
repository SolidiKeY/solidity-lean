import Solidity.Calculus.Derive
import Solidity.Calculus.Spec
import Solidity.Calculus.SurfaceSpec

/-!
# `sol_spec` on a scoped obligation: `⊨ᶠ cspec!{f}`

`Calculus/SurfaceSpec.lean`'s `sol_spec` (`sol_symex; sol_spec_close`) on a scoped
goal `Fml.Valid φ`, `φ` a specification's obligation (`cspec!{f}`,
`Calculus/Spec.lean`): `sol_symex` runs the scoped strategy
(`Calculus/Symex.lean`), and each leaf it leaves is closed by
`sol_spec_prep`'s steps, which read a scoped leaf without its erasure
(`Calculus/CloseScoped.lean`).  The text is today's, so `sol_spec`,
`sol_spec_close` and `sol_spec_try` work on either side.
-/

namespace Solidity

open Lean Elab Tactic

register_option sol.spec.stepPrep : Bool := {
  defValue := true
  descr := "prepare local joined specification updates one at a time"
}

/-- Try local joined preparation at the existing preparation dispatch point.
Unsupported leaves fall through to the default elaborator without an enclosing
`first` tactic: that extra nesting exceeds the browser's stack on Counter.
The option permits an exact whole-leaf control and explicit recovery. -/
@[tactic Solidity.tacticSol_spec_prep]
def evalSolSpecPrep : Tactic := fun stx => do
  unless sol.spec.stepPrep.get (← getOptions) do throwUnsupportedSyntax
  try evalSolCloseJoinPrep stx
  catch _ => throwUnsupportedSyntax
  trace[Solidity.spec.preparation] "step"

end Solidity
