import Solidity.Syntax.Quote
import Solidity.Calculus.Hyp

/-!
# The strategy's tactics: their syntax, and the formula goal they work on

The strategy's tactics, declared once so that the scoped calculus and the
closer each add an elaborator to the same syntax: `sol_step`, `sol_symex`,
`sol_derive`, `sol_derive?`, `sol_chain?`, `sol_prove` and `sol_prove?`.
The elaborators are `Calculus/Symex.lean`'s (`sol_step`, `sol_symex`),
`Calculus/Derive.lean`'s (`sol_derive?`), `Calculus/ProvesDerive.lean`'s
(`sol_prove`, on `⊢ φ` and on `Valid φ`) and `Calculus/Closers.lean`'s
(`sol_prove?`).  The syntax kinds keep their names
(`Solidity.tacticSol_step`, `Solidity.ProofTree.tacticSol_derive?`, …), which
the elaborators are registered under.  Moved out of `Symex.lean`
(`docs/intrinsic.md`, W4 item 11).
-/

namespace Solidity

open Semantics

variable {C : Contract}

namespace Derive

open Lean Meta in
/-- A lemma `type` proved by `value`, checked by the kernel now, as
`decide +kernel` checks one. -/
def kernelLemma (type value : Expr) : MetaM Expr := do
  let n ← withOptions (Elab.async.set · false) <| mkAuxLemma [] type value
  return mkConst n

end Derive

/-! ## The syntax -/

/-- `sol_step`: fire the rule of the first active statement. -/
syntax (name := tacticSol_step) "sol_step" : tactic

/-- `sol_symex`: run the strategy until no modality is left.  With no goal
left it does nothing, as `sol_close` does. -/
syntax (name := tacticSol_symex) "sol_symex" : tactic

/-- `sol_derive`: run the strategy as a derivation, until no goal has a
modality left; what is left is for `close`. -/
syntax (name := tacticSol_derive) "sol_derive" : tactic

/-- `sol_prove`: the strategy as one kernel evaluation, on a goal `Γ ⊢ φ` or
`⊨ φ`; one goal `leafᵢ` per leaf the closer leaves. -/
syntax (name := tacticSol_prove) "sol_prove" : tactic

/-- `sol_prove?`: `sol_prove`, each leaf closed by the first tactic that
closes it; suggests the replay. -/
syntax (name := tacticSol_prove?) "sol_prove?" : tactic

namespace ProofTree

/-- `sol_derive?`: build the proof tree of the goal and suggest it as the walk
it is, one `apply` per rule, a `case` per branch. -/
syntax (name := tacticSol_derive?) "sol_derive?" : tactic

/-- `sol_chain?`: prove a chain as `sol_chain` does, and suggest the chain
written out. -/
syntax (name := tacticSol_chain?) "sol_chain?" : tactic

end ProofTree

end Solidity
