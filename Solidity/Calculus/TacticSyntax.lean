import Solidity.Calculus.NFmlQuote

/-!
# The strategy's tactics: their syntax, and the formula goal they work on

The strategy's tactics, declared once so that the scoped calculus and the
closer each add an elaborator to the same syntax: `sol_step`, `sol_symex`,
`sol_derive`, `sol_derive?`, `sol_chain?`, `sol_prove` and `sol_prove?`.
The scoped elaborators are `Calculus/Symex.lean`'s (`sol_step`,
`sol_symex`), `Calculus/Derive.lean`'s (`sol_prove`, `sol_derive?`),
`Calculus/ProvesDerive.lean`'s (`sol_prove`) and `Calculus/Closers.lean`'s
(`sol_prove?`); the closer's, on an `NFml.Valid` goal, are
`Calculus/NFmlDerive.lean`'s (`sol_prove`, `sol_prove?`) and this module's
(`sol_symex`).  The syntax kinds keep their names
(`Solidity.tacticSol_step`, `Solidity.ProofTree.tacticSol_derive?`, …), which
the scoped elaborators are registered under.

With them, the plumbing of a tactic on a goal `⊨ φ` (`normValid`,
`applyValid`), which the closer's drivers use too (`Calculus/NFmlClose.lean`,
`Calculus/Rewrite.lean`).
Moved out of `Symex.lean` (`docs/intrinsic.md`, W4 item 11).
-/

namespace Solidity

open Semantics

variable {C : Contract}

open Lean Elab Tactic Meta in
/-- Compute the formula inside a `⊨ _` goal, so the goal shows the result of
the rule rather than the call; the kernel re-checks it (`replaceTargetDefEq`).

A closed formula of a named contract — what `dl[C]{ … }` gives — is run by
the compiled code and quoted back (`NFml.quote`), as mini-solkey's
`normValid` does: `Meta.reduce` would unfold `symex 200 φ` by the
interpreter of `whnf`, which takes a minute on three storage writes.  Any
other formula (a variable in it, or an anonymous contract) falls back to
`Meta.reduce`. -/
def normValid (g : MVarId) : TacticM MVarId := do
  let ty ← instantiateMVars (← g.getType)
  let_expr NFml.Valid C φ := ty | throwError "expected a goal `Valid φ`"
  let φ ← instantiateMVars φ
  let φ' ← match C.constName?, φ.hasFVar || φ.hasMVar with
    | some n, false =>
      unsafe evalExpr Lean.Expr (mkConst ``Lean.Expr)
        (mkApp3 (mkConst ``NFml.quote) C (quoteConstName n) φ)
    | _, _ => withTransparency .all <| Meta.reduce φ (skipTypes := true) (skipProofs := true)
  g.replaceTargetDefEq (mkApp2 (mkConst ``NFml.Valid) C φ')

open Lean Elab Tactic Meta in
/-- The shape of the formula tactics: apply `lem`, a lemma `Valid ψ → Valid φ`
with `ψ` computed from `φ`, to the main goal, and compute `ψ` (`normValid`).
With `unchanged` given, a goal left as it was is an error, `tac: unchanged`. -/
def applyValid (tac : String) (lem : Lean.Term) (unchanged : Option MessageData := none) :
    TacticM Unit := do
  let g ← getMainGoal
  let before ← instantiateMVars (← g.getType)
  let [g'] ← g.apply (← elabTerm lem none) | throwError "{tac}: unexpected goals"
  let g'' ← normValid g'
  if let some msg := unchanged then
    if (← instantiateMVars (← g''.getType)) == before then throwError "{tac}: {msg}"
  replaceMainGoal [g'']

namespace NFml.Derive

open Lean Meta in
/-- A lemma `type` proved by `value`, checked by the kernel now, as
`decide +kernel` checks one. -/
def kernelLemma (type value : Expr) : MetaM Expr := do
  let n ← withOptions (Elab.async.set · false) <| mkAuxLemma [] type value
  return mkConst n

end NFml.Derive

/-! ## The syntax -/

/-- `sol_step`: fire the rule of the first active statement. -/
syntax (name := tacticSol_step) "sol_step" : tactic

/-- `sol_symex`: run the strategy until no modality is left.  With no goal
left it does nothing, as `sol_close` does. -/
syntax (name := tacticSol_symex) "sol_symex" : tactic

open Lean Elab Tactic Meta in
/-- `sol_symex` on a goal `⊨ φ` of the closer's formulas, which have no
modality: the strategy has nothing to fire, and `φ` is computed as `symex`
would leave it (`normValid`).  The goal a scoped leaf leaves for the closer, the erasure
`Valid ((H.wrap φ).erase ns)` (`Proves.close`), is one.  Declared before
the scoped strategy (`Symex.lean`), it is tried after it. -/
elab_rules : tactic
  | `(tactic| sol_symex) => do
    if (← getUnsolvedGoals).isEmpty then return
    let g ← getMainGoal
    let ty ← instantiateMVars (← g.getType)
    let_expr NFml.Valid _ _ := ty | throwUnsupportedSyntax
    replaceMainGoal [← normValid g]

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
