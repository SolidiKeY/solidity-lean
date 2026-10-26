import Solidity.Calculus.Preconditions
import Solidity.Tools.Counterexample

/-!
# Certified precondition audits

The audit checks the entry condition independently of its program. Both answers
retain a kernel-checked theorem tied to the original scoped obligation:
`PreconditionsImpossible` proves vacuity; `PreconditionsPossible` is a certified
refutation of impossibility. An unfinished bounded search reports unknown.
No unsuccessful search is called evidence for either answer.
-/

namespace Solidity.Tools

open Lean Elab Command Term Meta

/-- The report distinguishes lack of a certificate from either proved answer. -/
inductive PreconditionVerdict where
  | impossible
  | possible
  | unknown (reason : String)
  deriving Repr, Inhabited

private def auditAxioms : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]

private def closedTerm (t : Term) (expected : Expr) : TermElabM Expr := do
  let e ← Term.withoutErrToSorry <| Term.elabTerm t (some expected)
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasMVar || e.hasFVar || e.hasSorry then throwError "incomplete audit certificate"
  pure e

/-- One independently bounded search; only a complete proof term can succeed. -/
private def auditProof? (ty : Expr) (tac : TSyntax `tactic) : TermElabM (Option Expr) := do
  let saved ← Term.saveState
  let messages ← Core.getMessageLog
  let result ← withCurrHeartbeats <| tryCatchRuntimeEx (do
    let goal ← mkFreshExprSyntheticOpaqueMVar ty
    let goals ← Tactic.run goal.mvarId! (Tactic.evalTactic tac)
    unless goals.isEmpty do return none
    let proof ← instantiateMVars goal
    if proof.hasMVar || proof.hasFVar || proof.hasSorry then return none
    pure (some proof)) fun _ => pure none
  if result.isNone then saved.restore
  else Core.setMessageLog messages
  pure result

/-- Audit a closed formula of a named contract, retaining the selected theorem
at `name`. Both searches are independently bounded by the ambient heartbeat limit. -/
def auditPreconditions (φ : Expr) (name : Lean.Name) : TermElabM PreconditionVerdict := do
  if φ.hasMVar || φ.hasFVar || φ.hasSorry then
    return .unknown "the obligation is not a closed checked term"
  let type ← whnf (← inferType φ)
  let (``Fml, #[C, Γ]) := type.getAppFnArgs
    | return .unknown "expected a scoped formula"
  unless (← whnf Γ).isAppOf ``List.nil do
    return .unknown "the obligation has free locals"
  unless C.isConst do
    return .unknown "the contract is not a named declaration"
  let check ← mkAppM ``Fml.entryNegative? #[φ]
  let (``Option.some, #[_, value]) := (← whnf check).getAppFnArgs
    | return .unknown "no leading implication under parameter binders"
  let ψ ← whnf (← mkAppM ``Subtype.val #[value])
  let origin ← mkAppM ``Subtype.property #[value]
  let emptyTy ← mkAppM ``Fml.Valid #[ψ]
  let empty ← auditProof? emptyTy (← `(tactic| first | sol_close | sol_decide))
  let (verdict, proof, certificate) ← if let some proof := empty then
      pure (PreconditionVerdict.impossible, proof, ``Fml.PreconditionsImpossible)
    else
      let some proof ← auditProof? (mkNot emptyTy) (← `(tactic| sol_refute))
        | return .unknown "neither search produced a certificate within its budget"
      pure (PreconditionVerdict.possible, proof, ``Fml.PreconditionsPossible)
  let ty ← mkAppM certificate #[φ]
  let term ← `(⟨$(← exprToSyntax ψ), $(← exprToSyntax origin), $(← exprToSyntax proof)⟩)
  let proof ← closedTerm term ty
  let saved ← getEnv
  try
    addDecl <| .thmDecl {name, levelParams := [], type := ty, value := proof}
    unless (← collectAxioms name).all (auditAxioms.contains ·) do
      setEnv saved
      return .unknown "the certificate uses nonstandard axioms"
    pure verdict
  catch e =>
    setEnv saved
    throw e

/-- `#audit_preconditions cspec[C]{f} as checkName`: certify an impossible
entry condition, certify a possible one, or report unknown without a theorem. -/
syntax (name := auditPreconditionsCmd) "#audit_preconditions " term " as " ident : command

@[command_elab auditPreconditionsCmd]
def elabAuditPreconditions : CommandElab := fun stx => do
  let name := (← getCurrNamespace) ++ stx[3].getId
  if (← getEnv).contains name then throwErrorAt stx[3] "declaration already exists: {name}"
  let verdict ← liftTermElabM do
    let φ ← Term.withoutErrToSorry <| Term.elabTerm stx[1] none
    Term.synthesizeSyntheticMVarsNoPostponing
    auditPreconditions (← instantiateMVars φ) name
  match verdict with
  | .impossible => logInfo s!"preconditions: impossible (kernel-checked: {name})"
  | .possible => logInfo s!"preconditions: possible (kernel-checked: {name})"
  | .unknown reason => logInfo s!"preconditions: unknown ({reason})"

end Solidity.Tools
