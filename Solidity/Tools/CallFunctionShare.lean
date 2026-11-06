import Solidity.Tools.ProofTree
import Solidity.Calculus.Closers
import Solidity.Calculus.CloseCallSharing
import Solidity.Calculus.CallFunctionLeafMetrics

/-! # Explicit checked sharing API and source/walk/leaf measurements -/
namespace Solidity.Tools.CallFunctionShare
open Lean Elab Tactic Meta

-- Preserve the committed explicit consumer API while the implementation
-- lives below the aggregate closer, without an import of Tools from core.
def qUpdate {C : Contract} (Γ Δ : Ctx) (m : Modality) (U : Upd C Γ Δ)
    (φ : Fml C Δ) (qφ : Expr) : QM Expr := CloseCallSharing.qUpdate Γ Δ m U φ qφ

def qTransform {C : Contract} (Γ : Ctx) (φ : Fml C Γ) : QM Expr :=
  CloseCallSharing.qTransform Γ φ

def quoteTransform {C : Contract} (c : Expr) {Γ : Ctx} (φ : Fml C Γ) : Expr × Bool :=
  CloseCallSharing.quoteTransform c φ

def share (g : MVarId) : TacticM MVarId := CloseCallSharing.share g
def affineStep (g : MVarId) : TacticM MVarId := CloseCallSharing.affineStep g
def comparisonFacts (g : MVarId) : MetaM MVarId := CloseCallSharing.comparisonFacts g
def close : TacticM Unit := CloseCallSharing.close

/-- Source-boundary measurement only: actual original walk and both actual
whole leaves. Does not assert that either leaf closes. -/
syntax "#proof_share_size " term : command
open Lean Elab Command Meta in
@[command_elab Solidity.Tools.CallFunctionShare.«command#proof_share_size_»]
def elabShareSize : CommandElab := fun stx => liftTermElabM do
  let some tree ← Term.withoutErrToSorry <| Tools.coreProofTree? ⟨stx[1]⟩
    | Tools.notScoped "#proof_share_size"
  let mut oldBig := 0
  let mut newBig := 0
  for l in Tools.treeLeaves tree do
    let seq ← instantiateMVars l.sequent
    if seq.hasSorry || seq.hasMVar || seq.hasFVar then
      throwError "#proof_share_size: incomplete or open sequent"
    let g ← mkFreshExprSyntheticOpaqueMVar seq
    let gs ← Tactic.run g.mvarId! (Tactic.withoutRecover <| evalTactic (← `(tactic| sol_leaf)))
    let [g'] := gs | throwError "#proof_share_size: unexpected leaf goals"
    let some (_, φ) ← Symex.validGoal? g' | throwError "#proof_share_size: expected validity"
    let ψ ← mkAppM ``CallFunctionTransform.transform #[φ]
    let oldN ← unsafe evalExpr Nat (mkConst ``Nat) (← mkAppM ``Fml.tmSize #[φ])
    let newN ← unsafe evalExpr Nat (mkConst ``Nat) (← mkAppM ``Fml.tmSize #[ψ])
    oldBig := max oldBig oldN
    newBig := max newBig newN
  logInfo m!"{tree.rows.size} node(s), {tree.leaves} branch(es), {tree.openGoals.size} original open, old largest leaf {oldBig}, shared largest leaf {newBig} term node(s)"
end Solidity.Tools.CallFunctionShare
