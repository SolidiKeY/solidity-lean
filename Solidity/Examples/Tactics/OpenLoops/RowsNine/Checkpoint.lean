import Solidity.Examples.Tactics.OpenLoops

/-!
# Module boundaries for the nine-row walk

Each checkpoint exports its remaining sequent and a kernel-checked continuation
lemma. The walk still uses 128-step chunks, the original recursion depth and a
fresh ordinary heartbeat scope per iteration. The three four-iteration prefixes
and final continuation together use at most `Seq.chunkFuel` iterations.
-/
namespace Solidity.Examples.Tactics.OpenLoops.RowsNine.Checkpoint
open Lean Meta Elab Command Tactic

/-- A bounded prefix of the existing chunked walk. Failed rules or closers fail
this command; every unresolved frontier goal is retained. -/
def walkPrefix (root : MVarId) (iterations : Nat) : TacticM (List MVarId) :=
  Seq.withChunkDepth do
    let mut pending := [root]
    for _ in [0:iterations] do
      let some g := pending.head? | break
      pending := pending.tail
      let next ← withCurrHeartbeats do
        let some (C, R, Γ, H, φ) ← Seq.sequent? g
          | throwError "expected a closed sequent"
        let modalFree ← unsafe evalExpr Bool (mkConst ``Bool)
          (mkApp3 (mkConst ``Fml.modalFree) C Γ (← Symex.evaluable φ))
        if modalFree then Seq.closeLeaf g else Seq.chunk g C R Γ H φ 128
      pending := next ++ pending
    return pending

/-- Export four walk iterations and their remaining obligation. Refuse a
branching frontier rather than silently dropping any proof obligation. -/
elab "#rows_nine_checkpoint " name:ident " : " input:term : command =>
    liftTermElabM <| withTheReader Core.Context (fun c =>
      { c with
        maxRecDepth := Seq.chunkRecDepth
        options := maxRecDepth.set c.options Seq.chunkRecDepth }) do
  let ty ← Term.withoutErrToSorry <| Term.elabTerm input none
  let root ← mkFreshExprSyntheticOpaqueMVar (← whnf ty)
  let remaining ← Tactic.run root.mvarId! do
    setGoals (← walkPrefix root.mvarId! 4)
  withCurrHeartbeats do
    let [g] := remaining | throwError "expected one checkpoint obligation"
    let nextTy ← instantiateMVars (← g.getType)
    let nextName := (← getCurrNamespace) ++ name.getId.appendAfter "Goal"
    addDecl <| .defnDecl {
      name := nextName
      levelParams := []
      type := mkSort .zero
      value := nextTy
      hints := .abbrev
      safety := .safe }
    withLocalDeclD `continuation (mkConst nextName) fun h => do
      g.assign h
      let proof ← mkLambdaFVars #[h] (← instantiateMVars root)
      let theoremTy ← instantiateMVars (← mkForallFVars #[h] ty)
      if proof.hasSorry || proof.hasMVar || theoremTy.hasMVar then throwError "incomplete checkpoint"
      addDecl <| .thmDecl {
        name := (← getCurrNamespace) ++ name.getId
        levelParams := []
        type := theoremTy
        value := proof }

/-- Resume after the three prefixes, retaining the original aggregate walk
allowance and all unrelated tactic goals. -/
elab "rows_nine_finish" : tactic => Seq.withChunkDepth do
  let g ← getMainGoal
  let rest := (← getUnsolvedGoals).erase g
  let next ← withCurrHeartbeats do
    let next ← mkFreshExprSyntheticOpaqueMVar (← whnf (← g.getType))
    g.assign next
    pure next.mvarId!
  setGoals ((← walkPrefix next (Seq.chunkFuel - 12)) ++ rest)

end Solidity.Examples.Tactics.OpenLoops.RowsNine.Checkpoint
