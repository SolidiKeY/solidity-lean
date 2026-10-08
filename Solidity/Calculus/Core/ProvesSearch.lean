import Solidity.Calculus.Core.ProvesDerive
import Solidity.Calculus.Derive

/-!
# `sol_prove?` on a scoped sequent

`sol_prove?` on `H ⊢ φ` (`Core.Proves C R [] H φ`, `⊢ φ` under `open scoped
Solidity.Core.Surface`): the scoped `sol_prove` (`Seq.prove`,
`Calculus/Core/ProvesDerive.lean`), then on each leaf it leaves, a goal of
today's calculus, the tries of today's `sol_prove?` (`Derive.searchLeaf`,
`Calculus/Derive.lean`).  The suggestion is the same replay
(`Derive.replayLines`): `sol_prove`, and each leaf's lines.
-/

namespace Solidity.Core.Seq

open Lean Elab Tactic Meta

/-- The scoped `sol_prove` on `g`, then `Derive.searchLeaf` on each leaf it
leaves, the open ones left as goals: today's `Derive.proveSearch` over
`Seq.prove`. -/
def proveSearch (g : MVarId) (C R Γ H φ : Expr) : TacticM Derive.Search := do
  let h0 ← IO.getNumHeartbeats
  let leaves ← prove g C R Γ H φ
  let mut hb : Nat := (← IO.getNumHeartbeats) - h0
  let mut found : List (Lean.Name × Array String) := []
  let mut open_ : List MVarId := []
  for l in leaves do
    let name ← l.getTag
    match ← Derive.searchLeaf l with
    | some (t, h) =>
      found := found ++ [(name, t)]
      hb := hb + h
    | none =>
      open_ := open_ ++ [l]
      found := found ++ [(name, #["sorry"])]
  return { found, open_, heartbeats := hb }

/-- `sol_prove?` on a scoped sequent `H ⊢ φ`: `proveSearch`, the replay
suggested as today's `sol_prove?` suggests it. -/
@[tactic Solidity.«tacticSol_prove?»]
def evalSolProveSeqSearch : Tactic := fun stx => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let_expr Core.Proves C R Γ₀ Γ H φ := ty | throwUnsupportedSyntax
  unless (← whnfR Γ₀).isAppOf ``List.nil do throwUnsupportedSyntax
  let rest := (← getUnsolvedGoals).erase g
  -- an error is this elaborator's, logged (`Symex.reporting`): thrown, it
  -- would hand the goal on to today's `sol_prove?`, which reports its own
  Symex.reporting g do
    let s ← proveSearch g C R Γ H φ
    if let some l := s.open_.head? then
      logInfo m!"sol_prove?: no tactic closes {← l.getTag}:{indentExpr (← l.getType)}"
    else unless ← Derive.replayFits s.heartbeats do
      logWarning m!"sol_prove?: the replay needs about {s.heartbeats / 1000} heartbeats in one \
        declaration, past `maxHeartbeats`"
    setGoals (s.open_ ++ rest)
    ProofTree.suggest stx[0] (Derive.replayLines s.found)

end Solidity.Core.Seq
