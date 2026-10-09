import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.WalkSyntax
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.Rewrite

/-!
# Today's closers on a scoped leaf

After `sol_symex` on a scoped goal (`Valid ψ`, `⊨ dl!{ … }` under
`open scoped Solidity.Scoped`), a leaf is closed by today's closers on
its erasure, as `sol_close` and `sol_close_mt` are through their first
step, `sol_close_unwrap` (`Calculus/Derive.lean`): each tactic below
has a second elaborator that erases the leaf (`Derive.eraseLeaf`:
`Fml.posB`, checked by the kernel, then `Valid.of_erase`) and runs the same
tactic on today's goal.  Today's macro is tried first and fails on a scoped
goal; on today's goal the second elaborator steps aside.  `sol_spec_prep`'s
is `Calculus/SolSpec.lean`'s.  `sol_prove?` runs the scoped `sol_prove`
and today's leaf search after it.
-/

namespace Solidity

open Lean Elab Tactic

@[tactic Solidity.tacticSol_close_eval]
def evalSolCloseEvalCore : Tactic := fun stx => Derive.onErased "sol_close_eval" stx stx

@[tactic Solidity.Decide.tacticSol_decide]
def evalSolDecideCore : Tactic := fun stx => Derive.onErased "sol_decide" stx stx

@[tactic Solidity.Decide.tacticSol_decide_heuristic]
def evalSolDecideHeuristicCore : Tactic := fun stx =>
  Derive.onErased "sol_decide_heuristic" stx stx

@[tactic Solidity.Decide.tacticSol_decide_cons]
def evalSolDecideConsCore : Tactic := fun stx => Derive.onErased "sol_decide_cons" stx stx

@[tactic Solidity.Decide.tacticSol_decide_unconstrained]
def evalSolDecideUnconstrainedCore : Tactic := fun stx =>
  Derive.onErased "sol_decide_unconstrained" stx stx

@[tactic Solidity.Decide.tacticSol_reduce]
def evalSolReduceCore : Tactic := fun stx => Derive.onErased "sol_reduce" stx stx

@[tactic Solidity.Decide.tacticSol_reads]
def evalSolReadsCore : Tactic := fun stx => Derive.onErased "sol_reads" stx stx

@[tactic Solidity.tacticSol_apply_upd]
def evalSolApplyUpdCore : Tactic := fun stx => Derive.onErased "sol_apply_upd" stx stx

@[tactic Solidity.tacticSol_merge]
def evalSolMergeCore : Tactic := fun stx => Derive.onErased "sol_merge" stx stx

@[tactic Solidity.tacticSol_fold_terms]
def evalSolFoldTermsCore : Tactic := fun stx => Derive.onErased "sol_fold_terms" stx stx

@[tactic Solidity.tacticSol_upd_]
def evalSolUpdCore : Tactic := fun stx => Derive.onErased "sol_upd" stx stx

/-! ## `sol_prove?` on a scoped goal

The scoped `sol_prove` (`Valid φ`, `Calculus/Derive.lean`; `⊢ φ`,
`Calculus/ProvesDerive.lean`), then each leaf it leaves, a sequent of
today's calculus, closed by the first of today's leaf tactics
(`Derive.searchLeaf`); the replay suggested as today's (`Derive.replayLines`). -/

open Meta in
/-- `sol_prove?` on a scoped goal; on today's goal it steps aside. -/
@[tactic Solidity.tacticSol_prove?]
def evalSolProveQCore : Tactic := fun stx => withMainContext do
  let g ← getMainGoal
  unless ← Walk.isCoreGoal g do throwUnsupportedSyntax
  let rest := (← getUnsolvedGoals).erase g
  let h0 ← IO.getNumHeartbeats
  setGoals [g]
  evalTactic (← `(tactic| sol_prove))
  let leaves ← getUnsolvedGoals
  let mut hb : Nat := (← IO.getNumHeartbeats) - h0
  let mut found : List (Lean.Name × Array String) := []
  let mut open_ : List MVarId := []
  for l in leaves do
    let name ← l.getTag
    match ← NFml.Derive.searchLeaf l with
    | some (t, h) =>
      found := found ++ [(name, t)]
      hb := hb + h
    | none =>
      open_ := open_ ++ [l]
      found := found ++ [(name, #["sorry"])]
  if let some l := open_.head? then
    logInfo m!"sol_prove?: no tactic closes {← l.getTag}:{indentExpr (← l.getType)}"
  else unless ← NFml.Derive.replayFits hb do
    logWarning m!"sol_prove?: the replay needs about {hb / 1000} heartbeats in one \
      declaration, past `maxHeartbeats`"
  setGoals (open_ ++ rest)
  ProofTree.suggest stx[0] (NFml.Derive.replayLines found)

/-! ## A scoped formula refuted at a state

`¬ ⊨ dl!{ … }` by one typed state where the run panics, or fails under the
diamond: the typed run's outcome read by the kernel (`decide +kernel` on
`TRes.isPanic`/`TRes.isFail`), as today's refutations read it by `rfl`.  A
run exhausted (a push at the bound) is no failure: both modalities accept
it (decision 15). -/

/-- The typed outcome is a panic. -/
def TRes.isPanic {α : Type} : TRes α → Bool
  | .error .panic => true
  | _ => false

/-- The typed outcome is one the diamond refuses: a revert, a panic, a
divergence. -/
def TRes.isFail {α : Type} : TRes α → Bool
  | .error .exhausted => false
  | .error _ => true
  | .ok _ => false

/-- No modality holds of a run that panics. -/
theorem _root_.Solidity.Modality.afterRunTR_not_panic {α : Type} {m : Modality} {p : α → Prop}
    {r : TRes α} (h : m.afterRunTR p r) (hp : r.isPanic = true) : False := by
  cases r with
  | ok _ => cases hp
  | error e => cases e <;> first | exact h.2 rfl | cases hp

/-- The diamond does not hold of a run that fails. -/
theorem _root_.Solidity.Modality.afterRunTR_diamond_fail {α : Type} {p : α → Prop}
    {r : TRes α} (h : Modality.diamond.afterRunTR p r) (hp : r.isFail = true) : False := by
  cases r with
  | ok _ => cases hp
  | error e =>
    cases e with
    | exhausted => cases hp
    | _ => exact absurd h.1 nofun

end Solidity
