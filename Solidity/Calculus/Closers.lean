import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.WalkSyntax
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.Rewrite
import Solidity.Calculus.UpdRuleScoped

/-!
# The closers on a scoped leaf

After `sol_symex` on a scoped goal (`Valid ψ`, `⊨ dl!{ … }`), or `sol_leaf`
on a leaf `sol_prove` left, a leaf is closed on its scoped form:
`sol_close`, `sol_close_mt` and `sol_spec_close` read it through
`sol_close_unwrap` (`CloseS.valid_of_holdsE`, `Calculus/CloseScoped.lean`),
with no erasure.  `sol_close_eval` on the bare leaf `Valid ψ`, before its
state is introduced, takes the same first step here.  `sol_decide`'s parts
reduce the scoped leaf by position (below).  `sol_apply_upd` and
`sol_fold_terms` have no scoped reading yet: their second elaborator erases
the leaf (`Derive.eraseLeaf`: `Fml.posB`, checked by the kernel, then
`Valid.of_erase`) and runs the same tactic on today's goal.  Today's macro
is tried first and fails on a scoped goal; on today's goal the second
elaborator steps aside.  `sol_upd` and `sol_merge` rewrite the scoped
formula itself (M6c, W7 `w7-rewrites`): `Calculus/UpdRuleScoped.lean`'s
rules, the leaf staying scoped.  `sol_prove?` runs the scoped `sol_prove`
and the scoped leaf search after it.
-/

namespace Solidity

open Lean Elab Tactic

/-- `sol_close_eval` on a bare scoped leaf `Valid ψ`: the leaf as `holdsE`
reads it (`sol_close_unwrap`), its state introduced, then the scoped step
(`Calculus/CloseScoped.lean`). -/
@[tactic Solidity.tacticSol_close_eval]
def evalSolCloseEvalCore : Tactic := fun _ => withMainContext do
  let some _ ← Symex.validGoal? (← getMainGoal) | throwUnsupportedSyntax
  evalTactic (← `(tactic| (sol_close_unwrap; intro σ; sol_close_eval)))

/-! ## `sol_decide`'s parts on a scoped goal (decision 80)

Each part on a scoped leaf `Valid ψ` reduces the leaf by position
(`Decide.reduceScoped`, `Valid.of_reduceS`; with a premise `wt(storage)`,
`Valid.of_reduceSL`, its layout then set aside), computes the reduction
(`sol_reduce`) and takes the step it names on it: the constraints with the
parameters typed (`sol_decide_cons`, `sol_decide_typed`'s step; `sol_reads`
its first part), or the finish without them, the parameters free
(`sol_decide_heuristic`, `sol_decide_unconstrained`).  On today's goal
each steps aside for today's macro. -/

open Meta in
/-- A part of `sol_decide` on a scoped goal: the leaf reduced by position,
the reduction computed, then `rest`. -/
def Decide.onReduced (layout : Bool) (rest : Option (TacticM Unit)) : Tactic := fun _ =>
  withMainContext do
    let g ← getMainGoal
    let some (C, ψ) ← Symex.validGoal? g | throwUnsupportedSyntax
    Symex.reporting g do
      let (g', hasLayout) ← Decide.reduceScoped g C ψ
      replaceMainGoal [g']
      evalTactic (← `(tactic| sol_reduce))
      if hasLayout && !layout then
        evalTactic (← `(tactic| refine Decide.LFml.forall_layout ?_))
      if let some k := rest then withMainContext k

@[tactic Solidity.Decide.tacticSol_decide_heuristic]
def evalSolDecideHeuristicCore : Tactic := Decide.onReduced false <| some do
  evalTactic (← `(tactic| (sol_decide_body; sol_decide_heuristic)))

@[tactic Solidity.Decide.tacticSol_decide_cons]
def evalSolDecideConsCore : Tactic := Decide.onReduced false <| some do
  evalTactic (← `(tactic| sol_decide_typed))

@[tactic Solidity.Decide.tacticSol_decide_unconstrained]
def evalSolDecideUnconstrainedCore : Tactic := Decide.onReduced false <| some do
  evalTactic (← `(tactic| (sol_decide_body; sol_decide_heuristic)))

@[tactic Solidity.Decide.tacticSol_reduce]
def evalSolReduceCore : Tactic := Decide.onReduced true none

@[tactic Solidity.Decide.tacticSol_reads]
def evalSolReadsCore : Tactic := Decide.onReduced false <| some do
  replaceMainGoal [← Decide.typedCons (← getMainGoal)]
  evalTactic (← `(tactic| sol_reads))

@[tactic Solidity.tacticSol_apply_upd]
def evalSolApplyUpdCore : Tactic := fun stx => Derive.onErased "sol_apply_upd" stx stx

open Meta in
/-- `sol_merge` on a scoped goal: every stack of updates merged and cleaned
on the scoped formula itself (`Fml.simpUpdsS`, `Valid.of_simpUpdsS`). -/
@[tactic Solidity.tacticSol_merge]
def evalSolMergeCore : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let some (C, _) ← Symex.validGoal? g | throwUnsupportedSyntax
  Symex.reporting g do
    replaceMainGoal [← Symex.applyValid "sol_merge" g (mkApp (mkConst ``Valid.of_simpUpdsS) C)]

@[tactic Solidity.tacticSol_fold_terms]
def evalSolFoldTermsCore : Tactic := fun stx => Derive.onErased "sol_fold_terms" stx stx

open Meta in
/-- `sol_upd r` on a scoped goal: the update rule `r` (`UpdRuleNameS`) at
the first update where it fits, on the scoped formula itself
(`Fml.updAtS`, `Valid.of_updAtSD`). -/
@[tactic Solidity.tacticSol_upd_]
def evalSolUpdCore : Tactic := fun stx => withMainContext do
  let g ← getMainGoal
  let some (C, _) ← Symex.validGoal? g | throwUnsupportedSyntax
  Symex.reporting g do
    let r ← Term.elabTermEnsuringType stx[1] (mkConst ``UpdRuleNameS)
    Term.synthesizeSyntheticMVarsNoPostponing
    let r ← instantiateMVars r
    replaceMainGoal [← Symex.applyValid "sol_upd" g (mkApp2 (mkConst ``Valid.of_updAtSD) C r)
      (some m!"rule {stx[1]} does not apply here")]

/-! ## `sol_prove?` on a scoped goal

The scoped `sol_prove` (`Valid φ` and `⊢ φ`, `Calculus/ProvesDerive.lean`),
then each leaf it leaves (a scoped sequent, `sol_leaf` its first line),
closed by the first of the scoped leaf tactics (`Derive.searchLeaf`,
`Derive.leafTacs`, its bounds read on the scoped leaf, `Seq.goalFits`); the
replay suggested as today's (`Derive.replayLines`). -/

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
    match ← NFml.Derive.searchLeaf l Seq.goalFits with
    | some (t, h) =>
      found := found ++ [(name, t)]
      hb := hb + h
    | none =>
      open_ := open_ ++ [l]
      found := found ++ [(name, #["sorry"])]
  if let some l := open_.head? then
    logInfo m!"sol_prove?: no tactic closes {← l.getTag}:{indentExpr (← l.getType)}"
  else unless ← Derive.replayFits hb do
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
