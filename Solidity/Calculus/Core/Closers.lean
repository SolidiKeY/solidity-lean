import Solidity.Calculus.Core.ProveSeq
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.Rewrite

/-!
# Today's closers on a scoped leaf

After `sol_symex` on a scoped goal (`Core.Valid ψ`, `⊨ dl!{ … }` under
`open scoped Solidity.Core.Surface`), a leaf is closed by today's closers on
its erasure, as `sol_close` is (`Calculus/Core/Derive.lean`): each tactic
below has a second elaborator that erases the leaf (`Derive.eraseLeaf`:
`Fml.posB`, checked by the kernel, then `Valid.of_erase`) and runs the same
tactic on today's goal.  Today's macro is tried first and fails on a scoped
goal; on today's goal the second elaborator steps aside.  `sol_spec_prep`'s
is `Calculus/Core/SolSpec.lean`'s.
-/

namespace Solidity.Core

open Lean Elab Tactic

@[tactic Solidity.tacticSol_close_mt]
def evalSolCloseMtCore : Tactic := fun stx => Derive.onErased "sol_close_mt" stx stx

@[tactic Solidity.tacticSol_close_eval]
def evalSolCloseEvalCore : Tactic := fun stx => Derive.onErased "sol_close_eval" stx stx

@[tactic Solidity.tacticSol_close_unwrap]
def evalSolCloseUnwrapCore : Tactic := fun stx => Derive.onErased "sol_close_unwrap" stx stx

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

/-! ## A scoped formula refuted at a state

`¬ ⊨ dl!{ … }` by one state where the run panics, or halts under the
diamond: the run's outcome read by the kernel (`decide +kernel` on
`isPanic`/`isHalt`), as today's refutations read it by `rfl`. -/

/-- The outcome is a panic. -/
def _root_.Solidity.Semantics.Res.isPanic {α : Type} : Semantics.Res α → Bool
  | .error .panic => true
  | _ => false

/-- The outcome is a halt (a revert or a panic). -/
def _root_.Solidity.Semantics.Res.isHalt {α : Type} : Semantics.Res α → Bool
  | .error _ => true
  | .ok _ => false

/-- No modality holds of a run that panics. -/
theorem _root_.Solidity.Modality.afterRunC_not_panic {α : Type} {m : Modality} {p : α → Prop}
    {r : Semantics.Res α} (h : m.afterRunC p r) (hp : r.isPanic = true) : False := by
  cases r with
  | ok _ => cases hp
  | error e => cases e <;> first | exact h.2 rfl | cases hp

/-- The diamond does not hold of a run that halts. -/
theorem _root_.Solidity.Modality.afterRunC_diamond_halt {α : Type} {p : α → Prop}
    {r : Semantics.Res α} (h : Modality.diamond.afterRunC p r) (hp : r.isHalt = true) : False := by
  cases r with
  | ok _ => cases hp
  | error _ => exact h.1

end Solidity.Core
