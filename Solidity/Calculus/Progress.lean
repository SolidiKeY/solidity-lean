import Solidity.Calculus.MultiStep
import Solidity.Calculus.Coverage
import Solidity.Calculus.JudgmentSplit

/-!
# Progress fails, and exactly where

The calculus is **not** total: a symbolic `if` — `if (flag) …` with
a plain stack-bool condition, precisely the statement `ternaryToIf`
produces from `x = flag ? 1 : 2` — is covered by no rule of the calculus, has no
`RuleStep` under any block modality, and so the rewrite calculus does not
normalize every block.  This module proves those three negative facts and
records how the symbolic `if` is really handled: not by a rewrite rule (a
single-residual rule cannot exist, since execution branches on the state)
but by the judgment-layer split `SolidityJudgment.ite_split_pure`.

There is no catch-all tier.  An earlier version of this file "proved"
strong progress by adding two fallback rules whose residual deleted any
uncovered statement; that made progress and normalization true and
meaningless.  What *is* true is the characterization in `Coverage.lean`:
a well-typed statement is either covered or one of the 24 listed
`ResidueShape`s (`Coverage.coverage_residue`,
`Coverage.not_covered_iff_residue`), and the completeness theorem is
stated over that fragment (`RuleStep.complete_of_wellTyped`).

`BlockStep.wellFounded` (termination of rewriting) remains the open
certificate of `Termination.lean`.

The interpreter has its own version of this question, and its own list:
the calculus's residue is `Coverage.ResidueShape`, the interpreter's is
`StuckShape.StuckCause`.
-/

namespace Solidity

open Rules

/-- `if (flag) { i = 1 } else { i = 2 }`: a symbolic stack-bool condition,
the very shape `ternaryToIf` produces from `x = flag ? 1 : 2`. -/
def symbolicIte : Stmt :=
  sstmt!{ if (flag) { i = 1 } else { i = 2 } }

/-- It is listed residue: the condition is simple but not a literal. -/
theorem symbolicIte_residue : Coverage.ResidueShape symbolicIte :=
  Coverage.ResidueShape.iteSymbolicCond _ _ _ rfl rfl

/-- No rule of the calculus covers it, under either modality. -/
theorem symbolicIte_not_covered (m : Modality) :
    ¬ Rules.ruleApplies m symbolicIte :=
  Coverage.residue_not_covered symbolicIte_residue

/-- **Coverage is not total.** -/
theorem rules_not_total (m : Modality) :
    ¬ ∀ lhs : Stmt, Rules.ruleApplies m lhs :=
  fun h => symbolicIte_not_covered m (h _)

/-- The symbolic `if` has no rule step under any block modality
(`.both` included: every step is a rule of the calculus whose condition holds,
`RuleStep.ruleApplies_of_ruleStep`). -/
theorem symbolicIte_no_step (sm : SolidityModality) :
    ¬ ∃ cond rhs, RuleStep sm symbolicIte cond rhs :=
  fun ⟨_, _, h⟩ =>
    let ⟨m, hm⟩ := RuleStep.ruleApplies_of_ruleStep h
    symbolicIte_not_covered m hm

/-- **Progress fails**: it is not the case that every statement has an
applicable rule under every modality. -/
theorem not_progress :
    ¬ ∀ (sm : SolidityModality) (lhs : Stmt),
        ∃ cond rhs, cond ∧ RuleStep sm lhs cond rhs :=
  fun h =>
    let ⟨cond, rhs, _, hstep⟩ := h .box symbolicIte
    symbolicIte_no_step .box ⟨cond, rhs, hstep⟩

/-- **Normalization fails**: the block `[symbolicIte]` never reaches an
empty block — it cannot take a single step. -/
theorem not_normalizing :
    ¬ ∀ sb : SolidityBlock, ∃ nf, (sb —↠ nf) ∧ nf.stmts = [] := by
  intro h
  obtain ⟨nf, hsteps, hnil⟩ := h ⟨.box, [symbolicIte]⟩
  cases hsteps with
  | refl => exact absurd hnil (by simp)
  | step hstep _ =>
      cases hstep with
      | head hrule => exact symbolicIte_no_step _ ⟨_, _, hrule⟩

/-- How the symbolic `if` is handled: at the judgment layer.  A pure
condition evaluates without touching the state, and the judgment on the
`if` is equivalent to the conjunction of the judgments on the two
branches, each guarded by the value of the condition. -/
theorem symbolicIte_judgment_split
    {m : SolidityModality} {post : WrappedExpr}
    {s0 t : Semantics.State} {b : Bool}
    (heval : Semantics.evalValue s0 (sexpr!{ flag }) = .ok (t, .bool b)) :
    (SolidityJudgment.mk ⟨m, [symbolicIte]⟩ post).Holds s0 ↔
      ((b = true ->
          (SolidityJudgment.mk ⟨m, [sstmt!{ i = 1 }]⟩ post).Holds s0) ∧
        (b = false ->
          (SolidityJudgment.mk ⟨m, [sstmt!{ i = 2 }]⟩ post).Holds s0)) :=
  SolidityJudgment.ite_split_pure (rest := []) rfl heval

/-- **Strong termination** (open, believed true): the step relation admits
no infinite reduction sequence.  Not refutable by any known
counterexample — the statement grammar has no loop construct, the
function table used by `functionBodyExpand` is acyclic (`blockCallFree`
lock-ins), and every capture/lowering rule strictly decreases a natural
measure — but proving it requires the concrete measure `Termination.lean`
intentionally leaves open: a `RewriteTerminationCertificate` whose
`decreases` field needs a per-rule decrease lemma for each generated
rule, with `Stmt.callStmt` weighted by `1 + weight (expandCall …)` over
the acyclic call table.  That certificate is a substantial standalone
development, not attempted here. -/
theorem BlockStep.wellFounded :
    WellFounded (fun after before : SolidityBlock => BlockStep before after) := by
  -- Open: supply the concrete `RewriteTerminationCertificate` (see
  -- Termination.lean's design note) and conclude via
  -- `RewriteTerminationCertificate.wellFounded`.
  sorry

end Solidity
