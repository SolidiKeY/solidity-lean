import Solidity.Examples.DecisionBlocks

namespace Solidity.Examples.Decision

open Solidity.Decide

set_option Elab.async false

/-! The astronomically large refutations: both leaves are in the fragment
and covered by the kernel, so they answer (`decideGoal_complete`).  The
instance the decision refutes is refuted by its arithmetic (computed for
`intTwoSides` below, the instance's state small), and the leaf's refuting
state is that state's mappings or ledger
rebuilt at the floors (`ApfFml.apfInst_refute`): a term whose reads are
proved region by region, the negative region of `2^255` keys for
`intTwoSides` (the positive one holds the default, the largest key's `2`),
one of `2^256 - 6` addresses for `ledgerFar`, which no evaluation builds. -/

theorem intTwoSides_inTarget : intTwoSides.inTarget {} = true := by decide +kernel
theorem ledgerFar_inTarget : ledgerFar.inTarget {} = true := by decide +kernel
theorem intTwoSides_covered : intTwoSides.Covered = true := by decide +kernel
theorem ledgerFar_covered : ledgerFar.Covered = true := by decide +kernel

theorem intTwoSides_answers : decideGoal intTwoSides ≠ .unknown := decideGoal_complete intTwoSides_covered rfl
theorem ledgerFar_answers : decideGoal ledgerFar ≠ .unknown := decideGoal_complete ledgerFar_covered rfl

/-- info: "refuted" -/
#guard_msgs in
#eval match quantReduction? intTwoSides with
  | some q => if q.Qs.isEmpty then (match q.main.verify with | .inl _ => "valid" | .inr _ => "refuted")
    else "quantified"
  | none => "none"
theorem gapPartialGuard_iff : decideLeaf gapPartialGuard = .proved ↔ Fml.Valid gapPartialGuard :=
  decideLeaf_proved_iff gapPartialGuard_covered

/-! Fifty reads (M7, 2026-10-25): the flattener's budget is the leaf's own
(`readBudget`), no longer a fixed 45 reads. -/

theorem gapManyReads_covered : gapManyReads.Covered = true := by decide +kernel

/-- It answers (`decideGoal_complete`); the answer is not computed here: the
walk of `AFml.fastVerify` over 51 variables of 256 bits recurses past the
interpreter's stack (docs/automation.md, M7, "Running time"). -/
theorem gapManyReads_answers : decideGoal gapManyReads ≠ .unknown :=
  decideGoal_complete gapManyReads_covered rfl


end Solidity.Examples.Decision
