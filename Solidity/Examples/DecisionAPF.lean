import Solidity.Examples.DecisionLedger

namespace Solidity.Examples.Decision

open Solidity.Decide

set_option Elab.async false

/-! Array property blocks past their last key and at two depths, over a
`bool` key, past a member, with a guard that may halt, and a positive `∀`
past the prefix (M7, features 16 to 19, 2026-10-26): each former
counterexample proved, a false variant refuted, the coverage
kernel-checked. -/

/-- info: ["proved", "proved", "proved", "proved", "proved", "proved"] -/
#guard_msgs in
#eval [gapColumn, gapTwoPaths, gapBoolKeyed, gapStructValue, gapPartialGuard, gapPositiveForall].map verdict

/-- info: ["refuted", "refuted", "refuted", "refuted", "refuted", "refuted"] -/
#guard_msgs in
#eval [columnBad, twoPathsBad, boolKeyedBad, structValueBad, partialGuardBad, positiveForallBad].map verdict

theorem gapColumn_covered : gapColumn.Covered = true := by decide +kernel
theorem gapTwoPaths_covered : gapTwoPaths.Covered = true := by decide +kernel
theorem gapBoolKeyed_covered : gapBoolKeyed.Covered = true := by decide +kernel
theorem gapStructValue_covered : gapStructValue.Covered = true := by decide +kernel
theorem gapPartialGuard_covered : gapPartialGuard.Covered = true := by decide +kernel
theorem gapPositiveForall_covered : gapPositiveForall.Covered = true := by decide +kernel
theorem columnBad_covered : columnBad.Covered = true := by decide +kernel

theorem gapColumn_answers : decideGoal gapColumn ≠ .unknown := decideGoal_complete gapColumn_covered rfl


end Solidity.Examples.Decision
