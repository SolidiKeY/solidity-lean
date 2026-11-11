import Solidity.Examples.Decision
import Solidity.Examples.DecisionThreeKindProof

/-! Checks literal arithmetic/bitwise coverage and positive verdict regressions. -/

namespace Solidity.Examples.Decision

open Solidity.Decide

set_option Elab.async false

/-! Operators with a literal operand (M7, 2026-10-25), written by the cut
through the others (`Calculus/QuotientCut.lean`: `bandGo`, `mulWGo`,
`litCutR`): each former counterexample proved, a false variant refuted,
the coverage kernel-checked. -/

/-- info: ["proved", "proved", "proved", "proved", "proved", "proved", "proved"] -/
#guard_msgs in #eval [gapIntDiv, gapIntMod, gapOr, gapXor, gapAnd, gapPow, gapMulW].map verdict

theorem gapIntDiv_covered : gapIntDiv.Covered = true := by decide +kernel
theorem gapIntMod_covered : gapIntMod.Covered = true := by decide +kernel
theorem gapOr_covered : gapOr.Covered = true := by decide +kernel
theorem gapXor_covered : gapXor.Covered = true := by decide +kernel
theorem gapAnd_covered : gapAnd.Covered = true := by decide +kernel
theorem gapPow_covered : gapPow.Covered = true := by decide +kernel
theorem gapMulW_covered : gapMulW.Covered = true := by decide +kernel
theorem andBad_covered : andBad.Covered = true := by decide +kernel
theorem mulWBad_covered : mulWBad.Covered = true := by decide +kernel

theorem gapOr_answers : decideGoal gapOr ≠ .unknown := decideGoal_complete gapOr_covered rfl
theorem gapMulW_iff : decideLeaf gapMulW = .proved ↔ Fml.Valid gapMulW :=
  decideLeaf_proved_iff gapMulW_covered

end Solidity.Examples.Decision
