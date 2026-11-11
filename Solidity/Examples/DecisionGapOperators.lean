import Solidity.Examples.DecisionGapLiteralChecks
import Solidity.Examples.DecisionGapModularChecks
import Solidity.Examples.DecisionThreeKindProof

/-!
# The closer's decision (M7): literal operators and hash kinds over `Gaps`

Operators with a literal operand written by the cut (features of
2026-10-25 and feature 22) and the three hash kinds (features 27 to 29). The formulas live in `Examples/Decision.lean`. The proposed split aims to
keep every module within the unchanged 300-second replay budget.
-/

namespace Solidity.Examples.Decision

open Solidity.Decide

-- The verdicts run one after another: run in parallel, their evaluations
-- together overflow a command-line `lean`'s stack (exit 135).
set_option Elab.async false

/-! Three kinds (feature 28, `Fml.tk3`), a second kind hashing one string
with no hash of the first (feature 27) and several such strings (feature
29): the former counterexamples covered, by the kernel, so answered;
`gapThreeKinds` proved, `gapMixedKinds` and `gapMixedPairs` refuted (their
variants in `Examples/DecisionHashes.lean`). -/

theorem gapMixedKinds_covered : gapMixedKinds.hashCovered = true := by decide +kernel
theorem gapThreeKinds_answers : decideGoal gapThreeKinds ≠ .unknown :=
  decideGoal_complete_hash gapThreeKinds_covered
theorem gapMixedKinds_answers : decideGoal gapMixedKinds ≠ .unknown :=
  decideGoal_complete_hash gapMixedKinds_covered
theorem gapMixedPairs_covered : gapMixedPairs.hashCovered = true := by decide +kernel
theorem gapMixedPairs_answers : decideGoal gapMixedPairs ≠ .unknown :=
  decideGoal_complete_hash gapMixedPairs_covered

/-- info: ["proved", "refuted", "refuted"] -/
#guard_msgs in
#eval [verdict gapThreeKinds, verdict gapMixedKinds, verdict gapMixedPairs]

end Solidity.Examples.Decision
