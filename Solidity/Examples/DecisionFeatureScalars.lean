import Solidity.Examples.Decision
import Solidity.Tools.Common

/-! Scalar and quantified decision regressions. Guards the original verdict/coverage checks against exceeding the unchanged per-module replay budget. -/

namespace Solidity.Examples.Decision

open Solidity.Decide

set_option Elab.async false

theorem double_covered : double.Covered = true := by decide +kernel

/-- `decideGoal_complete`, applied: no hash, so no premise. -/
theorem double_answers : decideGoal double ≠ .unknown :=
  decideGoal_complete double_covered rfl

theorem nested_covered : nested.Covered = true := by decide +kernel

/-- `decideLeaf_proved_iff`, applied: the verdict is exact. -/
theorem double_iff : decideLeaf double = .proved ↔ Fml.Valid double :=
  decideLeaf_proved_iff double_covered

/-- info: ["proved", "proved", "refuted", "proved"] -/
#guard_msgs in #eval [double, triple, doubleReturns, doubleBalance].map verdict

/-- info: [true, true, true, true] -/
#guard_msgs in #eval [double, triple, doubleReturns, doubleBalance].map Fml.Covered

/-- info: ["proved", "proved", "refuted"] -/
#guard_msgs in #eval [nested, written, writtenBad].map verdict

-- `decideLeaf` on Presburger quantifiers: each verdict exact
-- (`QFml.decide_iff`), each refutation a certified state.
/-- info: ["proved", "refuted", "proved", "proved", "refuted", "proved", "refuted", "proved", "refuted"] -/
#guard_msgs in
#eval [evenHyp, evenHypBad, leastHyp, above, below, evenWrite, oddWrite, evenRead, evenReadBad].map verdict

/-- info: [true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval [evenHyp, evenHypBad, leastHyp, above, below, evenWrite, oddWrite, evenRead, evenReadBad].map Fml.Covered

/-- info: (["proved", "refuted"], [true, true]) -/
#guard_msgs in #eval ([evenGoal, evenGoalBad].map verdict, [evenGoal, evenGoalBad].map Fml.Covered)

/-- A read in a quantifier, hoisted: kernel-checked coverage. -/
theorem evenGoal_covered : evenGoal.Covered = true := by decide +kernel

theorem evenRead_covered : evenRead.Covered = true := by decide +kernel

theorem evenHyp_covered : evenHyp.Covered = true := by decide +kernel

/-- `decideLeaf_complete`, applied to an `∃` in a hypothesis. -/
theorem evenHyp_answers : decideLeaf evenHyp ≠ .unknown := decideLeaf_complete evenHyp_covered

end Solidity.Examples.Decision
