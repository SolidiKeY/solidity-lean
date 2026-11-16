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

/-- info: ["proved", "refuted", "proved", "refuted", "proved", "refuted", "proved", "refuted"] -/
#guard_msgs in #eval [negOk, negBad, bnotOk, bnotBad, toIntOk, toIntBad, toUintOk, toUintBad].map verdict

/-- info: ["proved", "refuted", "proved", "refuted", "proved", "proved", "refuted"] -/
#guard_msgs in #eval [divOk, divBad, modOk, modBad, shrOk, shrInt, shrIntBad].map verdict

/-- info: ["proved", "refuted", "proved", "refuted", "proved", "refuted", "proved", "refuted"] -/
#guard_msgs in #eval [shlZero, shlFar, maskOk, maskBad, addWOk, addWBad, subWOk, subWBad].map verdict

-- `x << 4` against `x * 16`: decided by the walk (M7, the running time).
/-- info: "proved" -/
#guard_msgs in #eval verdict shlOk

/-- info: true -/
#guard_msgs in #eval [negOk, negBad, bnotOk, bnotBad, toIntOk, toIntBad, toUintOk, toUintBad, divOk,
  divBad, modOk, modBad, shrOk, shrInt, shrIntBad, shlOk, shlZero, shlFar, maskOk, maskBad, addWOk,
  addWBad, subWOk, subWBad].all Fml.Covered

/-! Kernel-checked coverage, one leaf a feature. -/

theorem neg_covered : negOk.Covered = true := by decide +kernel
theorem bnot_covered : bnotOk.Covered = true := by decide +kernel
theorem toInt_covered : toIntOk.Covered = true := by decide +kernel
theorem toUint_covered : toUintOk.Covered = true := by decide +kernel
theorem div_covered : divOk.Covered = true := by decide +kernel
theorem mod_covered : modOk.Covered = true := by decide +kernel
theorem shr_covered : shrInt.Covered = true := by decide +kernel
theorem shl_covered : shlOk.Covered = true := by decide +kernel
theorem mask_covered : maskOk.Covered = true := by decide +kernel
theorem addW_covered : addWOk.Covered = true := by decide +kernel
theorem subW_covered : subWOk.Covered = true := by decide +kernel

/-- info: ["proved", "refuted", "proved", "proved", "proved", "refuted", "proved", "proved"] -/
#guard_msgs in #eval [kintOk, kintBad, kintWide, kintNeg, kintScale, kintScaleBad, kintValue,
  kintRead].map verdict

/-- info: true -/
#guard_msgs in #eval [kintOk, kintBad, kintWide, kintNeg, kintScale, kintScaleBad, kintValue,
  kintRead].all Fml.Covered

theorem kint_covered : kintOk.Covered = true := by decide +kernel
theorem kintScale_covered : kintScale.Covered = true := by decide +kernel

/-- `decideLeaf_proved_iff`, applied to a KeY `int` leaf. -/
theorem kint_iff : decideLeaf kintOk = .proved ↔ Fml.Valid kintOk :=
  decideLeaf_proved_iff kint_covered

/-- `decideLeaf_proved_iff`, applied to a cut leaf. -/
theorem div_iff : decideLeaf divOk = .proved ↔ Fml.Valid divOk :=
  decideLeaf_proved_iff div_covered

end Solidity.Examples.Decision
