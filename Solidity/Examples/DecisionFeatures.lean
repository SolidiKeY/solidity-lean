import Solidity.Examples.DecisionFeatureScalars
import Solidity.Examples.DecisionFeatureMappings
import Solidity.Tools.Common

/-!
# The closer's decision (M7): the features on `Bank` and `Allow`

Coverage, exactness and the pinned verdicts of the features M7 added to
the fragment, the array property blocks and `sortedLe`'s certified replay. Split from `Examples/Decision.lean`, which defines the formulas, so
that each piece builds well under 300 s.
-/

namespace Solidity.Examples.Decision

open Solidity.Decide

-- The verdicts run one after another: run in parallel, their evaluations
-- together overflow a command-line `lean`'s stack (exit 135).
set_option Elab.async false

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

/-- info: ["proved", "proved", "refuted", "refuted", "proved", "proved", "proved"] -/
#guard_msgs in #eval [netOk, netSame, netNeg, netOther, netStore, netWrite, netDistinct].map verdict

/-- info: true -/
#guard_msgs in #eval [netOk, netSame, netNeg, netOther, netStore, netWrite, netDistinct].all Fml.Covered

-- Four ledger reads: decided by the walk (M7, the running time).
/-- info: "proved" -/
#guard_msgs in #eval verdict netSwap

theorem net_covered : netOk.Covered = true := by decide +kernel
theorem netSame_covered : netSame.Covered = true := by decide +kernel
theorem netSwap_covered : netSwap.Covered = true := by decide +kernel

/-- `decideLeaf_proved_iff`, applied to a leaf that reads the ledger. -/
theorem net_iff : decideLeaf netOk = .proved ↔ Fml.Valid netOk :=
  decideLeaf_proved_iff net_covered

/-- `decideLeaf_proved_iff`, applied to a cut leaf. -/
theorem div_iff : decideLeaf divOk = .proved ↔ Fml.Valid divOk :=
  decideLeaf_proved_iff div_covered

/-- info: [false, false, true, true] -/
#guard_msgs in #eval [gridApf, strictSorted, sortedLe, columnApf].map (Fml.inTarget {})

/-- A two-variable block over a root: covered (nine instances, nineteen
reads), decided by the walk (`docs/automation.md`, M7). -/
theorem sortedLe_covered : sortedLe.Covered = true := by
  -- The quantified branch suffices. Reducing the earlier exact-fragment
  -- recognizer first duplicates the nineteen-read expansion in the kernel.
  have cover (φ : Fml Allow []) (h : φ.quantCovered = true) : φ.Covered = true := by
    simp only [Fml.Covered, Fml.CoveredA, h, Bool.or_true, Bool.true_or]
  exact cover sortedLe (by decide +kernel)

/-- The sorted-mapping premise instantiated at keys `2` and `5`. -/
theorem sortedLe_valid : Fml.Valid sortedLe := by
  intro σ h
  exact h (PrimTy.ofIntD .uint 2) (PrimTy.ofIntD .uint 5) rfl

/-- The original decision function's exact verdict, without repeating its
expensive binary-derivative search at every library build. -/
theorem sortedLe_decision : decideGoal sortedLe = .proved := by
  have noHash (φ : Fml Allow []) (hh : φ.hasHash = false)
      (h : decideLeaf φ = .proved) : decideGoal φ = .proved := by
    simp only [decideGoal, hh, Bool.false_eq_true, if_false]
    exact h
  exact noHash sortedLe rfl
    ((decideLeaf_proved_iff (φ := sortedLe) sortedLe_covered).mpr sortedLe_valid)

/-- A cheap output replay carrying equality to the original compiled verdict.
The certificate is checked by the kernel; no expected result is assumed. -/
private def sortedLeReplay : {s : String // s = verdict sortedLe} :=
  have spell (φ : Fml Allow []) (h : decideGoal φ = .proved) : "proved" = verdict φ := by
    simp only [verdict, h]
  ⟨"proved", spell sortedLe sortedLe_decision⟩

/-- info: "proved" -/
#guard_msgs in #eval sortedLeReplay.val

/-- The certified decision cannot replay the opposite verdict. -/
theorem sortedLe_not_refuted : verdict sortedLe ≠ "refuted" := by
  intro h
  have wrong : ("proved" : String) = "refuted" := sortedLeReplay.property.trans h
  exact (by decide +kernel : ("proved" : String) ≠ "refuted") wrong

end Solidity.Examples.Decision
