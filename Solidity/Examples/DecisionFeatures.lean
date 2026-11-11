import Solidity.Examples.DecisionFeatureScalars
import Solidity.Examples.DecisionFeatureMappings
import Solidity.Tools.Common

/-!
# The closer's decision (M7): the features on `Bank` and `Allow`

Coverage, exactness and pinned verdicts are preserved across the scalar and
mapping pieces imported here. This entrypoint retains `sortedLe`'s certified
replay and exposes every original public declaration. The split aims to keep
each module within the unchanged 300-second replay budget.
-/

namespace Solidity.Examples.Decision

open Solidity.Decide

-- The verdicts run one after another: run in parallel, their evaluations
-- together overflow a command-line `lean`'s stack (exit 135).
set_option Elab.async false

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
