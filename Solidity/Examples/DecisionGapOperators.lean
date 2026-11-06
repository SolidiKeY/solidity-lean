import Solidity.Examples.Decision
import Solidity.Examples.DecisionThreeKindProof

/-!
# The closer's decision (M7): literal operators and hash kinds over `Gaps`

Operators with a literal operand written by the cut (features of
2026-10-25 and feature 22) and the three hash kinds (features 27 to 29). Split from `Examples/Decision.lean`, which defines the formulas, so
that each piece builds well under 300 s.
-/

namespace Solidity.Examples.Decision

open Solidity.Decide

-- The verdicts run one after another: run in parallel, their evaluations
-- together overflow a command-line `lean`'s stack (exit 135).
set_option Elab.async false

/-! Operators with a literal operand (M7, 2026-10-25), written by the cut
through the others (`Calculus/QuotientCut.lean`: `bandGo`, `mulWGo`,
`litCutR`): each former counterexample proved, a false variant refuted,
the coverage kernel-checked. -/

/-- info: ["proved", "proved", "proved", "proved", "proved", "proved", "proved"] -/
#guard_msgs in #eval [gapIntDiv, gapIntMod, gapOr, gapXor, gapAnd, gapPow, gapMulW].map verdict

/-- info: ["refuted", "refuted", "refuted", "refuted", "refuted", "refuted", "refuted"] -/
#guard_msgs in #eval [intDivBad, intModBad, orBad, xorBad, andBad, powBad, mulWBad].map verdict

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

/-! Feature 22 (2026-10-26): `&`, `|`, `^` at `int` with a literal, through
the words (`intBit`: `int(uint(x) ⊙ word(c))`), and `addmod`/`mulmod` at a
literal modulus, each sum modulo `c` one atom defined by cases (`amodDef`,
`addmodLit`, `mulmodLit`): the two former counterexamples and their
variants covered, by the kernel, so answered (`decideLeaf_complete`).  Only
`intOr`'s verdict is evaluated here: the others take minutes each
in the interpreter (the arithmetic over the conversion and remainder atoms;
`gapIntAnd` 886 s, `mulmodLt` 741 s), proved for `gapIntAnd`, `gapAddmod`,
`mulmodLt` and refuted for the `*Bad` variants and `addmodZero` when run. -/

/-- info: "proved" -/
#guard_msgs in #eval verdict intOr

theorem gapIntAnd_covered : gapIntAnd.Covered = true := by decide +kernel
theorem gapAddmod_covered : gapAddmod.Covered = true := by decide +kernel
theorem mulmodLt_covered : mulmodLt.Covered = true := by decide +kernel
theorem intAndBad_covered : intAndBad.Covered = true := by decide +kernel
theorem intXorBad_covered : intXorBad.Covered = true := by decide +kernel
theorem addmodBad_covered : addmodBad.Covered = true := by decide +kernel
theorem mulmodBad_covered : mulmodBad.Covered = true := by decide +kernel
theorem addmodZero_covered : addmodZero.Covered = true := by decide +kernel

theorem gapAddmod_answers : decideGoal gapAddmod ≠ .unknown := decideGoal_complete gapAddmod_covered rfl
theorem gapIntAnd_answers : decideLeaf gapIntAnd ≠ .unknown := decideLeaf_complete gapIntAnd_covered
theorem gapIntAnd_iff : decideLeaf gapIntAnd = .proved ↔ Fml.Valid gapIntAnd :=
  decideLeaf_proved_iff gapIntAnd_covered

/-- info: ["refuted", "unknown"] -/
#guard_msgs in
#eval [verdict gapWrittenMemory, verdict gapHashNegForall]

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
