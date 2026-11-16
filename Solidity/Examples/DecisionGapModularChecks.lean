import Solidity.Examples.Decision
import Solidity.Examples.DecisionThreeKindProof

/-! Checks literal refutations, modular/integer-bitwise coverage, answer completeness, and written-memory/hash verdict regressions. -/

namespace Solidity.Examples.Decision

open Solidity.Decide

set_option Elab.async false

/-- info: ["refuted", "refuted", "refuted", "refuted", "refuted", "refuted", "refuted"] -/
#guard_msgs in #eval [intDivBad, intModBad, orBad, xorBad, andBad, powBad, mulWBad].map verdict

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

end Solidity.Examples.Decision
