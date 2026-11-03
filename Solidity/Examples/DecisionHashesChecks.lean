import Solidity.Examples.DecisionHashes

/-!
# The checks of `Examples/DecisionHashes.lean`

The verdicts (`#eval` pins), fragment membership and kernel-checked coverage
(`decide +kernel`) of the hash leaves defined in `Examples/DecisionHashes.lean`,
in its order.  The formulas stay there, where `Examples/Decision.lean` reads
them; the checks are this leaf, which nothing imports, so they build beside
the decision examples instead of before them (`docs/parallelism.md`, P2 and P5).
-/

namespace Solidity.Examples.DecisionHashes

open Solidity.Decide

section Hashes

open Solidity.Examples.Tactics.Hashing (Names)

/-- info: ["proved", "refuted", "proved", "refuted", "proved", "refuted"] -/
#guard_msgs in
#eval [namesSet, namesSetBad, namesEq, namesEqBad, namesTwoKinds, namesTwoKindsBad].map verdict

/-- info: [true, true, true, true, true, true] -/
#guard_msgs in
#eval [namesSet, namesSetBad, namesEq, namesEqBad, namesTwoKinds, namesTwoKindsBad].map Fml.hashCovered

/-- info: [true, true, true, true, true, true] -/
#guard_msgs in
#eval [namesSet, namesSetBad, namesEq, namesEqBad, namesTwoKinds, namesTwoKindsBad].map (Fml.inTarget {})

/-- Two kinds of hash, by the kernel: the reading with the `sha256` words
and its instances covered. -/
theorem namesTwoKinds_covered : namesTwoKinds.hashCovered = true := by decide +kernel

/-- `decideGoal_complete_hash`, applied to two kinds. -/
theorem namesTwoKinds_answers : decideGoal namesTwoKinds ≠ .unknown :=
  decideGoal_complete_hash namesTwoKinds_covered

/-- The leaf is covered, by the kernel: its swapped reading and its two
instances (one class, two classes) in `Fml.Covered`, its keyed root `ids`. -/
theorem namesSet_covered : namesSet.hashCovered = true := by decide +kernel

/-- `decideGoal_complete_hash`, applied. -/
theorem namesSet_answers : decideGoal namesSet ≠ .unknown := decideGoal_complete_hash namesSet_covered

theorem namesEqBad_covered : namesEqBad.hashCovered = true := by decide +kernel

/-- info: ["proved", "refuted", "proved", "refuted"] -/
#guard_msgs in #eval [namesLanded, namesLandedBad, namesSetLocal, namesSetLocalBad].map verdict

/-- info: [true, true, true, true] -/
#guard_msgs in
#eval [namesLanded, namesLandedBad, namesSetLocal, namesSetLocalBad].map
  (fun φ => φ.hashCovered && φ.inTarget {})

/-- A hash past an update, by the kernel. -/
theorem namesLanded_covered : namesLanded.hashCovered = true := by decide +kernel

/-- `decideGoal_complete_hash`, applied past an update. -/
theorem namesLanded_answers : decideGoal namesLanded ≠ .unknown :=
  decideGoal_complete_hash namesLanded_covered

/-- info: ["refuted", "proved"] -/
#guard_msgs in #eval [fiveStrings, fiveChain].map verdict

/-- info: [true, true] -/
#guard_msgs in #eval [fiveStrings, fiveChain].map (fun φ => φ.hashCovered && φ.inTarget {})

/-- Five strings, by the kernel: the family of five checked (`famOKAll 5`,
fifteen hashes) and the 52 instances covered. -/
theorem fiveChain_covered : fiveChain.hashCovered = true := by decide +kernel

/-- info: ["proved", "refuted"] -/
#guard_msgs in #eval [namesUnderForall, namesUnderForallBad].map verdict

/-- info: [true, true] -/
#guard_msgs in #eval [namesUnderForall, namesUnderForallBad].map (fun φ => φ.hashCovered && φ.inTarget {})

/-- A value quantifier in the body, by the kernel. -/
theorem namesUnderForall_covered : namesUnderForall.hashCovered = true := by decide +kernel

/-- info: (false, "unknown") -/
#guard_msgs in #eval (namesBound.inTarget {}, verdict namesBound)

/-- info: ["proved", "refuted"] -/
#guard_msgs in #eval [namesThreeKinds, namesThreeKindsBad].map verdict

theorem namesThreeKindsBad_covered : namesThreeKindsBad.hashCovered = true := by decide +kernel

/-- info: ["proved", "refuted"] -/
#guard_msgs in #eval [mixedSome, mixedSomeBad].map verdict

theorem mixedSome_covered : mixedSome.hashCovered = true := by decide +kernel

/-- Covered `keccak256` first, where `b` is unlinked (with `sha256` first,
`keccak256` hashes `c` and `d` only, both linked: feature 12). -/
theorem mixedSome_coveredK2 : mixedSome.coveredK2 .keccak .sha256 = true := by decide +kernel

end Hashes

section TwoKeys

/-- info: ["proved", "refuted"] -/
#guard_msgs in #eval [twoKeys, twoKeysBad].map verdict

/-- info: [true, true] -/
#guard_msgs in #eval [twoKeys, twoKeysBad].map (fun φ => φ.hashCovered && φ.inTarget {})

theorem twoKeys_covered : twoKeys.hashCovered = true := by decide +kernel

/-- info: "proved" -/
#guard_msgs in #eval verdict mixedKinds

theorem mixedKinds_covered : mixedKinds.hashCovered = true := by decide +kernel

end TwoKeys

end Solidity.Examples.DecisionHashes
