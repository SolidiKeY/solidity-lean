import Solidity.Examples.DecisionHashes

/-!
# The closer's decision on leaves with hashes (M7, plan step 7)

`decideGoal` (`Calculus/Decision.lean`) on leaves whose memory locals are
fresh strings read only by hashes of one kind or of two (`decideHash`):
proofs by the swapped leaf, refutations by strings of a family,
kernel-checked coverage (`Fml.hashCovered`), and leaves outside it.
-/

namespace Solidity.Examples.DecisionHashes

open Solidity.Decide

set_option Elab.async false

/-! ### Leaves with hashes (M7, plan step 7)

The string-keyed mapping of `Examples/Tactics/Hashing.lean` §3 (`Names`,
`mapping(string => uint) ids`, keyed by `keccak256` of the string).  A leaf
over two fresh strings (`Fml.allocAll`, any bytes) is read under its own hash
premise: `keccak256(s) != keccak256(t)` says the strings read different
bytes, and `ids[keccak256(s)]`, `ids[keccak256(t)]` are one entry exactly
where they read the same.  `decideGoal` reads each string as the word it
hashes to (`Fml.swPrefix`), so a proof holds whatever the hash; a refutation
picks the strings (`Fml.swInst`), one of a family of one-word strings with
distinct hashes per class, so it meets the premise.  The leaves are written
with the constructors: `dl!` has no notation for a fresh string or a hash in
a formula. -/

section Hashes

open Solidity.Examples.Tactics.Hashing (Names)

/-- A string: a `uint[]` in memory. -/
/-- The two strings' context, `t` innermost. -/
/-- `find(storage, ids[key])` -/
/-- `keccak256(memory, s)` and `keccak256(memory, t)`; `sha256(memory, ·)`. -/
/-- `∀ fresh strings s t. φ` -/
/-- `{ storage := save(storage, ids[keccak256(t)], 1) } φ`: `ids[t] = 1;`. -/
/-- **`∀ s t. s ≠ t → ids[s] == 0 → [ ids[t] = 1; ] ids[s] == 0`**, past the
program. -/
/-- Without `s ≠ t`: refuted by two strings with the same bytes. -/
/-- Equal hashes, equal entries; and equal hashes alone, refuted by two
strings with different bytes. -/
/-- Two kinds of hash of one string: valid under the premise (equal
`sha256`s, equal bytes, equal `keccak256`s).  Each string stands for one
word per kind, the `sha256` words binders of their own linked to the
`keccak256` ones (`Fml.tk`, `Calculus/HashKinds.lean`): proved.  Its false
variant, refuted by one string twice. -/
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


end Hashes

end Solidity.Examples.DecisionHashes
