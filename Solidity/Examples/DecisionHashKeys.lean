import Solidity.Examples.DecisionHashCore

/-!
# Two kinds of hash as mapping keys

Public names remain in `Solidity.Examples.DecisionHashes` for existing consumers.
-/
namespace Solidity.Examples.DecisionHashes
open Solidity.Decide
set_option Elab.async false

/-! ### Two kinds as keys

Two mappings keyed by hashes of the strings, one by `keccak256`
(`mapping(string => uint)`), one by `sha256` (a `mapping(uint => uint)`
read at the hash).  The second kind's words key `shas` and are linked to
the first kind's (`Fml.tk`); the relabeling of each kind moves its root's
entries (`Fml.tk_complete`). -/

section TwoKeys

/-- `mapping(string => uint) ids; mapping(uint => uint) shas;` -/
/-- `ids[t] = 1;` -/
/-- **`∀ s t. sha256(s) ≠ sha256(t) → ids[s] == 0 → shas[sha256(s)] == 1 →
[ ids[t] = 1; ] (ids[s] == 0 ∧ shas[sha256(s)] == 1)`**: proved; without the
`sha256`s apart, refuted by one string twice. -/
/-- info: ["proved", "refuted"] -/
#guard_msgs in #eval [twoKeys, twoKeysBad].map verdict

/-- info: [true, true] -/
#guard_msgs in #eval [twoKeys, twoKeysBad].map (fun φ => φ.hashCovered && φ.inTarget {})

theorem twoKeys_covered : twoKeys.hashCovered = true := by decide +kernel

/-- **A second kind hashing one string**, which the first kind does not
hash (`gapMixedKinds`, M7 feature 27): its word needs no link, so the
string needs no hash of the first kind.  `ids[keccak256(s)] == 1 →
shas[sha256(t)] == 2 → ids[keccak256(s)] != shas[sha256(t)]`, proved;
`gapMixedKinds` (`ids[keccak256(s)] == 1 → shas[sha256(t)] == 1`) refuted. -/
/-- info: "proved" -/
#guard_msgs in #eval verdict mixedKinds

theorem mixedKinds_covered : mixedKinds.hashCovered = true := by decide +kernel

end TwoKeys


end Solidity.Examples.DecisionHashes
