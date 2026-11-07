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
