import Solidity.Examples.DecisionHashCore
import Solidity.Examples.DecisionHashFamilyCheck
import Solidity.Examples.DecisionHashFiveChain

/-!
# Five-string family and exact coverage controls.

Public names remain in `Solidity.Examples.DecisionHashes` for existing consumers.
-/

namespace Solidity.Examples.DecisionHashes
open Solidity.Decide
set_option Elab.async false
section Hashes
open Solidity.Examples.Tactics.Hashing (Names)

/-! #### More strings than `famBound`

A refutation picks one string of the family per class of equal strings,
so a leaf of `n` strings needs `n` strings with distinct hashes.  Up to
`famBound` the family is the kernel's theorem (`famOKAll_bound`); past it,
`famCheck` computes the family's `3n` hashes (`famN`, `famOKAll`), and a
coverage check asks for the same (`famCovered`). -/

/-- info: ["refuted", "proved"] -/
#guard_msgs in #eval [fiveStrings, fiveChain].map verdict

/-- info: [true, true] -/
#guard_msgs in #eval [fiveStrings, fiveChain].map (fun φ => φ.hashCovered && φ.inTarget {})


end Hashes
end Solidity.Examples.DecisionHashes
