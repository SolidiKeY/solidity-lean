import Solidity.Examples.DecisionHashCore

/-!
# Value quantifiers and hidden-memory refusal controls.

Public names remain in `Solidity.Examples.DecisionHashes` for existing consumers.
-/

namespace Solidity.Examples.DecisionHashes
open Solidity.Decide
set_option Elab.async false
section Hashes
open Solidity.Examples.Tactics.Hashing (Names)

/-! #### A value quantifier in the body

The swap reads a value binder in the body as one (`Fml.sw`).  The premise
is read at each of its instances (`Fml.holdsS`), which only weakens a
positive binder, so a positive one is proved by the swapped leaf
(`Fml.posAll`, `Fml.holdsS_of_sw`). -/

/-- info: ["proved", "refuted"] -/
#guard_msgs in #eval [namesUnderForall, namesUnderForallBad].map verdict

/-- info: [true, true] -/
#guard_msgs in #eval [namesUnderForall, namesUnderForallBad].map (fun φ => φ.hashCovered && φ.inTarget {})

/-- A value quantifier in the body, by the kernel. -/
theorem namesUnderForall_covered : namesUnderForall.hashCovered = true := by decide +kernel

/-- info: (false, "unknown") -/
#guard_msgs in #eval (namesBound.inTarget {}, verdict namesBound)


end Hashes
end Solidity.Examples.DecisionHashes
