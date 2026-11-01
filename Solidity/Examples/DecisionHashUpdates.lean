import Solidity.Examples.DecisionHashCore

/-!
# Hashes past storage and value-local updates.

Public names remain in `Solidity.Examples.DecisionHashes` for existing consumers.
-/

namespace Solidity.Examples.DecisionHashes
open Solidity.Decide
set_option Elab.async false
section Hashes
open Solidity.Examples.Tactics.Hashing (Names)

/-! #### A hash past an update

The usual shape past symbolic execution: the hypotheses at the top, the
conclusion past an update.  The premise reads a hash in an update's
continuation where the update lands (`Fml.HashIn`), so the second kind's
words may be read there; the first kind's hash of each string is read at
the top (`Fml.tkBody`). -/

/-- `{ storage := save(storage, ids[0], 1) } φ`: `ids[0] = 1;`. -/
/-- **`sha256(s) == sha256(t) → [ ids[0] = 1; ] keccak256(s) == keccak256(t)`**:
proved; without the hypothesis, refuted. -/
/-- A value local set in the leaf (`{ x := 1 }`): `∀ x s t. sha256(s) ==
sha256(t) → { x := 1 } (keccak256(s) == keccak256(t) ∧ x == 1)`, proved;
its false variant (`x == 2`) refuted. -/
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


end Hashes
end Solidity.Examples.DecisionHashes
