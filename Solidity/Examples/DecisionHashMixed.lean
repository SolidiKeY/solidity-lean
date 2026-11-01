import Solidity.Examples.DecisionHashCore

/-!
# Partly linked mixed-kind strings

Public fixture names are preserved in `Solidity.Examples.DecisionHashes`.
-/
namespace Solidity.Examples.DecisionHashes
open Solidity.Decide
set_option Elab.async false
section Hashes
open Solidity.Examples.Tactics.Hashing (Names)

/-! #### Strings of the second kind the first does not hash

The decision links a pair of strings' extra words only where the premise
reads both strings' hashes of the first kind (`Fml.tkKeep`); a string the
first kind hashes nowhere is linked to none (M7, feature 29).  Its swapped
word is then read nowhere, and a refutation is moved, each such word set to
follow its extra word's class, before the relabeling (`Fml.tk_complete_move`,
`Calculus/HashMove.lean`). -/

/-- `d`, `c`, `b`, `a`, innermost first. -/
/-- **`keccak256(d) == keccak256(c) → sha256(b) == sha256(d) → sha256(b) ==
sha256(c)`**: `c`, `d` linked, `b` hashed by `sha256` only: proved. -/
/-- With `!=` last, refuted by one string three times. -/
/-- info: ["proved", "refuted"] -/
#guard_msgs in #eval [mixedSome, mixedSomeBad].map verdict

/-- Covered `keccak256` first, where `b` is unlinked (with `sha256` first,
`keccak256` hashes `c` and `d` only, both linked: feature 12). -/
theorem mixedSome_coveredK2 : mixedSome.coveredK2 .keccak .sha256 = true := by decide +kernel

/-- Reuse the exact two-kind coverage certificate through its existing route. -/
theorem mixedSome_covered : mixedSome.hashCovered = true := by
  let T : HashTry Names := tryK2 .keccak .sha256 (by decide) (by decide)
  have hc : T.covers = Fml.coveredK2 .keccak .sha256 := rfl
  have ht : T.covers mixedSome = true := by
    rw [hc]
    exact mixedSome_coveredK2
  have hm : T ∈ hashTries (C := Names) := by
    unfold hashTries
    iterate 3 apply List.mem_cons_of_mem
    exact List.mem_cons_self
  unfold Fml.hashCovered
  simp only [Bool.and_eq_true]
  exact ⟨by decide +kernel, List.any_eq_true.mpr ⟨T, hm, ht⟩⟩


#print axioms mixedSome_covered
#print axioms mixedSome_coveredK2

end Hashes
end Solidity.Examples.DecisionHashes
