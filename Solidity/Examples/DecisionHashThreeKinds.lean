import Solidity.Examples.DecisionHashCore

/-!
# Three-kind hashes and partly linked mixed-kind strings.

Public names remain in `Solidity.Examples.DecisionHashes` for existing consumers.
-/

namespace Solidity.Examples.DecisionHashes
open Solidity.Decide
set_option Elab.async false
section Hashes
open Solidity.Examples.Tactics.Hashing (Names)

/-! #### Three kinds

A string hashed by three kinds stands for one word per kind: the second
kind's words a layer of binders linked to the first kind's, the third
kind's a layer inside it (`Fml.tk3`, `Calculus/HashKinds3.lean`, M7
feature 28).  Each layer is relabeled in turn (`Fml.tk3_complete`). -/

/-- **`keccak256(s) == keccak256(t) → sha256(s) == sha256(t) →
ripemd160(s) == ripemd160(t)`** (`gapThreeKinds`): proved; with `!=` last,
refuted by one string twice. -/
/-- info: ["proved", "refuted"] -/
#guard_msgs in #eval [namesThreeKinds, namesThreeKindsBad].map verdict

theorem namesThreeKindsBad_covered : namesThreeKindsBad.hashCovered = true := by
  have hk : namesThreeKindsBad.coveredK3 .ripemd160 .keccak .sha256 = true := by
    decide +kernel
  let T : HashTry Names :=
    tryK3 .ripemd160 .keccak .sha256 (by decide) (by decide) (by decide)
  have hc : T.covers = Fml.coveredK3 .ripemd160 .keccak .sha256 := rfl
  have ht : T.covers namesThreeKindsBad = true := by
    rw [hc]
    exact hk
  have hm : T ∈ hashTries (C := Names) := by
    unfold hashTries
    iterate 13 apply List.mem_cons_of_mem
    exact List.mem_cons_self
  unfold Fml.hashCovered
  simp only [Bool.and_eq_true]
  exact ⟨by decide +kernel, List.any_eq_true.mpr ⟨T, hm, ht⟩⟩

#print axioms namesThreeKindsBad_covered
end Hashes
end Solidity.Examples.DecisionHashes
