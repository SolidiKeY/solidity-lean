import Solidity.Examples.DecisionHashCore
import Solidity.Examples.DecisionHashFamilyCheck

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

/-- **Two of five strings read alike**: refuted only by five classes, five
strings with distinct bytes (`gapFiveStrings` until 2026-10-25). -/
/-- A chain of equal hashes: proved. -/
/-- info: ["refuted", "proved"] -/
#guard_msgs in #eval [fiveStrings, fiveChain].map verdict

/-- info: [true, true] -/
#guard_msgs in #eval [fiveStrings, fiveChain].map (fun φ => φ.hashCovered && φ.inTarget {})

/-- Five strings, by the kernel: the family of five checked (`famOKAll 5`,
fifteen hashes) and the 52 instances covered. -/
theorem fiveChain_covered : fiveChain.hashCovered = true := by
  have hf : famCovered fiveChain.allocCount = true := by
    change famCovered 5 = true
    exact famCovered_five
  have hk : fiveChain.coveredK .keccak = true := by
    simp only [Fml.coveredK, hf]
    decide +kernel
  unfold Fml.hashCovered
  simp only [Bool.and_eq_true]
  refine ⟨by decide +kernel, List.any_eq_true.mpr ?_⟩
  refine ⟨tryK .keccak (by decide), ?_, hk⟩
  simp only [hashTries, List.mem_cons, true_or]


#print axioms fiveChain_covered

end Hashes
end Solidity.Examples.DecisionHashes
