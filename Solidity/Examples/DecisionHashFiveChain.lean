import Solidity.Examples.DecisionHashes
import Solidity.Examples.DecisionHashFamilyCheck

/-! # Isolated kernel coverage of the existing five-string chain
The original public statement and proof obligations are retained. No decision
budget, family or hash premise changes; the guarded observations remain in
DecisionHashFamilies so they can be checked independently of this proof.
-/
namespace Solidity.Examples.DecisionHashes
open Solidity.Decide
set_option Elab.async false

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

end Solidity.Examples.DecisionHashes
