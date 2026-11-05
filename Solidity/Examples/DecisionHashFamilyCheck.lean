import Solidity.Calculus.HashReduction

/-!
# Kernel checks for the existing five-string regression family

Check each kind once and compose the results. The decision procedure's
family, `famBound`, check and budgets are unchanged.
-/
namespace Solidity.Examples.DecisionHashes
open Solidity.Decide
set_option Elab.async false

/-- The original five one-word strings have distinct nonzero Keccak hashes. -/
theorem famOK_five_keccak : famOK .keccak 5 = true := by decide +kernel
/-- The same existing family has distinct nonzero SHA-256 hashes. -/
theorem famOK_five_sha256 : famOK .sha256 5 = true := by decide +kernel
/-- The same existing family has distinct nonzero RIPEMD-160 hashes. -/
theorem famOK_five_ripemd160 : famOK .ripemd160 5 = true := by decide +kernel

/-- Compose the three kernel checks without reevaluating the hash algorithms. -/
theorem famOKAll_five : famOKAll 5 = true := by
  simp only [famOKAll, famOK_five_keccak, famOK_five_sha256, famOK_five_ripemd160, Bool.and_self]

/-- The unchanged coverage check accepts this exact five-string family. -/
theorem famCovered_five : famCovered 5 = true := by
  simp only [famCovered, famOKAll_five, Bool.or_true]

#print axioms famOK_five_keccak
#print axioms famOK_five_sha256
#print axioms famOK_five_ripemd160
#print axioms famOKAll_five
#print axioms famCovered_five
end Solidity.Examples.DecisionHashes
