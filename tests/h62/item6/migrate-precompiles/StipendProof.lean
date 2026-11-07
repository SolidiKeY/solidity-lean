import Solidity.Roadmap.Evm
namespace H62.StipendProof
open Solidity.Roadmap.Evm
/-- Exact numeric obligation underlying the frozen stipend theorem. -/
theorem explicitNatDecision : pinned.stipend < 3000 :=
  @of_decide_eq_true _ (Nat.decLt _ _) rfl
#print axioms explicitNatDecision
end H62.StipendProof
