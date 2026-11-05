import Solidity.Lowering.V07.GraphRanks

/-! H14 signature validation ONLY. These definitions name propositions; they
are not proofs, axioms, a frozen interface, or completed theorem obligations. -/
namespace Solidity.Lowering.V07.TerraStatementChecks
open RecursiveGraph

def step_ext_statement : Prop :=
  ∀ {n : Nat} (fs : Fin n → List (Name × TypeGraph.Ty n)) (r s : Fin n → Nat),
    (∀ i, r i = s i) → rankStep fs r = rankStep fs s

def iter_zero_statement : Prop :=
  ∀ {n : Nat} (fs : Fin n → List (Name × TypeGraph.Ty n)),
    rankIter fs 0 = fun _ => 0

def iter_succ_statement : Prop :=
  ∀ {n : Nat} (fs : Fin n → List (Name × TypeGraph.Ty n)) (k : Nat),
    rankIter fs (k+1) = rankStep fs (rankIter fs k)

def iter_le_later_statement : Prop :=
  ∀ {n : Nat} (fs : Fin n → List (Name × TypeGraph.Ty n)) (k m : Nat),
    k ≤ m → ∀ i, rankIter fs k i ≤ rankIter fs m i

def fixed_tail_statement : Prop :=
  ∀ {n : Nat} (fs : Fin n → List (Name × TypeGraph.Ty n)) (k : Nat),
    (∀ i, rankIter fs (k+1) i = rankIter fs k i) →
      ∀ t i, rankIter fs (k+t) i = rankIter fs k i

#check step_ext_statement
#check iter_zero_statement
#check iter_succ_statement
#check iter_le_later_statement
#check fixed_tail_statement

end Solidity.Lowering.V07.TerraStatementChecks
