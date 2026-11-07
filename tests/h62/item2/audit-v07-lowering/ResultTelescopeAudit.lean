import Solidity.Lowering.V07.LocalFamilyControls
import Solidity.Lowering.V07.NodeRank

/-!
Guarded regression: source-inferred result binders must not be silently treated
as propositions or omitted from the V07 audit. These exact typed applications
resolve the four retained result groups against the imported declarations.
This does not resolve inherited section membership or the rest of the census,
and live Lean 4.24 checking does not establish Lean 4.35 migration acceptance.
-/
namespace Solidity.H62.AuditV07.ResultTelescopeAudit
open Solidity.Lowering.V07
open RecursiveGraph

/-- The collapsed-content input is a pair of Boolean keys, not alias evidence. -/
def collapsed_signature :
    ∀ k : LocalFamilyControls.Keys,
      IntValueRel .u8 (LocalFamilyControls.source.1.get (LocalFamilyControls.si k))
        (TEnv.get (LocalFamilyControls.collapsed k) LocalFamilyControls.target.env) :=
  @LocalFamilyControls.collapsed_contents_agree

/-- The iteration is Nat and the selected node is intrinsically Fin n. -/
def count_signature :
    ∀ {n : Nat} (fs : Fin n → List (Name × TypeGraph.Ty n))
      (r : Fin n → Nat),
      (∀ i f, f ∈ fs i → f.2.inlineRank r < r i) →
      ∀ (k : Nat) (i : Fin n), NodeRank.height r i ≤ k →
        rankIter fs k i = rankIter fs (k+1) i :=
  @NodeRank.stable_by_count

/-- The node-count result quantifies a Fin n node, retaining the valid-rank proof. -/
def nodes_signature :
    ∀ {n : Nat} (fs : Fin n → List (Name × TypeGraph.Ty n))
      (r : Fin n → Nat),
      (∀ i f, f ∈ fs i → f.2.inlineRank r < r i) →
      ∀ i : Fin n, rankIter fs n i = rankIter fs (n+1) i :=
  @NodeRank.stable_at_nodes

/-- Positive comparison ranks and field validity remain separate proof inputs. -/
def iteration_signature :
    ∀ {n : Nat} (fs : Fin n → List (Name × TypeGraph.Ty n))
      (r : Fin n → Nat),
      (∀ i, 0 < r i) → (∀ i f, f ∈ fs i → f.2.inlineRank r < r i) →
      ∀ (k : Nat) (i : Fin n), r i ≤ k →
        rankIter fs k i = rankIter fs (k+1) i :=
  @RankConvergence.iter_stable

#check @LocalFamilyControls.collapsed_contents_agree
#check @NodeRank.stable_by_count
#check @NodeRank.stable_at_nodes
#check @RankConvergence.iter_stable
#print axioms collapsed_signature
#print axioms count_signature
#print axioms nodes_signature
#print axioms iteration_signature
end Solidity.H62.AuditV07.ResultTelescopeAudit
