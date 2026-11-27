import Solidity.Source.Preservation.Fragment
import Solidity.Roadmap.V16.SSCP2.NewAllocation


namespace Solidity.Source.Preservation
open EM


theorem eval_new_fragment_mem {E : Env} {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (n : Nat) (H : HeapTy)
    {Γ : RCtx} {τ σ : STy} (newable : τ.newable = true) (len : RExpr E Γ σ)
    (indexable : σ.isIndex = true) (fragment : len.ValFragC A) (operations : len.OpsOK) :
    Hoare (MemOK E H) (evalE G F (n + 1) (.newArray newable len indexable))
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  apply Solidity.Roadmap.V16.SSCP2.NewAllocation.eval_new_mem E Γ G F n H τ σ newable len indexable
  exact Hoare.conseq (evalE_fragment_mem calls F contract n len fragment operations H)
    (fun _ h => h) (fun _ _ h => h.1) (fun _ _ h => h)

#print axioms eval_new_fragment_mem
end Solidity.Source.Preservation
