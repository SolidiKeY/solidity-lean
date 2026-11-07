import Solidity.Source.Preservation.Fragment
import Solidity.Roadmap.V16.SSCP2.NewAllocation

/-! Dynamic-new consumer of published allocation preservation. The child triple
is discharged by the existing checked call fragment, not assumed. This adds a
standalone allocating expression rule without changing ValFragC or CallsOK. -/
namespace Solidity.Source.Preservation
open EM

/-- New-array allocation after any indexable length expression in the existing
call fragment. Current/caller references and the full MemOK invariant survive
success AND every actual halt; no progress or universal fragment extension. -/
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
