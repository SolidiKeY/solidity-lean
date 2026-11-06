import Solidity.Source.Progress.ForwardingReturns

/-! Initialized locals consume composed expressions, including certified internal
calls. The new local aliases the returned memory reference; the existing caller
locals and all reached allocations remain valid. Only identity conversions are
admitted here. -/
namespace Solidity.Source.Progress
open EM
variable {E : Env}

theorem initialized_composed_nsp {A : Decl → Prop} {G : Glob E} {c : String} {ds : List Decl}
    {n : Nat} (context : CompositionAt A G c ds n) (F : Fr) (contract : F.contract = c)
    (nps : Nat) {R : List STy} {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (same : τ.implicit E.isBase E.mapFree τ = true) (plain : PlainResultType τ)
    (ready : ComposedExpr A (fun d => d ∈ ds) e) (l : Locals E.layout Γ) :
    NSP (execS G F (n+1) nps none (.declInit (R := R) (M := false) (k := .body) e same) l)
      (fun out => ∃ v last, out = .normal (.cons v last)) := by
  rw [execS]
  have child : NS (do getV (← convRV F n τ (← evalE G F n e))) := by
    refine NS.bind (context.expr F contract e ready (Heap.empty : Heap E.layout).ty).1 (fun v => ?_)
    simp only [convRV,↓reduceDIte,pure_bind]
    exact getV_plain_ns plain v
  refine NSP.bind (NSP.sub' (Q := fun _ => True)
    (NSP.weaken (NSP.of_ns child) (fun _ _ _ => trivial))) (fun p _ => ?_)
  exact NSP.pure' ⟨p.1,p.2,rfl⟩

theorem initialized_composed_mem {A : Decl → Prop} {G : Glob E} {c : String} {ds : List Decl}
    {n : Nat} (context : CompositionAt A G c ds n) (F : Fr) (contract : F.contract = c)
    (nps : Nat) {R : List STy} {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (same : τ.implicit E.isBase E.mapFree τ = true) (ready : ComposedExpr A (fun d => d ∈ ds) e)
    (l : Locals E.layout Γ) (H : HeapTy) :
    Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l)
      (execS G F (n+1) nps none (.declInit (R := R) (M := false) (k := .body) e same) l)
      (fun o y => MemOK E H y ∧ ∃ v last, o = .normal (.cons v last) ∧
        v.RefOK E y.2.heap.ty ∧ LocalsOK E y.2.heap.ty last)
      (fun _ y => MemOK E H y) := by
  have child : ∀ H', Hoare (MemOK E H')
      (do getV (← convRV F n τ (← evalE G F n e)))
      (fun v y => MemOK E H' y ∧ v.RefOK E y.2.heap.ty) (fun _ y => MemOK E H' y) := by
    intro H'
    refine Hoare.bind (context.expr F contract e ready H').2 (fun v => ?_)
    simp only [convRV,↓reduceDIte,pure_bind]
    exact Preservation.getV_ref_mem v H'
  rw [execS]
  refine Hoare.bind (Preservation.sub_result_mem l _ (fun v st => v.RefOK E st.heap.ty) child H) (fun r => ?_)
  exact Hoare.pure' (fun _ valid => ⟨valid.1,r.1,r.2,rfl,valid.2.2,valid.2.1⟩)

#print axioms initialized_composed_nsp
#print axioms initialized_composed_mem
end Solidity.Source.Progress
