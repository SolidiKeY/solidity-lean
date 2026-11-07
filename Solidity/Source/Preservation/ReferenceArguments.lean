import Solidity.Source.Preservation.AllocatingFragment

/-! Exact-type arguments may be reference locals or allocating expressions.
The argument list keeps earlier references valid through later allocations.
Cross-type conversions and arbitrary reference-callee bodies are not admitted. -/
namespace Solidity.Source.Preservation
open EM

inductive ExactArgs {E : Env} (A : Decl → Prop) {Γ : RCtx} :
    {ts : List STy} → RConvArgs E Γ ts → Prop
  | nil : ExactArgs A .nil
  | cons {τ : STy} {ts : List STy} {e : RExpr E Γ τ} {es : RConvArgs E Γ ts}
      (h : τ.implicit E.isBase E.mapFree τ = true) :
      AllocatingExpr A e → ExactArgs A es → ExactArgs A (.cons e h es)

/-- Extracting a plain value retains its reference witness on success. A
non-plain RVal keeps its actual getV halt; no successful extraction is assumed. -/
theorem getV_ref_mem {E : Env} {Γ : RCtx} {τ : STy} (v : RVal E.layout τ) (H : HeapTy) :
    Hoare (fun y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (getV (Γ := Γ) v)
      (fun x y => MemOK E H y ∧ x.RefOK E y.2.heap.ty) (fun _ y => MemOK E H y) := by
  cases v with
  | val x => exact Hoare.lift' (fun _ h => h)
  | const _ | strLit _ | hex _ _ | tuple _ => exact Hoare.lift' (fun _ h => h.1)

/-- Earlier argument references remain valid after the tail grows the heap.
The proof uses the actual left-to-right evalConvArgs evaluator. -/
theorem eval_exact_args_mem {E : Env} {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) :
    ∀ n {Γ : RCtx} {ts : List STy} (es : RConvArgs E Γ ts), ExactArgs A es → ∀ H,
      Hoare (MemOK E H) (evalConvArgs G F n es)
        (fun vs y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR) (fun _ y => MemOK E H y)
  | 0, _, _, _, _, _ => by rw [evalConvArgs.eq_1]; exact Hoare.halt' (fun _ h => h)
  | n+1, _, _, _, admitted, H => by
    cases admitted with
    | nil => exact Hoare.pure' (fun _ h => ⟨h, trivial⟩)
    | @cons τ ts e es same head tail =>
      rw [evalConvArgs]
      refine Hoare.bind (eval_allocating_mem calls F contract n e head H) (fun v => ?_)
      simp only [convRV, ↓reduceDIte, pure_bind]
      refine Hoare.bind (getV_ref_mem v H) (fun x => ?_)
      refine Hoare.bind (Hoare.memGrow (R := fun H' => x.RefOK E H')
        (fun H' => eval_exact_args_mem calls F contract n es tail H')) (fun vs => ?_)
      refine Hoare.pure' (fun y h => ?_)
      rcases h.2.2 with ⟨H', hx, growth⟩
      exact ⟨h.1, Val.RefOK.mono growth hx, h.2.1⟩

#print axioms getV_ref_mem
#print axioms eval_exact_args_mem
end Solidity.Source.Preservation
