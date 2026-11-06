import Solidity.Source.Progress.InitializedLocals

/-! Finite initialized-local prefixes followed by one composed return. The
certificate follows the intrinsic body syntax; it excludes uninitialized locals,
nonidentity conversions, loops and mutation. Scope exit uses the evaluator's
actual local restoration, including on reference returns. -/
namespace Solidity.Source.Progress
open EM
variable {E : Env}

inductive InitializedReturns (A B : Decl → Prop) (τ : STy) :
    {Γ Δ : RCtx} → RItems E [τ] false .body Γ Δ → Prop where
  | returned {Γ} {e : RExpr E Γ τ} (same : τ.implicit E.isBase E.mapFree τ = true)
      (plain : PlainResultType τ) : ComposedExpr A B e →
      InitializedReturns A B τ (.stmt (.retVal rfl e same) .nil)
  | initialized {Γ Δ σ} {e : RExpr E Γ σ}
      {rest : RItems E [τ] false .body (σ :: Γ) Δ}
      (same : σ.implicit E.isBase E.mapFree σ = true) (plain : PlainResultType σ) :
      ComposedExpr A B e → InitializedReturns A B τ rest →
      InitializedReturns A B τ (.stmt (.declInit e same) rest)

theorem initialized_prefix_items {A : Decl → Prop} {G : Glob E} {c : String} {ds : List Decl}
    (compositions : ∀ n, CompositionAt A G c ds n) (F : Fr) (contract : F.contract = c)
    (nps : Nat) {τ : STy} : ∀ n {Γ Δ : RCtx}
      (items : RItems E [τ] false .body Γ Δ)
      (_ready : InitializedReturns A (fun d => d ∈ ds) τ items)
      (l : Locals E.layout Γ) (_frame : BodyFrame nps [τ] Γ) (H : HeapTy),
      NSP (execItems G F n nps none items l) (fun o => o.esc = false) ∧
      Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l)
        (execItems G F n nps none items l)
        (fun o y => MemOK E H y ∧ Preservation.OutRefsOK (E := E) y.2.heap.ty o)
        (fun _ y => MemOK E H y)
  | 0, _, _, _, _, _, _, _ => by
    rw [execItems.eq_1]
    exact ⟨NSP.halt' trivial,Hoare.halt' (fun _ h => h.1)⟩
  | 1, _, _, _, ready, _, _, _ => by
    cases ready <;> simp only [execItems,execS,bind] <;>
      exact ⟨NSP.halt' trivial,Hoare.halt' (fun _ h => h.1)⟩
  | n+2, Γ, Δ, _, ready, l, frame, H => by
    cases ready with
    | returned same plain expression =>
      rw [execItems]
      constructor
      · refine NSP.bind (return_composed_nsp (compositions n) F contract nps _ same plain expression l frame)
          (fun out returned => ?_)
        rcases returned with ⟨last,rfl⟩
        exact NSP.pure' rfl
      · refine Hoare.bind (return_composed_mem (compositions n) F contract nps _ same expression l H) (fun out => ?_)
        intro state valid
        rcases valid.2 with ⟨last,rfl,locals⟩
        exact ⟨valid.1,locals⟩
    | @initialized _ _ σ e rest same plain expression tail =>
      rw [execItems]
      constructor
      · refine NSP.bind (initialized_composed_nsp (compositions n) F contract nps e same plain expression l)
          (fun out normal => ?_)
        rcases normal with ⟨v,last,rfl⟩
        refine NSP.bind (initialized_prefix_items compositions F contract nps (n+1) rest tail
          (.cons v last) (frame.ext [σ]) H).1 (fun result safe => ?_)
        exact NSP.weaken (Out.up_esc [σ] result) (fun _ same => same.trans safe)
      · refine Hoare.bind (initialized_composed_mem (compositions n) F contract nps e same expression l H)
          (fun out => ?_)
        intro state valid
        rcases valid.2 with ⟨v,last,rfl,hv,hl⟩
        exact Hoare.bind (initialized_prefix_items compositions F contract nps (n+1) rest tail
          (.cons v last) (frame.ext [σ]) H).2 (fun result => Preservation.up_mem result H)
          state ⟨valid.1,hv,hl⟩

#print axioms initialized_prefix_items
end Solidity.Source.Progress
