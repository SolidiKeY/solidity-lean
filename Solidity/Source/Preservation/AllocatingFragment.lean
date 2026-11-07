import Solidity.Source.Preservation.NewArrayFragment

/-! An additive memory-expression admission over intrinsic resolved syntax.
It retains the original checked value fragment and admits reference locals,
identity conversions, conditionals with reference results, and dynamic new.
It neither changes ValFragC nor admits new reference-call bodies. -/
namespace Solidity.Source.Preservation
open EM

/-- A syntactic, memory-aware expression subset. The value constructor retains
both original admission checks; no semantic preservation premise is stored. -/
inductive AllocatingExpr {E : Env} (A : Decl → Prop) {Γ : RCtx} :
    {τ : STy} → RExpr E Γ τ → Prop
  | value {τ} {e : RExpr E Γ τ} : e.ValFragC A → e.OpsOK → AllocatingExpr A e
  | «local» {τ} (i : Idx Γ τ) : AllocatingExpr A (.local i)
  | same {τ} {e : RExpr E Γ τ} (h : Conv E.isBase E.mapFree τ τ) :
      AllocatingExpr A e → AllocatingExpr A (.conv e h)
  | branch {τ} {c : RExpr E Γ .bool} {a b : RExpr E Γ τ} :
      AllocatingExpr A c → AllocatingExpr A a → AllocatingExpr A b →
      AllocatingExpr A (.cond c a b)
  | newArray {τ σ : STy} {len : RExpr E Γ σ} (hn : τ.newable = true)
      (hi : σ.isIndex = true) : AllocatingExpr A len → AllocatingExpr A (.newArray hn len hi)

/-- Reference locals are justified by the actual local-state invariant, rather
than by the old value-type result lemma. -/
theorem eval_local_mem {E : Env} {Γ : RCtx} {τ : STy} (G : Glob E) (F : Fr)
    (n : Nat) (H : HeapTy) (i : Idx Γ τ) :
    Hoare (MemOK E H) (evalE G F (n+1) (.local i))
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  rw [evalE]
  exact Hoare.bind (Hoare.locals' (fun y h => ⟨h, LocalsOK.get y.1 i h.1.2⟩))
    (fun l => Hoare.pure' (fun _ h => h))

/-- All-horizon preservation of the additive subset, including validity of a
reference returned through either branch. Every halt retains MemOK. -/
theorem eval_allocating_mem {E : Env} {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) :
    ∀ n {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ), AllocatingExpr A e → ∀ H,
      Hoare (MemOK E H) (evalE G F n e)
        (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y)
  | 0, _, _, _, _, _ => by rw [evalE.eq_1]; exact Hoare.halt' (fun _ h => h)
  | n+1, _, _, e, admitted, H => by
    cases admitted with
    | value hf ho => exact evalE_fragment_mem calls F contract (n+1) e hf ho H
    | «local» i => exact eval_local_mem G F n H i
    | @same τ e h child =>
      rw [evalE]
      refine Hoare.bind (eval_allocating_mem calls F contract n e child H) (fun v => ?_)
      simp only [convRV]
      exact Hoare.pure' (fun _ h => h)
    | @branch τ c a b guard left right =>
      rw [evalE]
      refine Hoare.bind (Hoare.conseq (eval_allocating_mem calls F contract n c guard H)
        (fun _ h => h) (fun _ _ h => h.1) (fun _ _ h => h)) (fun v => ?_)
      refine Hoare.bind (MemPres.getV' v H) (fun x => ?_)
      split
      · exact eval_allocating_mem calls F contract n a left H
      · exact eval_allocating_mem calls F contract n b right H
    | newArray hn hi child =>
      exact Solidity.Roadmap.V16.SSCP2.NewAllocation.eval_new_mem _ _ G F n H _ _ hn _ hi
        (Hoare.conseq (eval_allocating_mem calls F contract n _ child H)
          (fun _ h => h) (fun _ _ h => h.1) (fun _ _ h => h))

#print axioms eval_local_mem
#print axioms eval_allocating_mem
end Solidity.Source.Preservation
