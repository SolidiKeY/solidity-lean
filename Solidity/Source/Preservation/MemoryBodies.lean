import Solidity.Source.Preservation.MemoryExpressions

/-! An additive memory-body certificate and joint statement/sequence Hoare
proof. Default and initialized declarations, reference rebindings, primitive
array writes, scopes and reference returns reuse the actual evaluator frames.
Old value-fragment statements/loops remain available with all old premises. -/
namespace Solidity.Source.Preservation
open EM
variable {E : Env}

mutual
inductive MemoryStmt {E : Env} (A : Decl → Prop) (R : List STy) (M : Bool) :
    {k : SCtx} → {Γ Δ : RCtx} → RStmt E R M k Γ Δ → Prop
  | value {k Γ Δ} {s : RStmt E R M k Γ Δ} : s.ValFragC A → s.OpsOK → MemoryStmt A R M s
  | expr {k Γ τ} {e : RExpr E Γ τ} : BodyExpr A e → MemoryStmt A R M (.expr (k := k) e)
  | declVar {k Γ} (τ : STy) : MemoryStmt A R M (.declVar (k := k) (Γ := Γ) τ)
  | declInit {k Γ τ} {e : RExpr E Γ τ} (h : τ.implicit E.isBase τ = true) :
      BodyExpr A e → MemoryStmt A R M (.declInit (k := k) e h)
  | returns {k Γ} {args : RConvArgs E Γ R} : ExactArgs A args → MemoryStmt A R M (.retTuple (k := k) args)
  | block {k Γ Δ} {b : RItems E R M k Γ Δ} : MemoryItems A R M b → MemoryStmt A R M (.block b)
inductive MemoryItems {E : Env} (A : Decl → Prop) (R : List STy) (M : Bool) :
    {k : SCtx} → {Γ Δ : RCtx} → RItems E R M k Γ Δ → Prop
  | nil {k Γ} : MemoryItems A R M (.nil (k := k) (Γ := Γ))
  | stmt {k Γ Ξ Δ} {s : RStmt E R M k Γ Ξ} {rest : RItems E R M k Ξ Δ} :
      MemoryStmt A R M s → MemoryItems A R M rest → MemoryItems A R M (.stmt s rest)
  | unchecked {l Γ Ξ Δ} {b : RItems E R M ⟨l,true⟩ Γ Ξ} {rest : RItems E R M ⟨l,false⟩ Γ Δ} :
      MemoryItems A R M b → MemoryItems A R M rest → MemoryItems A R M (.unchecked b rest)
end

structure MemoryBodyAt (A : Decl → Prop) (G : Glob E) (c : String) (n : Nat) : Prop where
  stmt : ∀ F, F.contract = c → ∀ nps ph {R : List STy} {M : Bool} {k : SCtx} {Γ Δ : RCtx}
    (s : RStmt E R M k Γ Δ), MemoryStmt A R M s → ∀ l H,
    Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l) (execS G F n nps ph s l)
      (fun o y => MemOK E H y ∧ OutRefsOK (E := E) y.2.heap.ty o) (fun _ y => MemOK E H y)
  items : ∀ F, F.contract = c → ∀ nps ph {R : List STy} {M : Bool} {k : SCtx} {Γ Δ : RCtx}
    (b : RItems E R M k Γ Δ), MemoryItems A R M b → ∀ l H,
    Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l) (execItems G F n nps ph b l)
      (fun o y => MemOK E H y ∧ OutRefsOK (E := E) y.2.heap.ty o) (fun _ y => MemOK E H y)

theorem plain_body_expr_mem {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (hc : F.contract = c) (n : Nat)
    {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) (h : BodyExpr A e) (H : HeapTy) :
    Hoare (MemOK E H) (do getV (← convRV F n τ (← evalE G F n e)))
      (fun v y => MemOK E H y ∧ v.RefOK E y.2.heap.ty) (fun _ y => MemOK E H y) := by
  refine Hoare.bind (eval_body_expr_mem calls F hc n e h H) (fun v => ?_)
  simp only [convRV,↓reduceDIte,pure_bind]
  exact getV_ref_mem v H

theorem memory_stmt_step {A : Decl → Prop} {G : Glob E} {c : String} {n : Nat}
    (calls : CallsOK A G c) (ih : MemoryBodyAt A G c n)
    (F : Fr) (hc : F.contract = c) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Δ : RCtx} (s : RStmt E R M k Γ Δ)
    (admitted : MemoryStmt A R M s) (l : Locals E.layout Γ) (H : HeapTy) :
    Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l) (execS G F (n+1) nps ph s l)
      (fun o y => MemOK E H y ∧ OutRefsOK (E := E) y.2.heap.ty o) (fun _ y => MemOK E H y) := by
  cases admitted with
  | value hf ho => exact (fragMemAt calls (n+1)).stmt.execS F hc nps ph s l hf ho H
  | expr h =>
    rw [execS]
    refine Hoare.bind (sub_result_mem l (evalE G F n _)
      (fun v st => RValOK E st.heap.ty v) (fun H' => eval_body_expr_mem calls F hc n _ h H') H) (fun r => ?_)
    exact Hoare.pure' (fun _ h => ⟨h.1,h.2.1⟩)
  | declVar τ =>
    rw [execS]
    refine Hoare.bind (sub_result_mem l (zeroVal n τ)
      (fun v st => v.RefOK E st.heap.ty) (fun H' => (zeroOK n).val H' τ) H) (fun r => ?_)
    exact Hoare.pure' (fun _ h => ⟨h.1,h.2.2,h.2.1⟩)
  | declInit same h =>
    rw [execS]
    refine Hoare.bind (sub_result_mem l _ (fun v st => v.RefOK E st.heap.ty)
      (fun H' => plain_body_expr_mem calls F hc n _ h H') H) (fun r => ?_)
    exact Hoare.pure' (fun _ h => ⟨h.1,h.2.2,h.2.1⟩)
  | returns h =>
    refine Hoare.conseq (return_exact_mem calls F hc n nps ph _ h l H)
      (fun _ h => h) (fun o y h => ?_) (fun _ _ h => h)
    rcases h.2 with ⟨last,rfl,valid⟩
    exact ⟨h.1,valid⟩
  | block h =>
    rw [execS]
    exact Hoare.bind (ih.items F hc nps ph _ h l H) (fun o => close_mem o H)

theorem memory_items_step {A : Decl → Prop} {G : Glob E} {c : String} {n : Nat}
    (ih : MemoryBodyAt A G c n) (F : Fr) (hc : F.contract = c) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Δ : RCtx} (b : RItems E R M k Γ Δ)
    (admitted : MemoryItems A R M b) (l : Locals E.layout Γ) (H : HeapTy) :
    Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l) (execItems G F (n+1) nps ph b l)
      (fun o y => MemOK E H y ∧ OutRefsOK (E := E) y.2.heap.ty o) (fun _ y => MemOK E H y) := by
  cases admitted with
  | nil => exact Hoare.pure' (fun _ h => h)
  | stmt head tail =>
    rw [execItems]
    refine Hoare.bind (ih.stmt F hc nps ph _ head l H) (fun o => ?_)
    cases o with
    | normal l' => exact Hoare.bind (ih.items F hc nps ph _ tail l' H) (fun o' => up_mem o' H)
    | brk l' | cont l' | ret l' => exact Hoare.pure' (fun _ h => h)
  | unchecked inner tail =>
    rw [execItems]
    refine Hoare.bind (ih.items {F with checked := false} hc nps ph _ inner l H) (fun o => ?_)
    cases o with
    | normal l' => exact Hoare.bind (restore_mem l' H) (fun l'' => ih.items F hc nps ph _ tail l'' H)
    | brk l' | cont l' | ret l' => exact Hoare.pure' (fun _ h => h)

theorem memory_body_at {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) : ∀ n, MemoryBodyAt A G c n
  | 0 => {
      stmt := by intros; rw [execS.eq_1]; exact Hoare.halt' (fun _ h => h.1)
      items := by intros; rw [execItems.eq_1]; exact Hoare.halt' (fun _ h => h.1) }
  | n+1 => {
      stmt := memory_stmt_step calls (memory_body_at calls n)
      items := memory_items_step (memory_body_at calls n) }

#print axioms memory_body_at
end Solidity.Source.Preservation
