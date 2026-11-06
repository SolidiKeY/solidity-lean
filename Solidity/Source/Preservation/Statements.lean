import Solidity.Source.Preservation.StatementFrames

/-! Statement half of joint preservation on the existing call value fragment.
A malformed frame may still halt: this is memory preservation on every outcome,
not a replacement or weakening of the independent progress theorem.
-/
namespace Solidity.Source.Preservation
open EM
variable {E : Env}

structure StmtMemAt (A : Decl → Prop) (G : Glob E) (c : String) (n : Nat) : Prop where
  execS : ∀ F, F.contract = c → ∀ nps ph {R : List STy} {M : Bool} {k : SCtx} {Γ Δ : RCtx}
    (s : RStmt E R M k Γ Δ) (l : Locals E.layout Γ), s.ValFragC A → s.OpsOK → ∀ H,
    Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l) (execS G F n nps ph s l)
      (fun o y => MemOK E H y ∧ OutRefsOK (E := E) y.2.heap.ty o) (fun _ y => MemOK E H y)
  execItems : ∀ F, F.contract = c → ∀ nps ph {R : List STy} {M : Bool} {k : SCtx} {Γ Δ : RCtx}
    (b : RItems E R M k Γ Δ) (l : Locals E.layout Γ), b.ValFragC A → b.OpsOK → ∀ H,
    Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l) (execItems G F n nps ph b l)
      (fun o y => MemOK E H y ∧ OutRefsOK (E := E) y.2.heap.ty o) (fun _ y => MemOK E H y)
  forIter : ∀ F, F.contract = c → ∀ nps ph {R : List STy} {M u : Bool} {Γ Δ : RCtx}
    (cond : ROptBool E Γ) (post : ROptExpr E Γ) (b : RStmt E R M ⟨true, u⟩ Γ Δ)
    (l : Locals E.layout Γ), cond.ValFragC A → cond.OpsOK → post.ValFragC A → post.OpsOK →
    b.ValFragC A → b.OpsOK → ∀ H,
    Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l) (forIter G F n nps ph cond post b l)
      (fun o y => MemOK E H y ∧ OutRefsOK (E := E) y.2.heap.ty o) (fun _ y => MemOK E H y)

section
variable {A : Decl → Prop} {G : Glob E} {c : String} {n : Nat}

theorem execS_memStep (ih : StmtMemAt A G c n)
    (hX : ∀ F, F.contract = c → ExprMemAt A G F n)
    (F : Fr) (hc : F.contract = c) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Δ : RCtx} (s : RStmt E R M k Γ Δ)
    (l : Locals E.layout Γ) (hf : s.ValFragC A) (ho : s.OpsOK) (H : HeapTy) :
    Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l) (execS G F (n + 1) nps ph s l)
      (fun o y => MemOK E H y ∧ OutRefsOK (E := E) y.2.heap.ty o) (fun _ y => MemOK E H y) := by
  have hsub : ∀ {Γ₀ t} (l₀ : Locals E.layout Γ₀) (e : RExpr E Γ₀ t), e.ValFragC A → e.OpsOK →
      Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l₀)
        (sub (Γ := []) l₀ (evalE G F n e))
        (fun r y => MemOK E H y ∧ LocalsOK E y.2.heap.ty r.2) (fun _ y => MemOK E H y) :=
    fun l₀ e hf ho => sub_mem_locals l₀ _ ((hX F hc).val e hf ho)
  have hclose : ∀ {Ξ} (t : RStmt E R M k Γ Ξ) (l₁ : Locals E.layout Γ), t.ValFragC A → t.OpsOK →
      Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l₁)
        (do lift (← execS G F n nps ph t l₁).close)
        (fun o y => MemOK E H y ∧ OutRefsOK (E := E) y.2.heap.ty o) (fun _ y => MemOK E H y) :=
    fun t l₁ hf ho => Hoare.bind (ih.execS F hc nps ph t l₁ hf ho H) fun o => close_mem o H
  cases s with
  | expr e =>
    simp only [execS]
    exact Hoare.bind (hsub l e hf ho) fun _ => Hoare.pure' fun _ h => h
  | declVar t =>
    simp only [execS]
    have hm : MemPres (zeroVal (E := E) (Γ := Γ) n t) := fun H' =>
      Hoare.conseq ((zeroOK n).val H' t) (fun _ h => h) (fun _ _ h => h.1) (fun _ _ h => h)
    exact Hoare.bind (sub_mem_locals l _ hm) fun p => Hoare.pure' fun _ h =>
      ⟨h.1, Val.refOK_of_loc (default_some_loc hf) p.1, h.2⟩
  | declInit e h =>
    simp only [execS]
    have hm := MemPres.bind ((hX F hc).val e hf.1 ho) fun v =>
      MemPres.bind (convRV_pres F n (.inl h) hf.2.2 v) fun w => MemPres.getV' w
    exact Hoare.bind (sub_mem_locals l _ hm) fun p => Hoare.pure' fun _ hi =>
      ⟨hi.1, Val.refOK_of_loc (loc_of_frag (.inl hf.2.1)) p.1, hi.2⟩
  | block b =>
    simp only [execS]
    exact Hoare.bind (ih.execItems F hc nps ph b l hf ho H) fun o => close_mem o H
  | ifThen cond t =>
    simp only [execS]
    refine Hoare.bind (hsub l cond hf.1 ho.1) fun p =>
      Hoare.bind (getV_frame_mem p.2 p.1 H) fun x => ?_
    split
    · exact hclose t p.2 hf.2 ho.2
    · exact Hoare.pure' fun _ h => h
  | ifElse cond t f =>
    simp only [execS]
    refine Hoare.bind (hsub l cond hf.1 ho.1) fun p =>
      Hoare.bind (getV_frame_mem p.2 p.1 H) fun x => ?_
    split
    · exact hclose t p.2 hf.2.1 ho.2.1
    · exact hclose f p.2 hf.2.2 ho.2.2
  | whileLoop cond body =>
    simp only [execS]
    refine Hoare.bind (hsub l cond hf.1 ho.1) fun p =>
      Hoare.bind (getV_frame_mem p.2 p.1 H) fun x => ?_
    split
    · refine Hoare.bind (ih.execS F hc nps ph body p.2 hf.2 ho.2 H) fun o => ?_
      cases o with
      | normal l2 => exact Hoare.bind (restore_mem l2 H) fun l3 => ih.execS F hc nps ph _ l3 hf ho H
      | cont l2 => exact ih.execS F hc nps ph _ l2 hf ho H
      | brk l2 => exact Hoare.pure' fun _ h => h
      | ret l2 => exact Hoare.pure' fun _ h => h
    · exact Hoare.pure' fun _ h => h
  | @doWhile lp u0 _ _ body cond =>
    simp only [execS]
    have tail : ∀ l₂ : Locals E.layout Γ,
        Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l₂)
          (do let p ← sub l₂ (evalE G F n cond)
              match ← getV p.1 with
              | .bool true => execS G F n nps ph (body.doWhile (l := lp) cond) p.2
              | _ => pure (.normal p.2))
          (fun o y => MemOK E H y ∧ OutRefsOK (E := E) y.2.heap.ty o) (fun _ y => MemOK E H y) := by
      intro l₂
      refine Hoare.bind (hsub l₂ cond hf.2 ho.2) fun p =>
        Hoare.bind (getV_frame_mem p.2 p.1 H) fun x => ?_
      split
      · exact ih.execS F hc nps ph _ p.2 hf ho H
      · exact Hoare.pure' fun _ h => h
    refine Hoare.bind (ih.execS F hc nps ph body l hf.1 ho.1 H) fun o => ?_
    cases o with
    | normal l2 => exact Hoare.bind (restore_mem l2 H) tail
    | cont l2 => exact Hoare.bind (Hoare.pure' fun _ h => h) tail
    | brk l2 => exact Hoare.pure' fun _ h => h
    | ret l2 => exact Hoare.pure' fun _ h => h
  | forLoop init cond post body =>
    simp only [execS]
    refine Hoare.bind (ih.execS F hc nps ph init l hf.2.1 ho.1 H) fun o => ?_
    cases o with
    | normal l1 =>
      refine Hoare.bind (ih.forIter F hc nps ph cond post body l1 hf.2.2.1 ho.2.1
        hf.2.2.2.1 ho.2.2.1 hf.2.2.2.2 ho.2.2.2 H) fun o2 => ?_
      cases o2 with
      | normal l2 => exact Hoare.bind (restore_mem l2 H) fun l3 => Hoare.pure' fun _ h => h
      | ret l2 => exact Hoare.bind (restore_mem l2 H) fun l3 => Hoare.pure' fun _ h => h
      | brk _ => exact Hoare.halt' fun _ h => h.1
      | cont _ => exact Hoare.halt' fun _ h => h.1
    | brk _ => exact Hoare.halt' fun _ h => h.1
    | cont _ => exact Hoare.halt' fun _ h => h.1
    | ret _ => exact Hoare.halt' fun _ h => h.1
  | skip => exact Hoare.pure' fun _ h => h
  | brk => exact Hoare.pure' fun _ h => h
  | cont => exact Hoare.pure' fun _ h => h
  | ret _ => exact Hoare.pure' fun _ h => h
  | @retVal _ _ s t hR e h =>
    simp only [execS]
    have hm := MemPres.bind ((hX F hc).val e hf.1 ho) fun v =>
      MemPres.bind (convRV_pres F n (.inl h) hf.2.2 v) fun w => MemPres.getV' w
    exact Hoare.bind (sub_mem_locals l _ hm) fun p =>
      Hoare.bind (setAt_value_mem p.2 _ p.1 (loc_of_frag (.inl hf.2.1)) H) fun _ => Hoare.pure' fun _ h => h
  | retTuple es =>
    simp only [execS]
    exact Hoare.bind (sub_mem_locals l _ ((hX F hc).convArgs es hf ho)) fun p =>
      Hoare.bind (setRets_value_mem p.2 _ p.1 (args_value_types es hf) H) fun _ => Hoare.pure' fun _ h => h
  | _ => exact hf.elim

theorem execItems_memStep (ih : StmtMemAt A G c n)
    (F : Fr) (hc : F.contract = c) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Δ : RCtx} (b : RItems E R M k Γ Δ)
    (l : Locals E.layout Γ) (hf : b.ValFragC A) (ho : b.OpsOK) (H : HeapTy) :
    Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l) (execItems G F (n + 1) nps ph b l)
      (fun o y => MemOK E H y ∧ OutRefsOK (E := E) y.2.heap.ty o) (fun _ y => MemOK E H y) := by
  cases b with
  | nil => exact Hoare.pure' fun _ h => h
  | stmt t rest =>
    simp only [execItems]
    refine Hoare.bind (ih.execS F hc nps ph t l hf.1 ho.1 H) fun o => ?_
    cases o with
    | normal l1 => exact Hoare.bind (ih.execItems F hc nps ph rest l1 hf.2 ho.2 H) fun o' => up_mem o' H
    | brk _ => exact Hoare.pure' fun _ h => h
    | cont _ => exact Hoare.pure' fun _ h => h
    | ret _ => exact Hoare.pure' fun _ h => h
  | unchecked inner rest =>
    simp only [execItems]
    refine Hoare.bind (ih.execItems {F with checked := false} hc nps ph inner l hf.1 ho.1 H) fun o => ?_
    cases o with
    | normal l1 => exact Hoare.bind (restore_mem l1 H) fun l2 => ih.execItems F hc nps ph rest l2 hf.2 ho.2 H
    | brk _ => exact Hoare.pure' fun _ h => h
    | cont _ => exact Hoare.pure' fun _ h => h
    | ret _ => exact Hoare.pure' fun _ h => h

theorem forIter_memStep (ih : StmtMemAt A G c n)
    (hX : ∀ F, F.contract = c → ExprMemAt A G F n)
    (F : Fr) (hF : F.contract = c) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M u : Bool} {Γ Δ : RCtx} (cond : ROptBool E Γ) (post : ROptExpr E Γ)
    (body : RStmt E R M ⟨true, u⟩ Γ Δ) (l : Locals E.layout Γ)
    (hc : cond.ValFragC A) (hc' : cond.OpsOK) (hp : post.ValFragC A) (hp' : post.OpsOK)
    (hb : body.ValFragC A) (hb' : body.OpsOK) (H : HeapTy) :
    Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l) (forIter G F (n + 1) nps ph cond post body l)
      (fun o y => MemOK E H y ∧ OutRefsOK (E := E) y.2.heap.ty o) (fun _ y => MemOK E H y) := by
  have hnext : ∀ l₂ : Locals E.layout Γ,
      Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l₂)
        (do let l3 ← match post with
              | .none => pure l₂
              | .some pe => do pure (← sub l₂ (evalE G F n pe)).2
            forIter G F n nps ph cond post body l3)
        (fun o y => MemOK E H y ∧ OutRefsOK (E := E) y.2.heap.ty o) (fun _ y => MemOK E H y) := by
    intro l₂
    cases post with
    | none =>
      simp only [pure_bind]
      exact ih.forIter F hF nps ph _ _ body l₂ hc hc' hp hp' hb hb' H
    | some pe =>
      simp only [pure_bind]
      exact Hoare.bind (sub_mem_locals l₂ _ ((hX F hF).val pe hp.1 hp')) fun p =>
        ih.forIter F hF nps ph _ _ body p.2 hc hc' hp hp' hb hb' H
  have hbody : ∀ l₁ : Locals E.layout Γ,
      Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l₁)
        (do let l2 ← match ← execS G F n nps ph body l₁ with
              | .normal l2 => lift (l2.restore _)
              | .cont l2 => pure l2
              | .brk l2 => return .normal l2
              | .ret l2 => return .ret l2
            let l3 ← match post with
              | .none => pure l2
              | .some pe => do pure (← sub l2 (evalE G F n pe)).2
            forIter G F n nps ph cond post body l3)
        (fun o y => MemOK E H y ∧ OutRefsOK (E := E) y.2.heap.ty o) (fun _ y => MemOK E H y) := by
    intro l₁
    refine Hoare.bind (ih.execS F hF nps ph body l₁ hb hb' H) fun o => ?_
    cases o with
    | normal l2 => exact Hoare.bind (restore_mem l2 H) hnext
    | cont l2 => exact Hoare.bind (Hoare.pure' fun _ h => h) hnext
    | brk l2 => exact Hoare.pure' fun _ h => h
    | ret l2 => exact Hoare.pure' fun _ h => h
  simp only [forIter]
  cases cond with
  | none =>
    refine Hoare.bind (Hoare.pure' (a := (true, l))
      (Q := fun p y => MemOK E H y ∧ LocalsOK E y.2.heap.ty p.2) (fun _ h => h)) fun y => ?_
    split
    · exact Hoare.pure' fun _ h => h
    · exact Hoare.bind (Hoare.pure' fun _ h => h) fun _ => hbody y.2
  | some ce =>
    refine Hoare.bind (sub_mem_locals l _ ((hX F hF).val ce hc hc')) fun p =>
      Hoare.bind (getV_frame_mem p.2 p.1 H) fun x => ?_
    obtain ⟨b, rfl⟩ := Val.eq_bool x
    refine Hoare.bind (Hoare.pure' (a := (b, p.2))
      (Q := fun q y => MemOK E H y ∧ LocalsOK E y.2.heap.ty q.2) (fun _ h => h)) fun y => ?_
    split
    · exact Hoare.pure' fun _ h => h
    · exact Hoare.bind (Hoare.pure' fun _ h => h) fun _ => hbody y.2

end

theorem stmtMemAt_zero (A : Decl → Prop) (G : Glob E) (c : String) : StmtMemAt A G c 0 where
  execS := by intros; rw [execS.eq_1]; exact Hoare.halt' fun _ h => h.1
  execItems := by intros; rw [execItems.eq_1]; exact Hoare.halt' fun _ h => h.1
  forIter := by intros; rw [forIter.eq_1]; exact Hoare.halt' fun _ h => h.1

theorem stmtMemAt_step {A : Decl → Prop} {G : Glob E} {c : String} {n : Nat}
    (ih : StmtMemAt A G c n) (hx : ∀ F, F.contract = c → ExprMemAt A G F n) : StmtMemAt A G c (n + 1) where
  execS := execS_memStep ih hx
  execItems := execItems_memStep ih
  forIter := forIter_memStep ih hx

#print axioms execS_memStep
#print axioms stmtMemAt_step
end Solidity.Source.Preservation
