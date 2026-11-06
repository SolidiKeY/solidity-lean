import Solidity.Source.Preservation.Expressions

/-! Actual scope and return-slot operations for the statement Hoare induction. -/
namespace Solidity.Source.Preservation
open EM
variable {E : Env} {H : HeapTy}

theorem localsSetAt_ok : ∀ (k : Nat) {Γ : RCtx} (l : Locals E.layout Γ) {t : STy}
    (v : Val E.layout t) (l' : Locals E.layout Γ),
    LocalsOK E H l → v.RefOK E H → l.setAt k v = .ok l' → LocalsOK E H l' := by
  intro k Γ l t v l' hl hv hr
  induction k generalizing Γ with
  | zero =>
    cases l with
    | nil => cases hr
    | @cons s ss w l =>
      simp only [Locals.setAt] at hr
      split at hr
      next he => subst s; cases hr; exact ⟨hv, hl.2⟩
      next he => cases hr
  | succ k ih =>
    cases l with
    | nil => cases hr
    | cons w l =>
      simp only [Locals.setAt] at hr
      cases hs : l.setAt k v with
      | error e => simp only [hs] at hr; cases hr
      | ok l'' =>
        simp only [hs] at hr
        cases hr
        exact ⟨hl.1, ih l l'' hl.2 hs⟩

theorem setRets_ok : ∀ {Γ : RCtx} (l : Locals E.layout Γ) (base : Nat)
    {rs : List STy} (vs : Vals E.layout rs) (l' : Locals E.layout Γ),
    LocalsOK E H l → RValsOK E H vs.toR → setRets l base vs = .ok l' → LocalsOK E H l'
  | _, l, base, _, .nil, l', hl, _, hr => by cases hr; exact hl
  | _, l, base, _, .cons (τs := ts) v vs, l', hl, hv, hr => by
    simp only [setRets] at hr
    cases hs : l.setAt (base + ts.length) v with
    | error e => simp only [hs] at hr; cases hr
    | ok l'' =>
      simp only [hs] at hr
      exact setRets_ok l'' base vs l' (localsSetAt_ok _ l v l'' hl hv.1 hs) hv.2 hr

theorem outClose_ok {Γ Δ : RCtx} (o : Out E.layout Γ Δ) (o' : Out E.layout Γ Γ)
    (hl : OutRefsOK (E := E) H o) (hr : o.close = .ok o') : OutRefsOK (E := E) H o' := by
  cases o with
  | normal l =>
    simp only [Out.close] at hr
    cases hs : l.restore Γ with
    | error e => simp only [hs] at hr; cases hr
    | ok l' => simp only [hs] at hr; cases hr; exact localsRestore_ok l l' hl hs
  | brk l => cases hr; exact hl
  | cont l => cases hr; exact hl
  | ret l => cases hr; exact hl

theorem outUp_ok {Γ Δ Ξ : RCtx} (o : Out E.layout Γ Δ) (o' : Out E.layout Ξ Δ)
    (hl : OutRefsOK (E := E) H o) (hr : o.up Ξ = .ok o') : OutRefsOK (E := E) H o' := by
  cases o with
  | normal l => cases hr; exact hl
  | brk l =>
    simp only [Out.up] at hr
    cases hs : l.restore Ξ with
    | error e => simp only [hs] at hr; cases hr
    | ok l' => simp only [hs] at hr; cases hr; exact localsRestore_ok l l' hl hs
  | cont l =>
    simp only [Out.up] at hr
    cases hs : l.restore Ξ with
    | error e => simp only [hs] at hr; cases hr
    | ok l' => simp only [hs] at hr; cases hr; exact localsRestore_ok l l' hl hs
  | ret l =>
    simp only [Out.up] at hr
    cases hs : l.restore Ξ with
    | error e => simp only [hs] at hr; cases hr
    | ok l' => simp only [hs] at hr; cases hr; exact localsRestore_ok l l' hl hs

theorem sub_mem_locals {Γ Δ : RCtx} {α : Type} (l' : Locals E.layout Δ) (m : EM E Δ α)
    (hm : MemPres m) :
    Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l')
      (sub l' m : EM E Γ (α × Locals E.layout Δ))
      (fun r y => MemOK E H y ∧ LocalsOK E y.2.heap.ty r.2)
      (fun _ y => MemOK E H y) := by
  intro ⟨l, s⟩ ⟨ho, hi⟩
  have hrun := hm s.heap.ty (l', s) (relocalize ho.self l' hi)
  unfold EM.sub
  rcases he : m.run (l', s) with ⟨r, ⟨l'', s'⟩⟩
  rw [he] at hrun
  have finish (h : MemOK E s.heap.ty (l'', s')) : MemOK E H (l, s') :=
    relocalize (h.weaken ho.le) l (LocalsOK.mono h.le l ho.1.2)
  have he' : m (l', s) = (r, (l'', s')) := he
  cases r with
  | ok a => simp only [ExceptT.run, ExceptT.mk, he']; exact ⟨finish hrun, hrun.1.2⟩
  | error e => simp only [ExceptT.run, ExceptT.mk, he']; exact finish hrun

theorem lift_keep {Γ : RCtx} {α : Type} (P : EMState E Γ → Prop) (r : R α) :
    Hoare P (lift r) (fun _ y => P y) (fun _ y => P y) :=
  Hoare.lift' fun _ h => by cases r <;> exact h

theorem getV_keep {Γ : RCtx} {t : STy} (P : EMState E Γ → Prop) (v : RVal E.layout t) :
    Hoare P (getV v) (fun _ y => P y) (fun _ y => P y) := lift_keep P v.get

theorem getV_frame_mem {Γ Δ : RCtx} {t : STy} (l : Locals E.layout Δ)
    (v : RVal E.layout t) (H : HeapTy) :
    Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l)
      (getV v : EM E Γ _) (fun _ y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l)
      (fun _ y => MemOK E H y) :=
  Hoare.conseq (getV_keep _ v) (fun _ h => h) (fun _ _ h => h) (fun _ _ h => h.1)

theorem restore_mem {Γ Δ : RCtx} (l : Locals E.layout Γ) (H : HeapTy) :
    Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l)
      (lift (l.restore Δ) : EM E [] _)
      (fun l' y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l') (fun _ y => MemOK E H y) := by
  refine Hoare.lift' fun y h => ?_
  cases hr : l.restore Δ with
  | error e => exact h.1
  | ok l' => exact ⟨h.1, localsRestore_ok l l' h.2 hr⟩

theorem close_mem {Γ Δ : RCtx} (o : Out E.layout Γ Δ) (H : HeapTy) :
    Hoare (fun y => MemOK E H y ∧ OutRefsOK (E := E) y.2.heap.ty o)
      (lift o.close : EM E [] _)
      (fun o' y => MemOK E H y ∧ OutRefsOK (E := E) y.2.heap.ty o') (fun _ y => MemOK E H y) := by
  refine Hoare.lift' fun y h => ?_
  cases hr : o.close with
  | error e => exact h.1
  | ok o' => exact ⟨h.1, outClose_ok o o' h.2 hr⟩

theorem up_mem {Γ Δ Ξ : RCtx} (o : Out E.layout Γ Δ) (H : HeapTy) :
    Hoare (fun y => MemOK E H y ∧ OutRefsOK (E := E) y.2.heap.ty o)
      (lift (o.up Ξ) : EM E [] _)
      (fun o' y => MemOK E H y ∧ OutRefsOK (E := E) y.2.heap.ty o') (fun _ y => MemOK E H y) := by
  refine Hoare.lift' fun y h => ?_
  cases hr : o.up Ξ with
  | error e => exact h.1
  | ok o' => exact ⟨h.1, outUp_ok o o' h.2 hr⟩

theorem setAt_value_mem {Γ : RCtx} {t : STy} (l : Locals E.layout Γ)
    (k : Nat) (v : Val E.layout t) (ht : t.loc? = none) (H : HeapTy) :
    Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l)
      (lift (l.setAt k v) : EM E [] _)
      (fun l' y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l') (fun _ y => MemOK E H y) := by
  refine Hoare.lift' fun y h => ?_
  cases hr : l.setAt k v with
  | error e => exact h.1
  | ok l' => exact ⟨h.1, localsSetAt_ok k l v l' h.2 (Val.refOK_of_loc ht v) hr⟩

theorem setRets_value_mem {Γ : RCtx} {rs : List STy} (l : Locals E.layout Γ)
    (k : Nat) (vs : Vals E.layout rs) (ht : rs.all STy.isValue = true) (H : HeapTy) :
    Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l)
      (lift (setRets l k vs) : EM E [] _)
      (fun l' y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l') (fun _ y => MemOK E H y) := by
  refine Hoare.lift' fun y h => ?_
  cases hr : setRets l k vs with
  | error e => exact h.1
  | ok l' => exact ⟨h.1, setRets_ok l k vs l' h.2 (vals_value_refs _ vs ht) hr⟩

theorem default_some_loc {t : STy} (h : (Val.default E.layout t).isSome = true) : t.loc? = none := by
  cases hr : Val.default E.layout t with
  | none => rw [hr] at h; cases h
  | some v => exact Val.default_loc hr

#print axioms sub_mem_locals
#print axioms localsSetAt_ok
#print axioms setRets_ok
end Solidity.Source.Preservation
