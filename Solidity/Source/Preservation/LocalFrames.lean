import Solidity.Source.Preservation.Frames

/-! Reference validity through the actual scope/call-frame packing operations.
These lemmas retain each operation's existing checked failure paths. -/
namespace Solidity.Source.Preservation
open EM
variable {E : Env} {H : HeapTy}

theorem localsDrop_ok : ∀ (k : Nat) {Γ : RCtx} (l : Locals E.layout Γ),
    LocalsOK E H l → LocalsOK E H (l.drop k)
  | 0, _, _, h => h
  | _ + 1, _, .nil, _ => trivial
  | k + 1, _, .cons _ l, h => localsDrop_ok k l h.2

theorem localsCast_ok {Γ Δ : RCtx} (h : Γ = Δ) (l : Locals E.layout Γ)
    (hl : LocalsOK E H l) : LocalsOK E H (h ▸ l) := by subst Δ; exact hl

theorem localsRestore_ok {Γ Δ : RCtx} (l : Locals E.layout Γ) (l' : Locals E.layout Δ)
    (hl : LocalsOK E H l) (hr : l.restore Δ = .ok l') : LocalsOK E H l' := by
  unfold Locals.restore at hr
  split at hr
  next he =>
    cases hr
    exact localsCast_ok he _ (localsDrop_ok _ l hl)
  next he => cases hr

theorem valsOnto_ok : ∀ {ts : List STy} (vs : Vals E.layout ts) {Γ : RCtx} (l : Locals E.layout Γ),
    RValsOK E H vs.toR → LocalsOK E H l → LocalsOK E H (vs.onto l)
  | _, .nil, _, _, _, hl => hl
  | _, .cons v vs, _, l, hv, hl => valsOnto_ok vs (.cons v l) hv.2 ⟨hv.1, hl⟩

theorem localsGetAt_ok : ∀ (k : Nat) {Γ : RCtx} (l : Locals E.layout Γ) (t : STy)
    (v : Val E.layout t), LocalsOK E H l → l.getAt k t = .ok v → v.RefOK E H := by
  intro k Γ l t v hl hr
  induction k generalizing Γ t with
  | zero =>
    cases l with
    | nil => cases hr
    | @cons u us w l =>
      simp only [Locals.getAt] at hr
      split at hr
      next he => subst t; cases hr; exact hl.1
      next he => cases hr
  | succ k ih =>
    cases l with
    | nil => cases hr
    | cons w l => exact ih l t v hl.2 hr

theorem retVals_ok {Γ : RCtx} (l : Locals E.layout Γ) (base : Nat) :
    ∀ (rs : List STy) (out : RVals E.layout rs),
    LocalsOK E H l → retVals l base rs = .ok out → RValsOK E H out := by
  intro rs
  induction rs with
  | nil => intro out hl hr; cases hr; trivial
  | cons t ts ih =>
    intro out hl hr
    simp only [retVals] at hr
    cases hg : l.getAt (base + ts.length) t with
    | error e => simp only [hg] at hr; cases hr
    | ok v =>
      cases ht : retVals l base ts with
      | error e => simp only [hg, ht] at hr; cases hr
      | ok vs =>
        simp only [hg, ht] at hr
        cases hr
        exact ⟨localsGetAt_ok _ l t v hl hg, ih vs hl ht⟩

theorem zeroVals_mem {Γ : RCtx} (n : Nat) : ∀ (ts : List STy) (H : HeapTy),
    Hoare (MemOK E H) (zeroVals n ts : EM E Γ _)
      (fun vs y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR) (fun _ y => MemOK E H y)
  | [], H => Hoare.pure' fun _ h => ⟨h, trivial⟩
  | t :: ts, H => by
    refine Hoare.bind ((zeroOK n).val H t) fun v => ?_
    refine Hoare.bind (Hoare.memGrow (R := fun H' => v.RefOK E H')
      (fun H' => zeroVals_mem n ts H')) fun vs => ?_
    refine Hoare.pure' fun y h => ?_
    rcases h.2.2 with ⟨H', hv, hle⟩
    exact ⟨h.1, Val.RefOK.mono hle hv, h.2.1⟩

#print axioms localsRestore_ok
#print axioms valsOnto_ok
#print axioms retVals_ok
#print axioms zeroVals_mem
end Solidity.Source.Preservation
