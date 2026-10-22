import Solidity.Calculus.RunFrameMem

/-!
# A body that writes only into its own objects

`Calculus/RunFrameMem.lean`'s frame is for a body that allocates but writes
no object (`Stmt.withinM`).  A memory return's callee commonly fills the
object it returns (`p.age = 7`, `r[i] = v`): such a write keeps the
caller's objects where it reaches none of them, the run invariant of
`docs/kernel-port.md` ("Recursion", "What is left", step 1).

**The invariant** (`Own b`): every memory reference a local of the callee's
frame holds, and every reference inside an object at or above the identity
`b` (the caller's heap length where the callee is entered), is at or above
`b`.  The callee's frame starts so (its parameters hold no memory reference,
`Args.memFree`; its return object is fresh); an allocation keeps it (a copy
refers to the objects it allocates, `SVal.ownNew_copyStToM`); a read through
a path reads an own object (`MPath.mvalT_own`); a write writes an own object
(`Heap.writeAddr_own`), so every object below `b` is kept
(`Heap.KeepsBelow`): at the frame's exit, every object of the caller.
-/

namespace Solidity

open Solidity (Mutability)
open Semantics (structDef)

variable {C : Contract}

/-! ## Own values, objects and heaps -/

section Own

variable {H H' : HTy}

/-- A slot at or above `b`: a word, or a reference to an object at or above
`b`. -/
def MVal.Own (b : Nat) : (T : Ty) → MVal H T → Prop
  | .prim _, _ => True
  | .ref _, r => b ≤ (r : HRef H _).id

/-- Every member at or above `b`. -/
def MFields.Own (b : Nat) : (fs : List (Name × Ty)) → MFields H fs → Prop
  | [], _ => True
  | (_, T) :: fs, x => MVal.Own b T x.1 ∧ MFields.Own b fs x.2

/-- Every slot of the object at or above `b`. -/
def MObj.Own (b : Nat) : (R : RefTy) → MObj H R → Prop
  | .struct s, o => MFields.Own b (structDef s) o
  | .array E, o => ∀ v ∈ (o : {l : List (MVal H E) // l.length < 2 ^ 256}).1, MVal.Own b E v
  | .fixed E n, o => ∀ v ∈ (o : {l : List (MVal H E) // l.length = n}).1, MVal.Own b E v
  | .mapping _ _, _ => True

/-- Every object at or above `b` holds slots at or above `b`. -/
def Heap.OwnAbove (b : Nat) (hp : Heap H) : Prop :=
  ∀ {R : RefTy} (r : HRef H R), b ≤ r.id → MObj.Own b R (hp.get r)

/-- `hp'` keeps every object of `hp` below `b`. -/
def Heap.KeepsBelow (b : Nat) (e : H <+: H') (hp : Heap H) (hp' : Heap H') : Prop :=
  ∀ {R : RefTy} (r : HRef H R), r.id < b → hp'.get (r.wk e) = MObj.wk e R (hp.get r)

/-- Every memory local holds a reference at or above `b`, or none. -/
def TEnv.Own (b : Nat) {Γ : Ctx} (e : TEnv C H Γ) : Prop :=
  ∀ {R : RefTy} (i : Idx Γ (.mem R)) (r : HRef H R), TEnv.get i e = some r → b ≤ r.id

theorem MVal.Own.mono {b b' : Nat} (hb : b ≤ b') : {T : Ty} → {v : MVal H T} →
    MVal.Own b' T v → MVal.Own b T v
  | .prim _, _, _ => trivial
  | .ref _, _, h => Nat.le_trans hb h

theorem MFields.Own.mono {b b' : Nat} (hb : b ≤ b') : {fs : List (Name × Ty)} →
    {x : MFields H fs} → MFields.Own b' fs x → MFields.Own b fs x
  | [], _, _ => trivial
  | (_, _) :: _, _, h => ⟨MVal.Own.mono hb h.1, MFields.Own.mono hb h.2⟩

theorem MObj.Own.mono {b b' : Nat} (hb : b ≤ b') : {R : RefTy} → {o : MObj H R} →
    MObj.Own b' R o → MObj.Own b R o
  | .struct _, _, h => MFields.Own.mono hb h
  | .array _, _, h => fun v hv => MVal.Own.mono hb (h v hv)
  | .fixed _ _, _, h => fun v hv => MVal.Own.mono hb (h v hv)
  | .mapping _ _, _, _ => trivial

theorem MVal.own_wk (e : H <+: H') {b : Nat} : (T : Ty) → (v : MVal H T) →
    MVal.Own b T (MVal.wk e T v) ↔ MVal.Own b T v
  | .prim _, _ => Iff.rfl
  | .ref _, _ => Iff.rfl

theorem MFields.own_wk (e : H <+: H') {b : Nat} : (fs : List (Name × Ty)) → (x : MFields H fs) →
    MFields.Own b fs (MFields.wk e fs x) ↔ MFields.Own b fs x
  | [], _ => Iff.rfl
  | (_, T) :: fs, x => and_congr (MVal.own_wk e T x.1) (MFields.own_wk e fs x.2)

theorem MObj.own_wk (e : H <+: H') {b : Nat} : (R : RefTy) → (o : MObj H R) →
    MObj.Own b R (MObj.wk e R o) ↔ MObj.Own b R o
  | .struct s, o => MFields.own_wk e (structDef s) o
  | .array E, o => by
    show (∀ v ∈ (o.1.map (MVal.wk e E)), MVal.Own b E v) ↔ ∀ v ∈ o.1, MVal.Own b E v
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      MVal.own_wk]
  | .fixed E n, o => by
    show (∀ v ∈ (o.1.map (MVal.wk e E)), MVal.Own b E v) ↔ ∀ v ∈ o.1, MVal.Own b E v
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      MVal.own_wk]
  | .mapping _ _, o => (o : Empty).elim

theorem Heap.KeepsBelow.refl {b : Nat} (hp : Heap H) :
    Heap.KeepsBelow b (List.prefix_refl H) hp hp :=
  fun r _ => (MObj.wk_refl _ (hp.get r)).symm

theorem Heap.KeepsBelow.trans {b : Nat} {H₂ : HTy} {e₁ : H <+: H'} {e₂ : H' <+: H₂}
    {e : H <+: H₂} {hp : Heap H} {hp₁ : Heap H'} {hp₂ : Heap H₂}
    (h₁ : Heap.KeepsBelow b e₁ hp hp₁) (h₂ : Heap.KeepsBelow b e₂ hp₁ hp₂) :
    Heap.KeepsBelow b e hp hp₂ := fun r hr => by
  show hp₂.get ((r.wk e₁).wk e₂) = _
  rw [h₂ (r.wk e₁) hr, h₁ r hr, MObj.wk_wk]

theorem Heap.Keeps.keepsBelow {b : Nat} {e : H <+: H'} {hp : Heap H} {hp' : Heap H'}
    (h : Heap.Keeps e hp hp') : Heap.KeepsBelow b e hp hp' := fun r _ => h r

/-- Everything below the heap's length kept: every object kept. -/
theorem Heap.KeepsBelow.keeps {e : H <+: H'} {hp : Heap H} {hp' : Heap H'}
    (h : Heap.KeepsBelow H.length e hp hp') : Heap.Keeps e hp hp' := fun r =>
  h r r.id_lt

end Own

/-! ## Allocations refer to what they allocate -/

section Alloc

variable {H H₁ H₂ : HTy}

/-- A reference into a grown heap below the old length: one of the old heap. -/
def HRef.unwk {R : RefTy} (e : H <+: H₁) (r : HRef H₁ R) (h : r.id < H.length) : HRef H R :=
  ⟨r.id, by
    obtain ⟨t, rfl⟩ := e
    have := r.get?
    rwa [List.getElem?_append_left h] at this⟩

theorem HRef.unwk_wk {R : RefTy} (e : H <+: H₁) (r : HRef H₁ R) (h : r.id < H.length) :
    (r.unwk e h).wk e = r := rfl

/-- The objects of `hp` from `H.length` on hold slots at or above `b`. -/
def Heap.OwnFrom (b : Nat) (H : HTy) (hp : Heap H₁) : Prop :=
  ∀ {R : RefTy} (r : HRef H₁ R), H.length ≤ r.id → MObj.Own b R (hp.get r)

/-- Grown along `e₂` keeping the objects, a heap whose new objects (from
`H₁`) and older ones (from `H`) are own is own from `H`. -/
theorem Heap.OwnFrom.trans {b : Nat} {e₂ : H₁ <+: H₂} {hp₁ : Heap H₁}
    {hp₂ : Heap H₂} (hk : Heap.Keeps e₂ hp₁ hp₂) (h₁ : Heap.OwnFrom b H hp₁)
    (h₂ : Heap.OwnFrom b H₁ hp₂) : Heap.OwnFrom b H hp₂ := fun r hr => by
  by_cases hlt : r.id < H₁.length
  · rw [← HRef.unwk_wk e₂ r hlt, hk, MObj.own_wk]
    exact h₁ _ hr
  · exact h₂ r (Nat.le_of_not_lt hlt)

/-- An allocation of an own object keeps the heap own from where it was. -/
theorem Heap.ownFrom_alloc {b : Nat} {R : RefTy} (hp : Heap H₁) (o : MObj H₁ R)
    (hh : Heap.OwnFrom b H hp) (ho : MObj.Own b R o) (hH : H.length ≤ H₁.length) :
    Heap.OwnFrom b H (hp.alloc o).1 := fun {R'} r hr => by
  by_cases hlt : r.id < H₁.length
  · rw [← HRef.unwk_wk (List.prefix_append H₁ [R]) r hlt, Heap.keeps_alloc, MObj.own_wk]
    exact hh _ hr
  · have hid : r.id = (hp.alloc o).2.id := by
      have := r.id_lt
      simp only [List.length_append, List.length_singleton] at this
      show r.id = H₁.length
      omega
    obtain ⟨rfl, hq⟩ := HRef.heq_of_id r (hp.alloc o).2 hid
    cases hq
    rw [Heap.get_alloc, MObj.own_wk]
    exact ho

theorem Heap.ownFrom_self {b : Nat} (hp : Heap H) : Heap.OwnFrom b H hp := fun r hr =>
  absurd r.id_lt (Nat.not_lt_of_le hr)

theorem Grown.ownFrom_alloc {b : Nat} {R : RefTy} {hp : Heap H} (g : Grown H (MObj · R))
    (hh : Heap.OwnFrom b H g.heap) (ho : MObj.Own b R g.val) :
    Heap.OwnFrom b H (Grown.alloc g).heap :=
  Heap.ownFrom_alloc g.heap g.val hh ho (List.IsPrefix.length_le g.ext)

theorem Grown.alloc_val_own {R : RefTy} (g : Grown H (MObj · R)) :
    MVal.Own H.length (.ref R) (Grown.alloc g).val :=
  List.IsPrefix.length_le g.ext

mutual
/-- **A copy into memory refers to what it allocates**: its new objects and
its value hold slots at or above the heap's old length. -/
theorem SVal.own_copyStToM : {T : Ty} → (v : SVal T) → (h : T.mapFree = true) →
    {H : HTy} → (hp : Heap H) →
      Heap.OwnFrom H.length H (v.copyStToM hp h).heap ∧
        MVal.Own H.length T (v.copyStToM hp h).val
  | _, .prim _, _, _, hp => by
    rw [SVal.copyStToM_prim]
    exact ⟨Heap.ownFrom_self hp, trivial⟩
  | _, .struct fs, h, _, hp => by
    rw [SVal.copyStToM_struct]
    have ih := SFields.own_copyStToM fs
      (mapFree_structDef _ (by simpa only [Ty.mapFree, decide_eq_true_eq] using h)) hp
    refine ⟨Grown.ownFrom_alloc (hp := hp) _ ?_ ?_, Grown.alloc_val_own _⟩
    · exact ih.1
    · exact ih.2
  | _, .array e _ _, h, _, hp => by
    rw [SVal.copyStToM_array]
    dsimp only
    have ih := SVec.own_copyStToM e (by simpa only [Ty.mapFree] using h) hp
    refine ⟨Grown.ownFrom_alloc (hp := hp) _ ?_ ?_, Grown.alloc_val_own _⟩
    · exact ih.1
    · exact ih.2
  | _, .fixed e, h, _, hp => by
    rw [SVal.copyStToM_fixed]
    have ih := SVec.own_copyStToM e (by simpa only [Ty.mapFree] using h) hp
    refine ⟨Grown.ownFrom_alloc (hp := hp) _ ?_ ?_, Grown.alloc_val_own _⟩
    · exact ih.1
    · exact ih.2
  | _, .map _ _, h, _, _ => by simp only [Ty.mapFree, Bool.false_eq_true] at h

theorem SFields.own_copyStToM : {fs : List (Name × Ty)} → (x : SFields fs) →
    (h : ∀ fT ∈ fs, fT.2.mapFree = true) → {H : HTy} → (hp : Heap H) →
      Heap.OwnFrom H.length H (x.copyStToM hp h).heap ∧
        MFields.Own H.length fs (x.copyStToM hp h).val
  | _, .nil, _, _, hp => by
    rw [SFields.copyStToM_nil]
    exact ⟨Heap.ownFrom_self hp, trivial⟩
  | _, .cons v rest, h, _, hp => by
    rw [SFields.copyStToM_cons]
    dsimp only
    have i₁ := SVal.own_copyStToM v (h _ List.mem_cons_self) hp
    have i₂ := SFields.own_copyStToM rest (fun fT hm => h fT (List.mem_cons_of_mem _ hm))
      (v.copyStToM hp (h _ List.mem_cons_self)).heap
    have hl := List.IsPrefix.length_le (v.copyStToM hp (h _ List.mem_cons_self)).ext
    refine ⟨Heap.OwnFrom.trans (SFields.keeps_copyStToM rest _ _) i₁.1 ?_, ?_, ?_⟩
    · exact fun r hr => MObj.Own.mono hl (i₂.1 r hr)
    · exact (MVal.own_wk _ _ _).2 i₁.2
    · exact MFields.Own.mono hl i₂.2

theorem SList.own_copyStToM : {E : Ty} → (l : SList E) → (h : E.mapFree = true) →
    {H : HTy} → (hp : Heap H) →
      Heap.OwnFrom H.length H (l.copyStToM hp h).heap ∧
        ∀ w ∈ (l.copyStToM hp h).val, MVal.Own H.length E w
  | _, .nil, _, _, hp => by
    rw [SList.copyStToM_nil]
    exact ⟨Heap.ownFrom_self hp, fun _ h => nomatch h⟩
  | _, .cons v rest, h, _, hp => by
    rw [SList.copyStToM_cons]
    dsimp only
    have i₁ := SVal.own_copyStToM v h hp
    have i₂ := SList.own_copyStToM rest h (v.copyStToM hp h).heap
    have hl := List.IsPrefix.length_le (v.copyStToM hp h).ext
    refine ⟨Heap.OwnFrom.trans (SList.keeps_copyStToM rest h _) i₁.1 ?_, ?_⟩
    · exact fun r hr => MObj.Own.mono hl (i₂.1 r hr)
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact (MVal.own_wk _ _ _).2 i₁.2
    · exact MVal.Own.mono hl (i₂.2 w hw)

theorem SVec.own_copyStToM : {E : Ty} → {n : Nat} → (l : SVec E n) → (h : E.mapFree = true) →
    {H : HTy} → (hp : Heap H) →
      Heap.OwnFrom H.length H (l.copyStToM hp h).heap ∧
        ∀ w ∈ (l.copyStToM hp h).val.1, MVal.Own H.length E w
  | _, _, .nil, _, _, hp => by
    rw [SVec.copyStToM_nil]
    exact ⟨Heap.ownFrom_self hp, fun _ h => nomatch h⟩
  | _, _, .cons v rest, h, _, hp => by
    rw [SVec.copyStToM_cons]
    dsimp only
    have i₁ := SVal.own_copyStToM v h hp
    have i₂ := SVec.own_copyStToM rest h (v.copyStToM hp h).heap
    have hl := List.IsPrefix.length_le (v.copyStToM hp h).ext
    refine ⟨Heap.OwnFrom.trans (SVec.keeps_copyStToM rest h _) i₁.1 ?_, ?_⟩
    · exact fun r hr => MObj.Own.mono hl (i₂.1 r hr)
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact (MVal.own_wk _ _ _).2 i₁.2
    · exact MVal.Own.mono hl (i₂.2 w hw)
end

end Alloc

/-! ## Reads and writes of own objects -/

section ReadWrite

variable {H H' : HTy}

theorem MFields.get_own {b : Nat} {f : Name} : (fs : List (Name × Ty)) → {T : Ty} →
    (x : MFields H fs) → (h : Semantics.lookupBy f fs = some T) → MFields.Own b fs x →
      MVal.Own b T (MFields.get fs x h)
  | [], _, _, h, _ => absurd h (by simp only [Semantics.lookupBy, reduceCtorEq, not_false_eq_true])
  | (f', T') :: fs, T, x, h, hx => by
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      simp only [MFields.get, e, dite_true]
      exact hx.1
    · simp only [MFields.get, e, dite_false]
      exact MFields.get_own fs x.2 _ hx.2

theorem MFields.set_own {b : Nat} {f : Name} : (fs : List (Name × Ty)) → {T : Ty} →
    (x : MFields H fs) → (h : Semantics.lookupBy f fs = some T) → (v : MVal H T) →
    MFields.Own b fs x → MVal.Own b T v → MFields.Own b fs (MFields.set fs x h v)
  | [], _, _, _, _, hx, _ => hx
  | (f', T') :: fs, T, x, h, v, hx, hv => by
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      simp only [MFields.set, e, dite_true]
      exact ⟨hv, hx.2⟩
    · simp only [MFields.set, e, dite_false]
      exact ⟨hx.1, MFields.set_own fs x.2 _ v hx.2 hv⟩

theorem MObj.elems_own {b : Nat} {R : RefTy} {E : Ty} (a : ArrTy R E) (o : MObj H R)
    (ho : MObj.Own b R o) : ∀ v ∈ MObj.elems a o, MVal.Own b E v := by
  cases a with
  | dyn => rw [MObj.elems_dyn]; exact ho
  | fixed => rw [MObj.elems_fixed]; exact ho

theorem MObj.setElem_own {b : Nat} {R : RefTy} {E : Ty} (a : ArrTy R E) (o : MObj H R) (i : Nat)
    (v : MVal H E) (ho : MObj.Own b R o) (hv : MVal.Own b E v) :
    MObj.Own b R (MObj.setElem a o i v) := by
  cases a with
  | dyn =>
    rw [MObj.setElem_dyn]
    intro w hw
    rcases List.mem_or_eq_of_mem_set hw with hw | rfl
    · exact ho w hw
    · exact hv
  | fixed =>
    rw [MObj.setElem_fixed]
    intro w hw
    rcases List.mem_or_eq_of_mem_set hw with hw | rfl
    · exact ho w hw
    · exact hv

/-- An address at or above `b`: its object's. -/
def MAddr.Own (b : Nat) {T : Ty} : MAddr H T → Prop
  | .field r _ => b ≤ r.id
  | .index r _ _ => b ≤ r.id

/-- A slot read at an own address of an own heap is own. -/
theorem Heap.readAddr_own {b : Nat} {T : Ty} (hp : Heap H) (hh : Heap.OwnAbove b hp)
    (a : MAddr H T) (ha : a.Own b) {v : MVal H T} (h : hp.readAddr a = some v) :
    MVal.Own b T v := by
  cases a with
  | field r hf =>
    cases h
    exact MFields.get_own _ _ hf (hh r ha)
  | index r ar i =>
    have hv : v ∈ MObj.elems ar (hp.get r) := List.mem_of_getElem? h
    exact MObj.elems_own ar _ (hh r ha) v hv

theorem Heap.OwnAbove.set {b : Nat} {R : RefTy} {hp : Heap H} (hh : Heap.OwnAbove b hp)
    (r : HRef H R) (o : MObj H R) (ho : MObj.Own b R o) : Heap.OwnAbove b (hp.set r o) :=
  fun {R'} r' hr' => by
    by_cases e : r.id = r'.id
    · obtain ⟨rfl, hq⟩ := HRef.heq_of_id r r' e
      cases hq
      rw [Heap.get_set_same]
      exact ho
    · rw [Heap.get_set_ne hp r r' e]
      exact hh r' hr'

theorem Heap.KeepsBelow.set {b : Nat} {R : RefTy} (hp : Heap H) (r : HRef H R) (o : MObj H R)
    (hr : b ≤ r.id) : Heap.KeepsBelow b (List.prefix_refl H) hp (hp.set r o) := fun r' hr' => by
  show (hp.set r o).get r' = _
  rw [Heap.get_set_ne hp r r' (by omega), MObj.wk_refl]

/-- **A write at an own address of an own slot** keeps every object below `b`
and the heap own. -/
theorem Heap.writeAddr_own {b : Nat} {T : Ty} (hp : Heap H) (hh : Heap.OwnAbove b hp)
    (a : MAddr H T) (ha : a.Own b) (v : MVal H T) (hv : MVal.Own b T v) {hp' : Heap H}
    (h : hp.writeAddr a v = some hp') :
    Heap.KeepsBelow b (List.prefix_refl H) hp hp' ∧ Heap.OwnAbove b hp' := by
  cases a with
  | field r hf =>
    cases h
    exact ⟨Heap.KeepsBelow.set hp r _ ha,
      hh.set r _ (MFields.set_own _ _ hf v (hh r ha) hv)⟩
  | index r ar i =>
    simp only [Heap.writeAddr, Heap.setIndex] at h
    split at h
    · cases h
      exact ⟨Heap.KeepsBelow.set hp r _ ha,
        hh.set r _ (MObj.setElem_own ar _ _ v (hh r ha) hv)⟩
    · cases h

/-- A heap grown keeping its objects, whose new objects are own from its old
length, is own above `b` where the old one was. -/
theorem Heap.OwnAbove.grow {b : Nat} {e : H <+: H'} {hp : Heap H} {hp' : Heap H'}
    (hk : Heap.Keeps e hp hp') (hh : Heap.OwnAbove b hp) (hn : Heap.OwnFrom H.length H hp')
    (hb : b ≤ H.length) : Heap.OwnAbove b hp' := fun r hr => by
  by_cases hlt : r.id < H.length
  · rw [← HRef.unwk_wk e r hlt, hk, MObj.own_wk]
    exact hh _ hr
  · exact MObj.Own.mono hb (hn r (Nat.le_of_not_lt hlt))

theorem TEnv.Own.wk {b : Nat} {Γ : Ctx} (e₀ : H <+: H') {e : TEnv C H Γ} (h : TEnv.Own b e) :
    TEnv.Own b (TEnv.wk e₀ Γ e) := fun i r hr => by
  rw [TEnv.get_wk] at hr
  cases hg : TEnv.get i e with
  | none => rw [hg] at hr; cases hr
  | some r₀ =>
    rw [hg] at hr
    cases hr
    exact h i r₀ hg

theorem TEnv.Own.push {b : Nat} {Γ : Ctx} {t : LTy} {e : TEnv C H Γ} (h : TEnv.Own b e)
    (v : t.TDenote C H) (hv : ∀ {R : RefTy} (ht : t = .mem R) (r : HRef H R),
      (ht ▸ v : LTy.TDenote C H (.mem R)) = some r → b ≤ r.id) :
    TEnv.Own (Γ := t :: Γ) b ((v, e) : TEnv C H (t :: Γ)) := fun i r hr => by
  cases i with
  | here => exact hv rfl r hr
  | there j => exact h j r hr

theorem Idx.eq_of_toNat {t : LTy} : {Γ : Ctx} → (i j : Idx Γ t) → i.toNat = j.toNat → i = j
  | _, .here, .here, _ => rfl
  | _, .here, .there j, h => absurd h (by simp only [Idx.toNat]; omega)
  | _, .there i, .here, h => absurd h (by simp only [Idx.toNat]; omega)
  | _, .there i, .there j, h => by
    have : i.toNat = j.toNat := by simpa only [Idx.toNat, Nat.add_right_cancel_iff] using h
    rw [Idx.eq_of_toNat i j this]

theorem TEnv.Own.set {b : Nat} {Γ : Ctx} {t : LTy} {e : TEnv C H Γ} (h : TEnv.Own b e)
    (j : Idx Γ t) (v : t.TDenote C H) (hv : ∀ {R : RefTy} (ht : t = .mem R) (r : HRef H R),
      (ht ▸ v : LTy.TDenote C H (.mem R)) = some r → b ≤ r.id) :
    TEnv.Own b (TEnv.set j v e) := fun {R} i r hr => by
  by_cases hij : j.toNat = i.toNat
  · have htu : t = .mem R := by
      have h1 := Idx.getElem?_toNat j
      have h2 := Idx.getElem?_toNat i
      rw [hij] at h1
      rw [h1] at h2
      exact Option.some.inj h2
    subst htu
    obtain rfl := Idx.eq_of_toNat j i hij
    rw [TEnv.get_set] at hr
    exact hv rfl r hr
  · rw [TEnv.get_set_ne j i v e hij] at hr
    exact h i r hr

end ReadWrite

/-! ## What the run reads of own objects -/

section Paths

variable {Γ : Ctx}

theorem TRes.ofOpt_ok {α : Type} {o : Option α} {a : α} (h : TRes.ofOpt o = .ok a) : o = some a := by
  cases o with
  | none => cases h
  | some x => cases h; rfl

mutual
/-- **A memory path of an own state reads an own slot.** -/
theorem MPath.mvalT_own {b : Nat} (σ : State C Γ) (he : TEnv.Own b σ.env)
    (hh : Heap.OwnAbove b σ.heap) : {T : Ty} → (p : MPath C Γ T) → {v : MVal σ.H T} →
      p.mvalT σ = .ok v → MVal.Own b T v
  | _, .var i _, v, h => by
    simp only [MPath.mvalT] at h
    split at h
    · rename_i r hr
      have e : r = v := Except.ok.inj h
      subst e
      exact he i r hr
    · cases h
  | _, .loc l, v, h => by
    simp only [MPath.mvalT] at h
    obtain ⟨a, ha, h⟩ := tbind_ok_inv h
    exact Heap.readAddr_own σ.heap hh a (MLoc.addrT_own σ he hh l ha) (TRes.ofOpt_ok h)

/-- **A memory location of an own state is at an own object.** -/
theorem MLoc.addrT_own {b : Nat} (σ : State C Γ) (he : TEnv.Own b σ.env)
    (hh : Heap.OwnAbove b σ.heap) : {T : Ty} → (l : MLoc C Γ T) → {a : MAddr σ.H T} →
      l.addrT σ = .ok a → a.Own b
  | _, .field p _ _, a, h => by
    simp only [MLoc.addrT] at h
    obtain ⟨r, hr, h⟩ := tbind_ok_inv h
    cases h
    exact MPath.mvalT_own σ he hh p hr
  | _, .index _ p _, a, h => by
    simp only [MLoc.addrT] at h
    obtain ⟨r, hr, h⟩ := tbind_ok_inv h
    obtain ⟨k, _, h⟩ := tbind_ok_inv h
    cases h
    exact MPath.mvalT_own σ he hh p hr
end

theorem MSrc.mvalT_own {b : Nat} (σ : State C Γ) (he : TEnv.Own b σ.env)
    (hh : Heap.OwnAbove b σ.heap) {T : Ty} (r : MSrc C Γ T) {v : MVal σ.H T}
    (h : r.mvalT σ = .ok v) : MVal.Own b T v := by
  cases r with
  | val => trivial
  | ref p => exact MPath.mvalT_own σ he hh p h

/-- **A memory right-hand side of an own state** keeps every object, the heap
own, and binds an own reference. -/
theorem MRhs.evalT_own {b : Nat} {R : RefTy} (σ : State C Γ) (he : TEnv.Own b σ.env)
    (hh : Heap.OwnAbove b σ.heap) (hb : b ≤ σ.H.length) (r : MRhs C Γ R)
    {g : Grew C Γ σ.H (HRef · R)} (h : r.evalT σ = .ok g) :
    Heap.Keeps g.ext σ.heap g.st.heap ∧ Heap.OwnAbove b g.st.heap ∧ TEnv.Own b g.st.env ∧
      b ≤ g.val.id := by
  cases r with
  | alias p =>
    simp only [MRhs.evalT] at h
    obtain ⟨v, hv, h⟩ := tbind_ok_inv h
    cases h
    exact ⟨Heap.Keeps.refl _, hh, he, MPath.mvalT_own σ he hh p hv⟩
  | copy p hm =>
    simp only [MRhs.evalT] at h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    obtain ⟨sv, _, h⟩ := tbind_ok_inv h
    cases h
    have ho := SVal.own_copyStToM sv hm σ.heap
    exact ⟨SVal.keeps_copyStToM sv hm σ.heap,
      Heap.OwnAbove.grow (SVal.keeps_copyStToM sv hm σ.heap) hh ho.1 hb,
      TEnv.Own.wk _ he, Nat.le_trans hb ho.2⟩
  | newArr n hn =>
    simp only [MRhs.evalT] at h
    cases h
    have ho := SVal.own_copyStToM (newArrT R (n.evalT σ) hn) (RefTy.mapFree_of_newArrOk hn) σ.heap
    exact ⟨SVal.keeps_copyStToM _ _ σ.heap,
      Heap.OwnAbove.grow (SVal.keeps_copyStToM _ _ σ.heap) hh ho.1 hb,
      TEnv.Own.wk _ he, Nat.le_trans hb ho.2⟩

end Paths

/-! ## The locals' references -/

section Locals

variable {H H' : HTy}

theorem TEnv.Own.drop {b : Nat} {Γ Δ : Ctx} (h : Ext Γ Δ) {e : TEnv C H Δ} (he : TEnv.Own b e) :
    TEnv.Own b (TEnv.drop h e) := fun i r hr => by
  rw [← TEnv.get_ext_drop] at hr
  exact he _ r hr

theorem TEnv.Own.cons {b : Nat} {Γ : Ctx} {t : LTy} (ht : ∀ R, t ≠ .mem R)
    {e : TEnv C H (t :: Γ)} (he : TEnv.Own b e.2) : TEnv.Own b e := fun {R} i r hr => by
  cases i with
  | here => exact absurd rfl (ht R)
  | there j => exact he j r hr

theorem TEnv.Own.nil {b : Nat} (e : TEnv C H []) : TEnv.Own b e := fun i => nomatch i

/-- Locals that agree but where `W` lists them, none of them a memory local:
the memory locals as they were. -/
theorem TEnv.Own.of_agree {b : Nat} {Γ : Ctx} {W : List (LTy × Nat)} {e e' : TEnv C H Γ}
    (hag : TLocAgree 0 W e e') (hW : ∀ x ∈ W, ∀ R, x.1 ≠ .mem R) (he : TEnv.Own b e) :
    TEnv.Own b e' := fun {R} i r hr => by
  have hni : (LTy.mem R, i.toNat - 0) ∉ W := fun hm => hW _ hm R rfl
  have := eq_of_heq (hag _ i (Nat.zero_le _) hni)
  rw [this] at hr
  exact he i r hr

theorem Heap.OwnAbove.of_heq {b : Nat} {hp : Heap H} {hp' : Heap H'} (hH : H' = H)
    (hh : HEq hp' hp) (ho : Heap.OwnAbove b hp) : Heap.OwnAbove b hp' := by
  subst hH
  cases hh
  exact ho

theorem Args.evalT_own {b : Nat} {Γ : Ctx} (σ : State C Γ) (he : TEnv.Own b σ.env)
    (hh : Heap.OwnAbove b σ.heap) : {ps : Ctx} → (args : Args C Γ ps) → {a : TEnv C σ.H ps} →
      args.evalT σ = .ok a → TEnv.Own b a
  | _, .nil, _, _ => TEnv.Own.nil _
  | _, .snoc as _ _ e, a, h => by
    change (do let r ← Args.evalT σ as; let v ← e.evalT σ; pure (v, r)) = Except.ok a at h
    obtain ⟨r, hr, h⟩ := tbind_ok_inv h
    obtain ⟨v, _, h⟩ := tbind_ok_inv h
    cases h
    exact TEnv.Own.cons (by intro R h; cases h) (Args.evalT_own σ he hh as hr)
  | _, .snocStorage as _ _ e, a, h => by
    change (do let r ← Args.evalT σ as; let v ← e.resolveT σ; pure (some v, r)) = Except.ok a at h
    obtain ⟨r, hr, h⟩ := tbind_ok_inv h
    obtain ⟨v, _, h⟩ := tbind_ok_inv h
    cases h
    exact TEnv.Own.cons (by intro R h; cases h) (Args.evalT_own σ he hh as hr)
  | _, .snocMemory as _ _ p, a, h => by
    change (do let r ← Args.evalT σ as; let v ← p.mvalT σ; pure (some v, r)) = Except.ok a at h
    obtain ⟨r, hr, h⟩ := tbind_ok_inv h
    obtain ⟨v, hv, h⟩ := tbind_ok_inv h
    cases h
    intro i r' hr'
    cases i with
    | here =>
      cases hr'
      exact MPath.mvalT_own σ he hh p hv
    | there j => exact Args.evalT_own σ he hh as hr j r' hr'

/-- No memory local: the parameters of a callee whose frame is its own. -/
def Ctx.memFree : Ctx → Bool
  | [] => true
  | .mem _ :: _ => false
  | _ :: ps => Ctx.memFree ps

theorem TEnv.Own.memFree {b : Nat} : {ps : Ctx} → Ctx.memFree ps = true → (e : TEnv C H ps) →
    TEnv.Own b e
  | [], _, e => TEnv.Own.nil e
  | .mem _ :: _, h, _ => by simp only [Ctx.memFree, Bool.false_eq_true] at h
  | .val _ :: _, h, e => TEnv.Own.cons (by intro R h; cases h) (TEnv.Own.memFree (ps := _) (by exact h) e.2)
  | .alias _ :: _, h, e => TEnv.Own.cons (by intro R h; cases h) (TEnv.Own.memFree (ps := _) (by exact h) e.2)
  | .old :: _, h, e => TEnv.Own.cons (by intro R h; cases h) (TEnv.Own.memFree (ps := _) (by exact h) e.2)
  | .oldNet :: _, h, e => TEnv.Own.cons (by intro R h; cases h) (TEnv.Own.memFree (ps := _) (by exact h) e.2)
  | .kint :: _, h, e => TEnv.Own.cons (by intro R h; cases h) (TEnv.Own.memFree (ps := _) (by exact h) e.2)

theorem Heap.ownAbove_length (hp : Heap H) : Heap.OwnAbove H.length hp := fun r hr =>
  absurd r.id_lt (Nat.not_lt_of_le hr)

theorem TEnv.Own.append {b : Nat} : (ρ : Ctx) → {Γ : Ctx} → (r : TEnv C H ρ) → (e : TEnv C H Γ) →
    TEnv.Own b r → TEnv.Own b e → TEnv.Own b (TEnv.append ρ r e)
  | [], _, _, _, _, he => he
  | _ :: ρ, _, r, e, hr, he => fun i x hx => by
    cases i with
    | here => exact hr .here x hx
    | there j => exact TEnv.Own.append ρ r.2 e (fun i' => hr (.there i')) he j x hx

theorem TEnv.Own.take {b : Nat} : (ρ : Ctx) → {Γ : Ctx} → (e : TEnv C H (ρ ++ Γ)) →
    TEnv.Own b e → TEnv.Own b (TEnv.take ρ e)
  | [], _, _, _ => TEnv.Own.nil _
  | _ :: ρ, _, e, he => fun i x hx => by
    cases i with
    | here => exact he .here x hx
    | there j => exact TEnv.Own.take ρ e.2 (fun i' => he (.there i')) j x hx

/-- A reference read at one heap typing as at an equal one: its identity. -/
theorem HRef.heq_some_id {R : RefTy} (hH : H' = H) {x : Option (HRef H' R)} {y : Option (HRef H R)}
    (h : HEq x y) {r : HRef H' R} (hx : x = some r) : ∃ r' : HRef H R, y = some r' ∧ r'.id = r.id := by
  subst hH
  cases h
  exact ⟨r, hx, rfl⟩

end Locals

/-! ## The frame -/

/-- **What a run that writes only own objects leaves of the global part**:
every object below `b` kept, the funds and the transaction, and, unless `μ`
is `nonpayable`, the storage and the ledger. -/
structure TGFrameW (μ : Mutability) (b : Nat) {Γ Δ : Ctx} (σ : State C Γ) (τ : State C Δ)
    (e : σ.H <+: τ.H) : Prop where
  keeps : Heap.KeepsBelow b e σ.heap τ.heap
  selfBalance : μ ≠ .nonpayable → τ.selfBalance = σ.selfBalance
  tx : τ.tx = σ.tx
  keepsSt : μ ≠ .nonpayable → τ.storage = σ.storage ∧ τ.net = σ.net

namespace TGFrameW

variable {μ : Mutability} {b : Nat} {Γ Δ Ε : Ctx}

theorem trans {σ : State C Γ} {τ : State C Δ} {υ : State C Ε} {e₁ : σ.H <+: τ.H}
    {e₂ : τ.H <+: υ.H} (h₁ : TGFrameW μ b σ τ e₁) (h₂ : TGFrameW μ b τ υ e₂) (e : σ.H <+: υ.H) :
    TGFrameW μ b σ υ e :=
  ⟨Heap.KeepsBelow.trans h₁.keeps h₂.keeps, fun hn => (h₂.selfBalance hn).trans (h₁.selfBalance hn),
    h₂.tx.trans h₁.tx, fun hμ => ⟨(h₂.keepsSt hμ).1.trans (h₁.keepsSt hμ).1,
      (h₂.keepsSt hμ).2.trans (h₁.keepsSt hμ).2⟩⟩

theorem ofM {σ : State C Γ} {τ : State C Δ} {e : σ.H <+: τ.H} (h : TGFrameM μ σ τ e) :
    TGFrameW μ b σ τ e :=
  ⟨Heap.Keeps.keepsBelow h.keeps, h.selfBalance, h.tx, h.keepsSt⟩

theorem withEnv {σ : State C Γ} {τ : State C Δ} {e : σ.H <+: τ.H} (h : TGFrameW μ b σ τ e)
    (env : TEnv C τ.H Ε) : TGFrameW μ b σ (τ.withEnv env) e :=
  ⟨h.keeps, h.selfBalance, h.tx, h.keepsSt⟩

/-- Every object below the entry's heap length kept: every object. -/
theorem toM {σ : State C Γ} {τ : State C Δ} {e : σ.H <+: τ.H}
    (h : TGFrameW μ σ.H.length σ τ e) : TGFrameM μ σ τ e :=
  ⟨Heap.KeepsBelow.keeps h.keeps, h.selfBalance, h.tx, h.keepsSt⟩

end TGFrameW

/-! ## Which bodies -/

mutual

/-- **A statement a callee of mutability `μ` may run writing its own
objects**: `Stmt.withinM`'s allocations and rebinds, a write into a memory
object (`assignMem`), a statement within `μ` that writes no memory local,
and `if`, a block, a loop or a call over such statements. -/
def Stmt.withinW (μ : Mutability) : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Bool
  | _, _, s => Stmt.casesOn (motive_1 := fun _ _ _ => Bool) s
    (assign := fun _ _ => μ == .nonpayable) (rebind := fun _ r => r.pathIn μ)
    (assignLocal := fun _ r => r.readsIn μ)
    (declLocal := fun _ _ init => match init with
      | none => true
      | some e => e.readsIn μ)
    (declStorage := fun _ _ init => match init with
      | none => true
      | some r => r.pathIn μ)
    (opAssign := fun _ _ _ l r => r.readsIn μ && l.writableIn μ)
    (incDec := fun _ _ l => l.writableIn μ) (assignIncDec := fun _ _ _ l _ => l.writableIn μ)
    (assignLocalPush := fun _ _ => false)
    (pushOpAssign := fun _ _ _ _ _ => false) (pushIncDec := fun _ _ _ => false)
    (push := fun _ _ _ => false) (pop := fun _ => false)
    (transfer := fun _ _ => μ == .nonpayable) (send := fun _ _ _ _ => μ == .nonpayable)
    (declMem := fun _ _ init _ _ => match init with
      | none => true
      | some r => r.allocIn μ)
    (rebindMem := fun _ r => r.allocIn μ)
    (assignFromMem := fun _ _ => false) (assignMem := fun _ _ => true)
    (delete := fun _ => μ == .nonpayable) (deleteMem := fun _ _ => false)
    (assignNew := fun _ _ _ => false)
    (ite := fun c thn els => c.readsIn μ && Prog.withinW μ thn && Prog.withinW μ els)
    (require := fun c => c.readsIn μ) (assert := fun c => c.readsIn μ) (revert := true)
    (assumeFalse := true)
    (call := fun _ args _ body => args.readsIn μ && Prog.withinW μ body)
    (tryCall := fun _ _ _ _ _ _ _ _ _ _ => false)
    (loop := fun _ c body => c.readsIn μ && Prog.withinW μ body)
    (block := fun body => Prog.withinW μ body)
    (callReceiver := fun _ _ _ _ _ => false)
    (callReceiverPush := fun _ _ _ _ _ _ => false)
    (callRec := fun _ _ args _ body => args.readsIn μ && Prog.withinW μ (body ()))
    (revertData := fun d => d.all fun p => match p with | .word v => v.readsIn μ | _ => true)
    (catchData := fun _ _ _ _ _ _ _ _ => false)
  termination_by structural _ _ s => s

/-- `Stmt.withinW` of every statement. -/
def Prog.withinW (μ : Mutability) : {Γ Γ' : Ctx} → Prog C Γ Γ' → Bool
  | _, _, P => Prog.casesOn (motive_2 := fun _ _ _ => Bool) P true
      (fun s P => Stmt.withinW μ s && Prog.withinW μ P)
  termination_by structural _ _ P => P

end

theorem Prog.withinW_cons {μ : Mutability} {Γ Γ₁ Γ₂ : Ctx} (s : Stmt C Γ Γ₁) (P : Prog C Γ₁ Γ₂) :
    Prog.withinW μ (.cons s P) = (Stmt.withinW μ s && Prog.withinW μ P) :=
  rfl

/-- Every frame of an unrolling is within `μ` where each frame is from the
one below. -/
theorem Prog.withinW_recUnroll {μ : Mutability} {F : Ctx}
    {step : Nat → (Unit → Prog C F F) → Prog C F F}
    (hs : ∀ n (t : Unit → Prog C F F), Prog.withinW μ (t ()) = true →
      Prog.withinW μ (step n t) = true) (d : Nat) :
    Prog.withinW μ (recUnroll Prog.recBase step d) = true :=
  recUnroll_induct (fun b => Prog.withinW μ b = true) rfl hs d

/-! ## Calls and leaves -/

section Calls

variable {μ : Mutability} {b : Nat} {Γ : Ctx}

theorem Binders.own {H : HTy} : {ρ : Ctx} → Binders ρ → (x : TEnv C H ρ) → TEnv.Own b x
  | _, .nil, x => TEnv.Own.nil x
  | _, .snoc bs _ _, x => TEnv.Own.cons (by intro R h; cases h) (Binders.own bs x.2)

/-- A call's frame entered from an own state: own, a memory return's object
fresh. -/
theorem CallRet.enterT_own {Γ' rs ps : Ctx} (ret : CallRet Γ rs Γ') (τ : State C ps)
    (hb : b ≤ τ.H.length) (he : TEnv.Own b τ.env) (hh : Heap.OwnAbove b τ.heap) :
    TEnv.Own b (ret.enterT τ).st.env ∧ Heap.OwnAbove b (ret.enterT τ).st.heap ∧
      b ≤ (ret.enterT τ).st.H.length := by
  cases ret with
  | none => exact ⟨he, hh, hb⟩
  | val p r res => exact ⟨TEnv.Own.cons (by intro R h; cases h) he, hh, hb⟩
  | rets bs => exact ⟨TEnv.Own.append _ _ _ (Binders.own bs _) he, hh, hb⟩
  | mem R r hd hm =>
    have ho := SVal.own_copyStToM (SVal.dflt (.ref R)) hm τ.heap
    refine ⟨?_, Heap.OwnAbove.grow (SVal.keeps_copyStToM _ hm τ.heap) hh ho.1 hb,
      Nat.le_trans hb (List.IsPrefix.length_le (τ.allocDefaultG R hm).ext)⟩
    intro _ i x hx
    cases i with
    | here =>
      have e : (τ.allocDefaultG R hm).val = x := Option.some.inj hx
      subst e
      exact Nat.le_trans hb ho.2
    | there j => exact TEnv.Own.wk _ he j x hx
  | storage R r => exact ⟨TEnv.Own.cons (by intro R' h; cases h) he, hh, hb⟩

/-- What a call leaves its caller's own locals: own. -/
theorem CallRet.leaveT_own {Γ' rs : Ctx} (ret : CallRet Γ rs Γ') {H : HTy} (e : TEnv C H Γ)
    (x : TEnv C H rs) (he : TEnv.Own b e) (hx : TEnv.Own b x) : TEnv.Own b (ret.leaveT e x) := by
  cases ret with
  | none => exact he
  | val p r res =>
    cases res with
    | none => exact he
    | some j => exact TEnv.Own.set he j _ (by intro R h; cases h)
  | rets bs => exact TEnv.Own.append _ x e hx he
  | mem R r hd hm =>
    intro _ i y hy
    cases i with
    | here => exact hx .here y hy
    | there j => exact he j y hy
  | storage R r => exact TEnv.Own.cons (by intro R' h; cases h) he

/-- A statement within `μ` that writes no memory local and pushes none: by
`Stmt.run_frame`, own where it started. -/
theorem Stmt.run_frameW_leaf {Γ' : Ctx} (s : Stmt C Γ Γ') (hw : s.within μ = true)
    (hW : ∀ x ∈ s.writesAt 0, ∀ R, x.1 ≠ .mem R)
    (hpush : ∀ {R : RefTy} (j : Idx Γ' (.mem R)), ∃ i : Idx Γ (.mem R), j = i.ext s.ext)
    (d : Nat) {σ : State C Γ} {o : Out C σ.H Γ'} (h : s.run σ = .ok o)
    (he : TEnv.Own b σ.env) (hh : Heap.OwnAbove b σ.heap) :
    TGFrameW μ b σ o.st o.ext ∧
      TLocAgreeM o.ext d (s.writesAt d) σ.env (TEnv.drop s.ext o.st.env) ∧
      TEnv.Own b o.st.env ∧ Heap.OwnAbove b o.st.heap := by
  obtain ⟨hg, ha⟩ := Stmt.run_frame s hw d h
  obtain ⟨-, ha0⟩ := Stmt.run_frame s hw 0 h
  refine ⟨TGFrameW.ofM (TGFrameM.ofFrame hg _), TLocAgreeM.ofAgree hg.H ha, ?_,
    Heap.OwnAbove.of_heq hg.H hg.heap hh⟩
  intro R j r hr
  obtain ⟨i, rfl⟩ := hpush j
  rw [TEnv.get_ext_drop] at hr
  have hni : (LTy.mem R, i.toNat - 0) ∉ s.writesAt 0 := fun hm => hW _ hm R rfl
  obtain ⟨r', hr', hid⟩ := HRef.heq_some_id hg.H (ha0 _ i (Nat.zero_le _) hni) hr
  rw [← hid]
  exact he i r' hr'

end Calls

/-! ## A program that writes only own objects, within its frame -/

section Progs

variable {μ : Mutability}

theorem Idx.outer_ty {Γ : Ctx} {t : LTy} {d : Nat} (i : Idx Γ t) {x : LTy × Nat}
    (hx : x ∈ i.outer d) : x.1 = t := by
  unfold Idx.outer at hx
  split at hx
  · rcases List.mem_singleton.1 hx with rfl
    rfl
  · exact absurd hx List.not_mem_nil

theorem OpLoc.writesAt_ty {Γ : Ctx} {p : PrimTy} {d : Nat} (l : OpLoc C Γ p) {x : LTy × Nat}
    (hx : x ∈ l.writesAt d) : x.1 = .val p := by
  cases l with
  | «local» i => exact Idx.outer_ty i hx
  | _ => exact absurd hx List.not_mem_nil

theorem Idx.ext_refl_eq {Γ : Ctx} {t : LTy} (i : Idx Γ t) : i.ext .refl = i := rfl

mutual

/-- **A statement that writes only its own objects runs within its frame**:
from a state whose memory locals and objects from `b` on are own, every
object below `b` kept, the state own after. -/
theorem Stmt.run_frameW : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → s.withinW μ = true → (d b : Nat) →
    {σ : State C Γ} → {o : Out C σ.H Γ'} → s.run σ = .ok o → b ≤ σ.H.length →
    TEnv.Own b σ.env → Heap.OwnAbove b σ.heap →
      TGFrameW μ b σ o.st o.ext ∧
        TLocAgreeM o.ext d (s.writesAt d) σ.env (TEnv.drop s.ext o.st.env) ∧
        TEnv.Own b o.st.env ∧ Heap.OwnAbove b o.st.heap
  | _, _, .assign .., hw, d, _, _, _, h, _, he, hh =>
    Stmt.run_frameW_leaf _ (by exact hw) (fun _ hx => absurd hx List.not_mem_nil)
      (fun j => ⟨j, rfl⟩) d h he hh
  | _, _, .rebind i _, hw, d, _, _, _, h, _, he, hh =>
    Stmt.run_frameW_leaf _ (by exact hw) (fun _ hx R e => by
        rw [Idx.outer_ty i hx] at e; cases e)
      (fun j => ⟨j, rfl⟩) d h he hh
  | _, _, .assignLocal i _, hw, d, _, _, _, h, _, he, hh =>
    Stmt.run_frameW_leaf _ (by exact hw) (fun _ hx R e => by
        rw [Idx.outer_ty i hx] at e; cases e)
      (fun j => ⟨j, rfl⟩) d h he hh
  | _, _, .declLocal .., hw, d, _, _, _, h, _, he, hh =>
    Stmt.run_frameW_leaf _ (by exact hw) (fun _ hx => absurd hx List.not_mem_nil)
      (fun j => by cases j with | there i => exact ⟨i, rfl⟩) d h he hh
  | _, _, .declStorage .., hw, d, _, _, _, h, _, he, hh =>
    Stmt.run_frameW_leaf _ (by exact hw) (fun _ hx => absurd hx List.not_mem_nil)
      (fun j => by cases j with | there i => exact ⟨i, rfl⟩) d h he hh
  | _, _, .opAssign _ _ _ l _, hw, d, _, _, _, h, _, he, hh =>
    Stmt.run_frameW_leaf _ (by exact hw) (fun _ hx R e => by
        rw [OpLoc.writesAt_ty l hx] at e; cases e)
      (fun j => ⟨j, rfl⟩) d h he hh
  | _, _, .incDec _ _ l, hw, d, _, _, _, h, _, he, hh =>
    Stmt.run_frameW_leaf _ (by exact hw) (fun _ hx R e => by
        rw [OpLoc.writesAt_ty l hx] at e; cases e)
      (fun j => ⟨j, rfl⟩) d h he hh
  | _, _, .assignIncDec i _ _ l _, hw, d, _, _, _, h, _, he, hh =>
    Stmt.run_frameW_leaf _ (by exact hw) (fun _ hx R e => by
        rcases List.mem_append.1 hx with hx | hx
        · rw [Idx.outer_ty i hx] at e; cases e
        · rw [OpLoc.writesAt_ty l hx] at e; cases e)
      (fun j => ⟨j, rfl⟩) d h he hh
  | _, _, .transfer .., hw, d, _, _, _, h, _, he, hh =>
    Stmt.run_frameW_leaf _ (by exact hw) (fun _ hx => absurd hx List.not_mem_nil)
      (fun j => ⟨j, rfl⟩) d h he hh
  | _, _, .send pv .., hw, d, _, _, _, h, _, he, hh =>
    Stmt.run_frameW_leaf _ (by exact hw) (fun _ hx R e => by
        rw [Idx.outer_ty pv hx] at e; cases e)
      (fun j => ⟨j, rfl⟩) d h he hh
  | _, _, .delete .., hw, d, _, _, _, h, _, he, hh =>
    Stmt.run_frameW_leaf _ (by exact hw) (fun _ hx => absurd hx List.not_mem_nil)
      (fun j => ⟨j, rfl⟩) d h he hh
  | _, _, .require .., hw, d, _, _, _, h, _, he, hh =>
    Stmt.run_frameW_leaf _ (by exact hw) (fun _ hx => absurd hx List.not_mem_nil)
      (fun j => ⟨j, rfl⟩) d h he hh
  | _, _, .assert .., hw, d, _, _, _, h, _, he, hh =>
    Stmt.run_frameW_leaf _ (by exact hw) (fun _ hx => absurd hx List.not_mem_nil)
      (fun j => ⟨j, rfl⟩) d h he hh
  | _, _, .revert, _, _, _, _, _, h, _, _, _ | _, _, .assumeFalse, _, _, _, _, _, h, _, _, _ => by
    cases h
  | _, _, .revertData ps, _, _, _, σ, _, h, _, _, _ => by
    change TRun.revertData ps σ = .ok _ at h
    unfold TRun.revertData at h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
  | _, _, .declMem R _ init _ hm, hw, d, b, σ, o, h, hb, he, hh => by
    change TRun.declMem R init hm σ = .ok o at h
    cases init with
    | none =>
      cases h
      have ho := SVal.own_copyStToM (SVal.dflt (.ref R)) hm σ.heap
      refine ⟨TGFrameW.ofM ((TGFrameM.adopt (μ := μ) σ _
          (State.keeps_allocDefaultG σ R hm)).withEnv _), TLocAgreeM.wk _ _, ?_,
        Heap.OwnAbove.grow (SVal.keeps_copyStToM _ hm σ.heap) hh ho.1 hb⟩
      intro _ i x hx
      cases i with
      | here =>
        have e : (σ.allocDefaultG R hm).val = x := Option.some.inj hx
        subst e
        exact Nat.le_trans hb ho.2
      | there j => exact TEnv.Own.wk _ he j x hx
    | some r =>
      simp only [TRun.declMem] at h
      obtain ⟨g, hg, h⟩ := tbind_ok_inv h
      cases h
      obtain ⟨hk, hh', he', hv⟩ := MRhs.evalT_own σ he hh hb r hg
      obtain ⟨hf, ha⟩ := MRhs.evalT_frame μ d r hg
      refine ⟨TGFrameW.ofM (hf.withEnv _), ha, ?_, hh'⟩
      intro _ i x hx
      cases i with
      | here =>
        have e : g.val = x := Option.some.inj hx
        subst e
        exact hv
      | there j => exact he' j x hx
  | _, _, .rebindMem i r, hw, d, b, σ, o, h, hb, he, hh => by
    change TRun.rebindMem i r σ = .ok o at h
    simp only [TRun.rebindMem] at h
    obtain ⟨g, hg, h⟩ := tbind_ok_inv h
    cases h
    obtain ⟨hk, hh', he', hv⟩ := MRhs.evalT_own σ he hh hb r hg
    obtain ⟨hf, ha⟩ := MRhs.evalT_frame μ d r hg
    refine ⟨TGFrameW.ofM (hf.withEnv _), (ha.mono fun _ hx => absurd hx List.not_mem_nil).trans
      (TLocAgreeM.set i _ _ (List.prefix_refl _)), ?_, hh'⟩
    refine TEnv.Own.set he' i _ ?_
    intro _ ht x hx
    cases ht
    cases hx
    exact hv
  | _, _, .assignMem l r, _, d, b, σ, o, h, hb, he, hh => by
    change TRun.assignMem l r σ = .ok o at h
    simp only [TRun.assignMem] at h
    obtain ⟨mv, hmv, h⟩ := tbind_ok_inv h
    obtain ⟨a, ha, h⟩ := tbind_ok_inv h
    obtain ⟨hp, hw', h⟩ := tbind_ok_inv h
    cases h
    obtain ⟨hk, hh'⟩ := Heap.writeAddr_own σ.heap hh a (MLoc.addrT_own σ he hh l ha) mv
      (MSrc.mvalT_own σ he hh r hmv) (TRes.ofOpt_ok hw')
    exact ⟨⟨hk, fun _ => rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩,
      TLocAgreeM.ofAgree rfl (TLocAgree.refl _), he, hh'⟩
  | _, _, .ite c thn els, hw, d, b, σ, o, h, hb, he, hh => by
    have hw' : (c.readsIn μ && Prog.withinW μ thn && Prog.withinW μ els) = true := hw
    simp only [Bool.and_eq_true] at hw'
    change TRun.ite c thn.ext thn.runR els.ext els.runR σ = .ok o at h
    simp only [TRun.ite] at h
    obtain ⟨v, _, h⟩ := tbind_ok_inv h
    split at h
    · obtain ⟨o', h', rfl⟩ := tmap_ok_inv h
      obtain ⟨hg, ha, he', hh'⟩ := Prog.run_frameW thn hw'.1.2 d b h' hb he hh
      exact ⟨hg.withEnv _, ha.left, TEnv.Own.drop _ he', hh'⟩
    · obtain ⟨o', h', rfl⟩ := tmap_ok_inv h
      obtain ⟨hg, ha, he', hh'⟩ := Prog.run_frameW els hw'.2 d b h' hb he hh
      exact ⟨hg.withEnv _, ha.right, TEnv.Own.drop _ he', hh'⟩
  | _, _, .block body, hw, d, b, σ, o, h, hb, he, hh => by
    change (body.runR σ).map (fun o => ⟨o.st.drop body.ext, o.ext⟩) = .ok o at h
    obtain ⟨o', h', rfl⟩ := tmap_ok_inv h
    obtain ⟨hg, ha, he', hh'⟩ := Prog.run_frameW body hw d b h' hb he hh
    exact ⟨hg.withEnv _, ha, TEnv.Own.drop _ he', hh'⟩
  | Γ, _, .call _ args ret body, hw, d, b, σ, o, h, hb, he, hh => by
    have hw' : (args.readsIn μ && Prog.withinW μ body) = true := hw
    simp only [Bool.and_eq_true] at hw'
    change TRun.call args ret body.ext body.runR σ = .ok o at h
    rw [TRun.call_eq] at h
    obtain ⟨a, haa, h⟩ := tbind_ok_inv h
    unfold TRun.callFrom at h
    obtain ⟨o', hbd, h⟩ := tbind_ok_inv h
    cases h
    have hea : TEnv.Own b a := Args.evalT_own σ he hh args haa
    obtain ⟨he₁, hh₁, hb₁⟩ := CallRet.enterT_own (b := b) ret (σ.withEnv a) hb hea hh
    have hen := CallRet.enterT_frameM (μ := μ) ret (σ.withEnv a)
    obtain ⟨hg, -, he₂, hh₂⟩ := Prog.run_frameW body hw'.2 0 b hbd hb₁ he₁ hh₁
    refine ⟨(((TGFrameW.ofM (TGFrameM.env σ a (List.prefix_refl _))).trans (TGFrameW.ofM hen)
        (ret.enterT (σ.withEnv a)).ext).trans hg _).withEnv _,
      CallRet.leaveT_frameM ret _ σ.env _ d, ?_, hh₂⟩
    exact CallRet.leaveT_own ret _ _ (TEnv.Own.wk _ he)
      (TEnv.Own.take _ _ (TEnv.Own.drop _ he₂))
  | Γ, _, .callRec _ _ args ret body, hw, d, b, σ, o, h, hb, he, hh => by
    have hw' : (args.readsIn μ && Prog.withinW μ (body ())) = true := hw
    simp only [Bool.and_eq_true] at hw'
    change TRun.call args ret (body ()).ext (body ()).runR σ = .ok o at h
    rw [TRun.call_eq] at h
    obtain ⟨a, haa, h⟩ := tbind_ok_inv h
    unfold TRun.callFrom at h
    obtain ⟨o', hbd, h⟩ := tbind_ok_inv h
    cases h
    have hea : TEnv.Own b a := Args.evalT_own σ he hh args haa
    obtain ⟨he₁, hh₁, hb₁⟩ := CallRet.enterT_own (b := b) ret (σ.withEnv a) hb hea hh
    have hen := CallRet.enterT_frameM (μ := μ) ret (σ.withEnv a)
    obtain ⟨hg, -, he₂, hh₂⟩ := Prog.run_frameW (body ()) hw'.2 0 b hbd hb₁ he₁ hh₁
    refine ⟨(((TGFrameW.ofM (TGFrameM.env σ a (List.prefix_refl _))).trans (TGFrameW.ofM hen)
        (ret.enterT (σ.withEnv a)).ext).trans hg _).withEnv _,
      CallRet.leaveT_frameM ret _ σ.env _ d, ?_, hh₂⟩
    exact CallRet.leaveT_own ret _ _ (TEnv.Own.wk _ he)
      (TEnv.Own.take _ _ (TEnv.Own.drop _ he₂))
  | _, _, .loop _ c body, hw, d, b, σ, o, h, hb, he, hh => by
    have hw' : (c.readsIn μ && Prog.withinW μ body) = true := hw
    rw [Bool.and_eq_true] at hw'
    change TLoop.run (fun o : Out C σ.H _ => (body.runR o.st).map
        fun o' => ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩) (fun o => c.evalT o.st)
        ⟨σ, List.prefix_refl _⟩ = .ok o at h
    refine TLoop.run_induct
      (P := fun a : Out C σ.H _ =>
        TGFrameW μ b σ a.st a.ext ∧ TLocAgreeM a.ext d (Prog.writesAt d body) σ.env a.st.env ∧
          TEnv.Own b a.st.env ∧ Heap.OwnAbove b a.st.heap ∧ b ≤ a.st.H.length)
      (Q := fun r => ∀ o, r = .ok o →
        TGFrameW μ b σ o.st o.ext ∧ TLocAgreeM o.ext d (Prog.writesAt d body) σ.env o.st.env ∧
          TEnv.Own b o.st.env ∧ Heap.OwnAbove b o.st.heap)
      ⟨TGFrameW.ofM (TGFrameM.ofFrame (TGFrame.refl σ) _),
        TLocAgreeM.ofAgree rfl (TLocAgree.refl _), he, hh, hb⟩
      (fun a ha => ?_) (fun _ h => by cases h) o h
    unfold TLoop.step
    dsimp only
    cases c.evalT a.st with
    | error => dsimp only; intro _ h; cases h
    | ok v =>
      cases v with
      | false => dsimp only; intro _ h; cases h; exact ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1⟩
      | true =>
        dsimp only
        cases hbd : (body.runR a.st).map
            (fun o' => (⟨o'.st.drop body.ext, a.ext.trans o'.ext⟩ : Out C σ.H _)) with
        | error => dsimp only; intro _ h; cases h
        | ok a' =>
          dsimp only
          obtain ⟨o', hb', rfl⟩ := tmap_ok_inv hbd
          obtain ⟨hg, ha', he', hh'⟩ :=
            Prog.run_frameW body hw'.2 d b hb' ha.2.2.2.2 ha.2.2.1 ha.2.2.2.1
          refine ⟨ha.1.trans (hg.withEnv (TEnv.drop body.ext o'.st.env)) (a.ext.trans o'.ext),
            ha.2.1.trans ha', TEnv.Own.drop _ he', hh',
            Nat.le_trans ha.2.2.2.2 (List.IsPrefix.length_le o'.ext)⟩
  | _, _, .assignLocalPush .., hw, _, _, _, _, _, _, _, _
  | _, _, .pushOpAssign .., hw, _, _, _, _, _, _, _, _
  | _, _, .pushIncDec .., hw, _, _, _, _, _, _, _, _
  | _, _, .push .., hw, _, _, _, _, _, _, _, _ | _, _, .pop _, hw, _, _, _, _, _, _, _, _
  | _, _, .assignFromMem .., hw, _, _, _, _, _, _, _, _
  | _, _, .deleteMem .., hw, _, _, _, _, _, _, _, _
  | _, _, .assignNew .., hw, _, _, _, _, _, _, _, _
  | _, _, .tryCall .., hw, _, _, _, _, _, _, _, _
  | _, _, .callReceiver .., hw, _, _, _, _, _, _, _, _
  | _, _, .callReceiverPush .., hw, _, _, _, _, _, _, _, _
  | _, _, .catchData .., hw, _, _, _, _, _, _, _, _ => by cases hw

/-- **A program that writes only its own objects runs within its frame.** -/
theorem Prog.run_frameW : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → Prog.withinW μ P = true →
    (d b : Nat) → {σ : State C Γ} → {o : Out C σ.H Γ'} → Prog.run σ P = .ok o →
    b ≤ σ.H.length → TEnv.Own b σ.env → Heap.OwnAbove b σ.heap →
      TGFrameW μ b σ o.st o.ext ∧
        TLocAgreeM o.ext d (Prog.writesAt d P) σ.env (TEnv.drop P.ext o.st.env) ∧
        TEnv.Own b o.st.env ∧ Heap.OwnAbove b o.st.heap
  | _, _, .nil, _, _, _, σ, _, h, _, he, hh => by
    cases h
    exact ⟨TGFrameW.ofM (TGFrameM.ofFrame (TGFrame.refl σ) _),
      TLocAgreeM.ofAgree rfl (TLocAgree.refl _), he, hh⟩
  | _, _, .cons s P, hw, d, b, σ, o, h, hb, he, hh => by
    rw [Prog.withinW_cons, Bool.and_eq_true] at hw
    change TRun.seq s.runR P.runR σ = .ok o at h
    unfold TRun.seq at h
    split at h
    · rename_i o₁ hs
      obtain ⟨o₂, h₂, rfl⟩ := tmap_ok_inv h
      obtain ⟨hg₁, ha₁, he₁, hh₁⟩ := Stmt.run_frameW s hw.1 d b hs hb he hh
      obtain ⟨hg₂, ha₂, he₂, hh₂⟩ := Prog.run_frameW P hw.2 (d + s.ext.depth) b h₂
        (Nat.le_trans hb (List.IsPrefix.length_le o₁.ext)) he₁ hh₁
      refine ⟨hg₁.trans hg₂ _, ?_, he₂, hh₂⟩
      show TLocAgreeM _ d (Stmt.writesAt d s ++ Prog.writesAt (d + s.ext.depth) P) σ.env
        (TEnv.drop (s.ext.trans P.ext) o₂.st.env)
      rw [TEnv.drop_trans]
      exact ha₁.left.trans (TLocAgreeM.drop s.ext ha₂).right
    · cases h

end

end Progs

end Solidity
