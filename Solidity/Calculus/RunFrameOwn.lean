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

end Solidity
