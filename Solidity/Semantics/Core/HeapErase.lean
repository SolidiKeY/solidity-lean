import Solidity.Semantics.Core.Heap

/-!
# The typed heap erases to the untyped heap

Every typed heap operation (`Semantics/Core/Heap.lean`) agrees with its
untyped namesake in `Semantics.lean` on a state whose heap is the erasure
(`σ.heap = hp.erase`, and `σ.nextId = H.length` where it allocates), which is
therefore never stuck there: `getObj` finds every object, an allocation lands
at the next position, `copyStToM` allocates the same objects in the same
order, and `copyMToSt` never runs out of unvisited identities, since a
reference's target has a smaller type (`RemOk`), so the cycle guard
(`rem`) never fires.
-/

namespace Solidity.Core

open Semantics (structDef lookupBy setBy tyRank fieldsRank structRank)

/-! ## Weakening keeps identities -/

theorem MVal.erase_wk {H H' : HTy} (e : H <+: H') :
    (T : Ty) → (v : MVal H T) → MVal.erase T (MVal.wk e T v) = MVal.erase T v
  | .prim _, _ => rfl
  | .ref _, _ => rfl

theorem MFields.erase_wk {H H' : HTy} (e : H <+: H') : (fs : List (Name × Ty)) →
    (x : MFields H fs) → MFields.erase fs (MFields.wk e fs x) = MFields.erase fs x
  | [], _ => rfl
  | (f, T) :: fs, x => by
    show (f, MVal.erase T (MVal.wk e T x.1)) :: MFields.erase fs (MFields.wk e fs x.2) = _
    rw [MVal.erase_wk, MFields.erase_wk e fs]
    rfl

theorem MObj.erase_wk {H H' : HTy} (e : H <+: H') :
    (R : RefTy) → (o : MObj H R) → MObj.erase R (MObj.wk e R o) = MObj.erase R o
  | .struct s, o => congrArg Semantics.MObj.struct (MFields.erase_wk e (structDef s) o)
  | .array E, o => by
    show Semantics.MObj.array (((o : List (MVal H E)).map (MVal.wk e E)).map (MVal.erase E)) false = _
    rw [List.map_map]
    exact congrArg (Semantics.MObj.array · false)
      (List.map_congr_left (fun v _ => MVal.erase_wk e E v))
  | .fixed E n, o => by
    show Semantics.MObj.array
      (((o : {l : List (MVal H E) // l.length = n}).1.map (MVal.wk e E)).map (MVal.erase E)) true = _
    rw [List.map_map]
    exact congrArg (Semantics.MObj.array · true)
      (List.map_congr_left (fun v _ => MVal.erase_wk e E v))
  | .mapping _ _, o => (o : Empty).elim

theorem Objs.erase_wk {H H' : HTy} (e : H <+: H') : (start : Nat) → (Rs : List RefTy) →
    (os : Objs H Rs) → Objs.erase start Rs (Objs.wk e Rs os) = Objs.erase start Rs os
  | _, [], _ => rfl
  | start, R :: Rs, os => by
    show (start, MObj.erase R (MObj.wk e R os.1)) :: Objs.erase (start + 1) Rs (Objs.wk e Rs os.2) = _
    rw [MObj.erase_wk, Objs.erase_wk e (start + 1) Rs]
    rfl

/-! ## Objects by identity -/

theorem Objs.erase_snoc {H : HTy} {R : RefTy} (o : MObj H R) : (start : Nat) → (Rs : List RefTy) →
    (os : Objs H Rs) → Objs.erase start (Rs ++ [R]) (Objs.snoc o Rs os) =
      Objs.erase start Rs os ++ [(start + Rs.length, MObj.erase R o)]
  | start, [], _ => by
    show [(start, MObj.erase R o)] = [(start + 0, MObj.erase R o)]
    rw [Nat.add_zero]
  | start, R' :: Rs, os => by
    show (start, MObj.erase R' os.1) :: Objs.erase (start + 1) (Rs ++ [R]) (Objs.snoc o Rs os.2) = _
    rw [Objs.erase_snoc o (start + 1) Rs, List.length_cons, Nat.add_right_comm, Nat.add_assoc]
    rfl

theorem Objs.lookupBy_erase {H : HTy} {R : RefTy} : (Rs : List RefTy) → (os : Objs H Rs) →
    (start i : Nat) → (h : Rs[i]? = some R) →
    lookupBy (start + i) (Objs.erase start Rs os) = some (MObj.erase R (Objs.get Rs os i h))
  | [], _, _, _, h => by simp only [List.getElem?_nil, reduceCtorEq] at h
  | R' :: Rs, os, start, 0, h => by
    have hR : R' = R := Option.some.inj (by simpa only [List.getElem?_cons_zero] using h)
    subst hR
    simp only [Objs.erase, Objs.get, Nat.add_zero, lookupBy, ↓reduceIte]
  | R' :: Rs, os, start, i + 1, h => by
    have ne : ¬start + (i + 1) = start := by omega
    simp only [Objs.erase, Objs.get, lookupBy, if_neg ne]
    rw [show start + (i + 1) = start + 1 + i by omega]
    exact Objs.lookupBy_erase Rs os.2 (start + 1) i _

theorem Objs.lookupBy_erase_none {H : HTy} {n : Nat} : (Rs : List RefTy) → (os : Objs H Rs) →
    (start : Nat) → start + Rs.length ≤ n → lookupBy n (Objs.erase start Rs os) = none
  | [], _, _, _ => rfl
  | R :: Rs, os, start, hn => by
    have ne : ¬n = start := by simp only [List.length_cons] at hn; omega
    simp only [Objs.erase, lookupBy, if_neg ne]
    exact Objs.lookupBy_erase_none Rs os.2 (start + 1)
      (by simp only [List.length_cons] at hn; omega)

theorem Objs.setBy_erase {H : HTy} {R : RefTy} : (Rs : List RefTy) → (os : Objs H Rs) →
    (start i : Nat) → (h : Rs[i]? = some R) → (o : MObj H R) →
    setBy (start + i) (MObj.erase R o) (Objs.erase start Rs os) =
      Objs.erase start Rs (Objs.set Rs os i h o)
  | [], _, _, _, h, _ => by simp only [List.getElem?_nil, reduceCtorEq] at h
  | R' :: Rs, os, start, 0, h, o => by
    have hR : R' = R := Option.some.inj (by simpa only [List.getElem?_cons_zero] using h)
    subst hR
    simp only [Objs.erase, Objs.set, Nat.add_zero, setBy, ↓reduceIte]
  | R' :: Rs, os, start, i + 1, h, o => by
    have ne : ¬start + (i + 1) = start := by omega
    simp only [Objs.erase, Objs.set, setBy, if_neg ne]
    rw [show start + (i + 1) = start + 1 + i by omega,
      Objs.setBy_erase Rs os.2 (start + 1) i _ o]

theorem Objs.keys_erase {H : HTy} : (start : Nat) → (Rs : List RefTy) → (os : Objs H Rs) →
    (Objs.erase start Rs os).map Prod.fst = List.range' start Rs.length
  | _, [], _ => rfl
  | start, R :: Rs, os => by
    show start :: (Objs.erase (start + 1) Rs os.2).map Prod.fst = _
    rw [Objs.keys_erase (start + 1) Rs os.2]
    rfl

theorem setBy_eq_append_of_none {κ α : Type} [DecidableEq κ] {k : κ} {v : α} :
    (l : List (κ × α)) → lookupBy k l = none → setBy k v l = l ++ [(k, v)]
  | [], _ => rfl
  | (k', v') :: rest, h => by
    by_cases e : k = k'
    · simp only [lookupBy, if_pos e, reduceCtorEq] at h
    · simp only [lookupBy, if_neg e] at h
      simp only [setBy, if_neg e, List.cons_append, setBy_eq_append_of_none rest h]

/-! ## The state -/

namespace Heap

variable {H : HTy} {σ : Semantics.State} {hp : Heap H}

theorem into_into (σ : Semantics.State) {H' : HTy} (hp : Heap H) (hp' : Heap H') :
    Heap.into (Heap.into σ hp) hp' = Heap.into σ hp' := rfl

theorem into_self (hh : σ.heap = hp.erase) (hn : σ.nextId = H.length) : Heap.into σ hp = σ := by
  cases σ
  simp only [Heap.into] at hh hn ⊢
  rw [hh, hn]

theorem getObj_erase (hh : σ.heap = hp.erase) {R : RefTy} (r : HRef H R) :
    σ.getObj r.id = .ok (MObj.erase R (hp.get r)) := by
  have := Objs.lookupBy_erase H hp 0 r.id r.get?
  rw [Nat.zero_add] at this
  simp only [Semantics.State.getObj, hh, Heap.erase, this]
  rfl

theorem setObj_erase (hh : σ.heap = hp.erase) {R : RefTy} (r : HRef H R) (o : MObj H R) :
    σ.setObj r.id (MObj.erase R o) = { σ with heap := (hp.set r o).erase } := by
  have := Objs.setBy_erase H hp 0 r.id r.get? o
  rw [Nat.zero_add] at this
  simp only [Semantics.State.setObj, hh, Heap.erase, this]
  rfl

theorem alloc_erase (hh : σ.heap = hp.erase) (hn : σ.nextId = H.length) {R : RefTy}
    (o : MObj H R) :
    σ.alloc (MObj.erase R o) = (Heap.into σ (hp.alloc o).1, (hp.alloc o).2.id) := by
  have hnone : lookupBy H.length (Objs.erase 0 H hp) = none :=
    Objs.lookupBy_erase_none H hp 0 (by omega)
  simp only [Semantics.State.alloc, hh, hn, Heap.erase, setBy_eq_append_of_none _ hnone,
    Heap.into, Heap.alloc, Objs.erase_snoc, Objs.erase_wk, MObj.erase_wk, Nat.zero_add,
    List.length_append, List.length_cons, List.length_nil]

end Heap

/-! ## Storage to memory -/

mutual
theorem SVal.copyStToM_erase : {T : Ty} → (v : SVal T) → (h : T.mapFree = true) →
    {H : HTy} → (hp : Heap H) → (σ : Semantics.State) → σ.heap = hp.erase →
    σ.nextId = H.length →
    Semantics.copyStToM σ v.erase =
      .ok (Heap.into σ (v.copyStToM hp h).heap, MVal.erase T (v.copyStToM hp h).val)
  | _, @SVal.prim .bool _, _, _, hp, σ, hh, hn => by
    simp only [SVal.erase, PrimTy.erase, Semantics.copyStToM, SVal.copyStToM,
      Heap.into_self hh hn]
    rfl
  | _, @SVal.prim .uint _, _, _, hp, σ, hh, hn => by
    simp only [SVal.erase, PrimTy.erase, Semantics.copyStToM, SVal.copyStToM,
      Heap.into_self hh hn]
    rfl
  | _, @SVal.prim .int _, _, _, hp, σ, hh, hn => by
    simp only [SVal.erase, PrimTy.erase, Semantics.copyStToM, SVal.copyStToM,
      Heap.into_self hh hn]
    rfl
  | _, @SVal.struct s fs, h, _, hp, σ, hh, hn => by
    have hf := SFields.copyStToM_erase fs
      (mapFree_structDef s (by simpa only [Ty.mapFree, decide_eq_true_eq] using h)) hp σ hh hn
    simp only [SVal.erase, Semantics.copyStToM, hf, bind, Except.bind]
    have ha := Heap.alloc_erase (σ := Heap.into σ (SFields.copyStToM hp fs
      (mapFree_structDef s (by simpa only [Ty.mapFree, decide_eq_true_eq] using h))).heap)
      rfl rfl (R := .struct s) (SFields.copyStToM hp fs
      (mapFree_structDef s (by simpa only [Ty.mapFree, decide_eq_true_eq] using h))).val
    rw [SVal.copyStToM]
    exact (congrArg (fun p => Except.ok (p.1, Semantics.MVal.ref p.2)) ha).trans rfl
  | _, @SVal.array E e _, h, _, hp, σ, hh, hn => by
    have hl := SList.copyStToM_erase e (by simpa only [Ty.mapFree] using h) hp σ hh hn
    simp only [SVal.erase, Semantics.copyStToM, hl, bind, Except.bind]
    have ha := Heap.alloc_erase (σ := Heap.into σ (SList.copyStToM hp e
      (by simpa only [Ty.mapFree] using h)).heap) rfl rfl (R := .array E)
      (SList.copyStToM hp e (by simpa only [Ty.mapFree] using h)).val
    rw [SVal.copyStToM]
    exact (congrArg (fun p => Except.ok (p.1, Semantics.MVal.ref p.2)) ha).trans rfl
  | _, @SVal.fixed E n e, h, _, hp, σ, hh, hn => by
    have hl := SVec.copyStToM_erase e (by simpa only [Ty.mapFree] using h) hp σ hh hn
    simp only [SVal.erase, Semantics.copyStToM, hl, bind, Except.bind]
    have ha := Heap.alloc_erase (σ := Heap.into σ (SVec.copyStToM hp e
      (by simpa only [Ty.mapFree] using h)).heap) rfl rfl (R := .fixed E n)
      (SVec.copyStToM hp e (by simpa only [Ty.mapFree] using h)).val
    rw [SVal.copyStToM]
    exact (congrArg (fun p => Except.ok (p.1, Semantics.MVal.ref p.2)) ha).trans rfl
  | _, .map _ _, h, _, _, _, _, _ => by
    simp only [Ty.mapFree, Bool.false_eq_true] at h

theorem SFields.copyStToM_erase : {fs : List (Name × Ty)} → (st : SFields fs) →
    (h : ∀ fT ∈ fs, fT.2.mapFree = true) →
    {H : HTy} → (hp : Heap H) → (σ : Semantics.State) → σ.heap = hp.erase →
    σ.nextId = H.length →
    Semantics.copyStFields σ st.erase =
      .ok (Heap.into σ (st.copyStToM hp h).heap, MFields.erase fs (st.copyStToM hp h).val)
  | _, .nil, _, _, hp, σ, hh, hn => by
    simp only [SFields.erase, Semantics.copyStFields, SFields.copyStToM, Heap.into_self hh hn]
    rfl
  | _, @SFields.cons f T _ v rest, h, _, hp, σ, hh, hn => by
    have h₁ := SVal.copyStToM_erase v (h _ List.mem_cons_self) hp σ hh hn
    have h₂ := SFields.copyStToM_erase rest (fun fT hm => h fT (List.mem_cons_of_mem _ hm))
      (SVal.copyStToM hp v (h _ List.mem_cons_self)).heap
      (Heap.into σ (SVal.copyStToM hp v (h _ List.mem_cons_self)).heap) rfl rfl
    simp only [SFields.erase, Semantics.copyStFields, h₁, h₂, bind, Except.bind,
      Heap.into_into, SFields.copyStToM, MFields.erase, MVal.erase_wk]

theorem SList.copyStToM_erase : {E : Ty} → (l : SList E) → (h : E.mapFree = true) →
    {H : HTy} → (hp : Heap H) → (σ : Semantics.State) → σ.heap = hp.erase →
    σ.nextId = H.length →
    Semantics.copyStElems σ l.erase =
      .ok (Heap.into σ (l.copyStToM hp h).heap, (l.copyStToM hp h).val.map (MVal.erase E))
  | _, .nil, _, _, hp, σ, hh, hn => by
    simp only [SList.erase, Semantics.copyStElems, SList.copyStToM, Heap.into_self hh hn]
    rfl
  | E, .cons v rest, h, _, hp, σ, hh, hn => by
    have h₁ := SVal.copyStToM_erase v h hp σ hh hn
    have h₂ := SList.copyStToM_erase rest h (SVal.copyStToM hp v h).heap
      (Heap.into σ (SVal.copyStToM hp v h).heap) rfl rfl
    simp only [SList.erase, Semantics.copyStElems, h₁, h₂, bind, Except.bind,
      Heap.into_into, SList.copyStToM, List.map_cons, MVal.erase_wk]

theorem SVec.copyStToM_erase : {E : Ty} → {n : Nat} → (l : SVec E n) → (h : E.mapFree = true) →
    {H : HTy} → (hp : Heap H) → (σ : Semantics.State) → σ.heap = hp.erase →
    σ.nextId = H.length →
    Semantics.copyStElems σ l.erase =
      .ok (Heap.into σ (l.copyStToM hp h).heap, (l.copyStToM hp h).val.1.map (MVal.erase E))
  | _, _, .nil, _, _, hp, σ, hh, hn => by
    simp only [SVec.erase, Semantics.copyStElems, SVec.copyStToM, Heap.into_self hh hn]
    rfl
  | E, _, .cons v rest, h, _, hp, σ, hh, hn => by
    have h₁ := SVal.copyStToM_erase v h hp σ hh hn
    have h₂ := SVec.copyStToM_erase rest h (SVal.copyStToM hp v h).heap
      (Heap.into σ (SVal.copyStToM hp v h).heap) rfl rfl
    simp only [SVec.erase, Semantics.copyStElems, h₁, h₂, bind, Except.bind,
      Heap.into_into, SVec.copyStToM, List.map_cons, MVal.erase_wk]
end

/-- `allocDefault` on the erasure: the default object, at the next position. -/
theorem Heap.allocDefault_erase {H : HTy} {σ : Semantics.State} {hp : Heap H}
    (hh : σ.heap = hp.erase) (hn : σ.nextId = H.length) (R : RefTy)
    (h : (Ty.ref R).mapFree = true) :
    Semantics.allocDefault σ R =
      .ok (Heap.into σ (hp.allocDefault R h).heap, (hp.allocDefault R h).val.id) := by
  have hc := SVal.copyStToM_erase (SVal.dflt (.ref R)) h hp σ hh hn
  rw [SVal.dflt_erase] at hc
  simp only [Semantics.allocDefault, Semantics.defaultForRef, hc]
  rfl

/-! ## Memory to storage

The untyped copy consumes an identity as it follows it (`rem`); the typed
one recurses on the type.  They agree because an object reached below one
of type `R` has a smaller type, by rank, or within one rank by size, so it
is not the one just consumed. -/

/-- `T` below `U`: by rank, then by size. -/
def TyLt (T U : Ty) : Prop :=
  tyRank T < tyRank U ∨ (tyRank T = tyRank U ∧ sizeOf T < sizeOf U)

/-- `T` at most `U`. -/
def TyLe (T U : Ty) : Prop :=
  tyRank T < tyRank U ∨ (tyRank T = tyRank U ∧ sizeOf T ≤ sizeOf U)

/-- Every object of a type at most `T` is still unvisited. -/
def RemOk (H : HTy) (rem : List Nat) (T : Ty) : Prop :=
  ∀ j R, H[j]? = some R → TyLe (.ref R) T → j ∈ rem

theorem RemOk.self {H : HTy} {rem : List Nat} {R : RefTy} {i : Nat} (hr : RemOk H rem (.ref R))
    (hi : H[i]? = some R) : i ∈ rem :=
  hr i R hi (Or.inr ⟨rfl, Nat.le_refl _⟩)

theorem RemOk.child {H : HTy} {rem : List Nat} {R : RefTy} {i : Nat} {T : Ty}
    (hr : RemOk H rem (.ref R)) (hi : H[i]? = some R) (hT : TyLt T (.ref R)) :
    RemOk H (rem.erase i) T := by
  intro j R' hj hle
  have hlt : TyLt (.ref R') (.ref R) := by
    unfold TyLt TyLe at *
    omega
  have hj' : j ∈ rem := hr j R' hj (by unfold TyLt TyLe at *; omega)
  have hne : j ≠ i := by
    intro e
    subst e
    rw [hi] at hj
    cases Option.some.inj hj
    unfold TyLt at hlt
    omega
  exact (List.mem_erase_of_ne hne).mpr hj'

theorem TyLt.field {s : Name} {T : Ty} {f : Name} (hm : (f, T) ∈ structDef s) :
    TyLt T (.ref (.struct s)) :=
  Or.inl (Nat.lt_of_le_of_lt (tyRank_le_fieldsRank hm) (Semantics.structDef_rank_lt s))

theorem TyLt.array (E : Ty) : TyLt E (.ref (.array E)) :=
  Or.inr ⟨rfl, by simp only [Ty.ref.sizeOf_spec, RefTy.array.sizeOf_spec]; omega⟩

theorem TyLt.fixed (E : Ty) (n : Nat) : TyLt E (.ref (.fixed E n)) :=
  Or.inl (by simp only [tyRank]; omega)

theorem RemOk.all {H : HTy} (hp : Heap H) (T : Ty) : RemOk H (hp.erase.map Prod.fst) T := by
  intro j R hj _
  rw [Heap.erase, Objs.keys_erase, List.mem_range'_1]
  exact ⟨Nat.zero_le _, by rw [Nat.zero_add]; exact (List.getElem?_eq_some_iff.mp hj).1⟩

section CopyMem

variable {H : HTy} {σ : Semantics.State} {hp : Heap H}

theorem MFields.copyBelow_erase (hh : σ.heap = hp.erase) (k : Nat)
    (ih : (T : Ty) → tyRank T < k → MVal H T → SVal T)
    (hih : ∀ T (h : tyRank T < k) (v : MVal H T) rem, RemOk H rem T →
      Semantics.copyMToSt σ rem (MVal.erase T v) = .ok (ih T h v).erase)
    (rem : List Nat) : (fs : List (Name × Ty)) → (hfs : fieldsRank fs < k) →
    (x : MFields H fs) → (∀ fT ∈ fs, RemOk H rem fT.2) →
    Semantics.copyMFields σ rem (MFields.erase fs x) =
      .ok (SFields.erase (MFields.copyBelow k ih fs hfs x))
  | [], _, _, _ => by
    simp only [MFields.erase, Semantics.copyMFields, MFields.copyBelow, SFields.erase]
  | (f, T) :: fs, hfs, x, hr => by
    simp only [MFields.erase, Semantics.copyMFields, MFields.copyBelow, SFields.erase,
      hih T (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hfs) x.1 rem (hr _ List.mem_cons_self),
      bind, Except.bind,
      MFields.copyBelow_erase hh k ih hih rem fs (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hfs) x.2
        (fun fT hm => hr fT (List.mem_cons_of_mem _ hm))]

theorem copyMElems_erase {E : Ty} (f : MVal H E → SVal E) (rem : List Nat)
    (hE : ∀ v, Semantics.copyMToSt σ rem (MVal.erase E v) = .ok (f v).erase) :
    (l : List (MVal H E)) →
    Semantics.copyMElems σ rem (l.map (MVal.erase E)) = .ok (l.map (fun v => (f v).erase))
  | [] => by simp only [List.map_nil, Semantics.copyMElems]
  | v :: rest => by
    simp only [List.map_cons, Semantics.copyMElems, hE v, bind, Except.bind,
      copyMElems_erase f rem hE rest]

theorem SVec.erase_ofLen {α : Type} {E : Ty} (f : α → SVal E) : (n : Nat) → (l : List α) →
    (h : l.length = n) → (SVec.ofLen f n l h).erase = l.map (fun v => (f v).erase)
  | 0, [], _ => by with_unfolding_all rfl
  | n + 1, x :: xs, h => by
    simp only [SVec.ofLen, SVec.erase, List.map_cons, SVec.erase_ofLen f n xs]
  | 0, _ :: _, h => by simp only [List.length_cons, Nat.add_one_ne_zero] at h
  | _ + 1, [], h => by simp only [List.length_nil, Nat.zero_ne_add_one] at h

mutual
theorem MVal.copyAt_erase (hh : σ.heap = hp.erase) (k : Nat)
    (ih : (T : Ty) → tyRank T < k → MVal H T → SVal T)
    (hih : ∀ T (h : tyRank T < k) (v : MVal H T) rem, RemOk H rem T →
      Semantics.copyMToSt σ rem (MVal.erase T v) = .ok (ih T h v).erase) :
    (T : Ty) → (h : tyRank T < k + 1) → (v : MVal H T) → (rem : List Nat) → RemOk H rem T →
    Semantics.copyMToSt σ rem (MVal.erase T v) = .ok (MVal.copyAt hp k ih T h v).erase
  | .prim .bool, _, _, _, _ => by
    simp only [MVal.erase, PrimTy.erase, Semantics.copyMToSt, MVal.copyAt, SVal.erase]
  | .prim .uint, _, _, _, _ => by
    simp only [MVal.erase, PrimTy.erase, Semantics.copyMToSt, MVal.copyAt, SVal.erase]
  | .prim .int, _, _, _, _ => by
    simp only [MVal.erase, PrimTy.erase, Semantics.copyMToSt, MVal.copyAt, SVal.erase]
  | .ref R, h, r, rem, hr => MVal.copyRefAt_erase hh k ih hih R h r rem hr

theorem MVal.copyRefAt_erase (hh : σ.heap = hp.erase) (k : Nat)
    (ih : (T : Ty) → tyRank T < k → MVal H T → SVal T)
    (hih : ∀ T (h : tyRank T < k) (v : MVal H T) rem, RemOk H rem T →
      Semantics.copyMToSt σ rem (MVal.erase T v) = .ok (ih T h v).erase) :
    (R : RefTy) → (h : tyRank (.ref R) < k + 1) → (r : HRef H R) → (rem : List Nat) →
    RemOk H rem (.ref R) →
    Semantics.copyMToSt σ rem (.ref r.id) = .ok (MVal.copyRefAt hp k ih R h r).erase
  | .struct s, h, r, rem, hr => by
    rw [Semantics.copyMToSt, dif_pos (hr.self r.get?), Heap.getObj_erase hh r]
    simp only [MObj.erase, bind, Except.bind,
      MFields.copyBelow_erase hh k ih hih (rem.erase r.id) (structDef s)
        (Nat.lt_of_lt_of_le (Semantics.structDef_rank_lt s) (Nat.le_of_lt_succ h)) (hp.get r)
        (fun fT hm => hr.child r.get? (TyLt.field hm)), MVal.copyRefAt, SVal.erase]
  | .array E, h, r, rem, hr => by
    rw [Semantics.copyMToSt, dif_pos (hr.self r.get?), Heap.getObj_erase hh r]
    simp only [MObj.erase, bind, Except.bind,
      copyMElems_erase (MVal.copyAt hp k ih E (by simpa only [tyRank] using h)) (rem.erase r.id)
        (fun v => MVal.copyAt_erase hh k ih hih E _ v _ (hr.child r.get? (TyLt.array E))),
      MVal.copyRefAt, SVal.erase, SList.erase_ofList, List.map_map, SList.erase]
    rfl
  | .fixed E n, h, r, rem, hr => by
    rw [Semantics.copyMToSt, dif_pos (hr.self r.get?), Heap.getObj_erase hh r]
    simp only [MObj.erase, bind, Except.bind,
      copyMElems_erase (MVal.copyAt hp k ih E (Nat.lt_of_succ_lt (by simpa only [tyRank] using h)))
        (rem.erase r.id)
        (fun v => MVal.copyAt_erase hh k ih hih E _ v _ (hr.child r.get? (TyLt.fixed E n))),
      MVal.copyRefAt, SVal.erase, SVec.erase_ofLen]
  | .mapping _ _, _, r, _, _ => (hp.get r : Empty).elim
end

theorem MVal.copyBelow_erase (hh : σ.heap = hp.erase) : (k : Nat) → (T : Ty) →
    (h : tyRank T < k) → (v : MVal H T) → (rem : List Nat) → RemOk H rem T →
    Semantics.copyMToSt σ rem (MVal.erase T v) = .ok (MVal.copyBelow hp k T h v).erase
  | 0, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | k + 1, T, h, v, rem, hr =>
    MVal.copyAt_erase hh k (MVal.copyBelow hp k) (fun T h v rem hr =>
      MVal.copyBelow_erase hh k T h v rem hr) T h v rem hr

/-- `copyMem` on the erasure: the typed copy, never stuck. -/
theorem MVal.copyMem_erase (hh : σ.heap = hp.erase) {T : Ty} (v : MVal H T) :
    Semantics.copyMem σ (MVal.erase T v) = .ok (v.copyMToSt hp).erase := by
  unfold Semantics.copyMem
  rw [hh]
  exact MVal.copyBelow_erase hh _ T _ v _ (RemOk.all hp T)

end CopyMem

/-! ## Members and elements -/

theorem MFields.lookupBy_erase {H : HTy} {f : Name} : (fs : List (Name × Ty)) → {T : Ty} →
    (x : MFields H fs) → (h : lookupBy f fs = some T) →
    lookupBy f (MFields.erase fs x) = some (MVal.erase T (MFields.get fs x h))
  | [], _, _, h => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, _, x, h => by
    by_cases e : f = f'
    · subst e
      have hT : T' = _ := SFields.lookupBy_cons_pos rfl h
      subst hT
      simp only [MFields.erase, MFields.get, lookupBy, ↓reduceIte, ↓reduceDIte]
    · simp only [MFields.erase, MFields.get, lookupBy, if_neg e, dif_neg e]
      exact MFields.lookupBy_erase fs x.2 _

theorem MFields.setBy_erase {H : HTy} {f : Name} : (fs : List (Name × Ty)) → {T : Ty} →
    (x : MFields H fs) → (h : lookupBy f fs = some T) → (v : MVal H T) →
    setBy f (MVal.erase T v) (MFields.erase fs x) = MFields.erase fs (MFields.set fs x h v)
  | [], _, _, h, _ => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, _, x, h, v => by
    by_cases e : f = f'
    · subst e
      have hT : T' = _ := SFields.lookupBy_cons_pos rfl h
      subst hT
      simp only [MFields.erase, MFields.set, setBy, ↓reduceIte, ↓reduceDIte]
    · simp only [MFields.erase, MFields.set, setBy, if_neg e, dif_neg e]
      exact congrArg _ (MFields.setBy_erase fs x.2 _ v)

/-- Whether an array kind is the fixed-size one. -/
def _root_.Solidity.ArrTy.isFixed : {R : RefTy} → {E : Ty} → ArrTy R E → Bool
  | _, _, .dyn => false
  | _, _, .fixed => true

theorem MObj.erase_arr {H : HTy} : {R : RefTy} → {E : Ty} → (a : ArrTy R E) → (o : MObj H R) →
    MObj.erase R o = .array ((MObj.elems a o).map (MVal.erase E)) a.isFixed
  | _, _, .dyn, _ => by rw [MObj.elems_dyn]; rfl
  | _, _, .fixed, _ => by rw [MObj.elems_fixed]; rfl

theorem MObj.erase_setElem {H : HTy} : {R : RefTy} → {E : Ty} → (a : ArrTy R E) →
    (o : MObj H R) → (i : Nat) → (v : MVal H E) →
    MObj.erase R (MObj.setElem a o i v) =
      .array (((MObj.elems a o).map (MVal.erase E)).set i (MVal.erase E v)) a.isFixed
  | _, _, .dyn, _, _, _ => by
    simp only [MObj.setElem, MObj.erase, MObj.elems, List.map_set, ArrTy.isFixed]
  | _, _, .fixed, _, _, _ => by
    simp only [MObj.setElem, MObj.erase, MObj.elems, List.map_set, ArrTy.isFixed]

namespace Heap

variable {H : HTy} {σ : Semantics.State} {hp : Heap H}

/-- `memWriteField` on the erasure. -/
theorem memWriteField_erase (hh : σ.heap = hp.erase) {s f : Name} {T : Ty}
    (r : HRef H (.struct s)) (h : lookupBy f (structDef s) = some T) (v : MVal H T) :
    Solidity.memWriteField σ r.id f (MVal.erase T v) =
      .ok { σ with heap := (hp.setField r h v).erase } := by
  simp only [Solidity.memWriteField, getObj_erase hh r, bind, Except.bind]
  show Except.ok (σ.setObj r.id (Semantics.MObj.struct
    (setBy f (MVal.erase T v) (MFields.erase (structDef s) (hp.get r))))) = _
  rw [MFields.setBy_erase (structDef s) (hp.get r) h v]
  exact congrArg Except.ok (setObj_erase hh r (R := .struct s) _)

/-- `memWriteIndex` on the erasure: a revert out of bounds. -/
theorem memWriteIndex_erase (hh : σ.heap = hp.erase) {R : RefTy} {E : Ty}
    (r : HRef H R) (a : ArrTy R E) (i : Int) (v : MVal H E) :
    Solidity.memWriteIndex σ r.id i (MVal.erase E v) =
      toRes (fun hp' : Heap H => { σ with heap := hp'.erase }) (hp.setIndex r a i v) := by
  simp only [Solidity.memWriteIndex, getObj_erase hh r, bind, Except.bind,
    MObj.erase_arr a (hp.get r), Heap.setIndex, List.length_map]
  split
  · rw [← MObj.erase_setElem a (hp.get r) i.toNat v, setObj_erase hh r]
    rfl
  · rfl

/-- `memArrayLen` on the erasure. -/
theorem memArrayLen_erase (hh : σ.heap = hp.erase) {R : RefTy} {E : Ty}
    (r : HRef H R) (a : ArrTy R E) :
    Solidity.memArrayLen σ r.id = .ok (.int (hp.len r a)) := by
  simp only [Solidity.memArrayLen, getObj_erase hh r, bind, Except.bind,
    MObj.erase_arr a (hp.get r), List.length_map, Heap.len]
  rfl

/-- A member read on the erasure (`MLoc.read`'s member arm). -/
theorem readField_erase (hh : σ.heap = hp.erase) {s f : Name} {T : Ty}
    (r : HRef H (.struct s)) (h : lookupBy f (structDef s) = some T) :
    (do
      match ← σ.getObj r.id with
      | .struct fields =>
        match lookupBy f fields with
        | some v => pure v
        | none => .error .stuck
      | .array _ _ => .error .stuck : Semantics.Res Semantics.MVal) =
      .ok (MVal.erase T (hp.field r h)) := by
  simp only [getObj_erase hh r, bind, Except.bind]
  show (match lookupBy f (MFields.erase (structDef s) (hp.get r)) with
    | some v => pure v | none => .error .stuck : Semantics.Res Semantics.MVal) = _
  rw [MFields.lookupBy_erase (structDef s) (hp.get r) h]
  rfl

/-- An element read on the erasure (`MLoc.read`'s index arm): a revert out
of bounds. -/
theorem readIndex_erase (hh : σ.heap = hp.erase) {R : RefTy} {E : Ty}
    (r : HRef H R) (a : ArrTy R E) (i : Int) :
    (do
      match ← σ.getObj r.id with
      | .array elems _ =>
        if h : 0 ≤ i ∧ i.toNat < elems.length then pure (elems.get ⟨i.toNat, h.2⟩)
        else .error .revert
      | .struct _ => .error .stuck : Semantics.Res Semantics.MVal) =
      toRes (MVal.erase E) (hp.index r a i) := by
  simp only [getObj_erase hh r, bind, Except.bind, MObj.erase_arr a (hp.get r), Heap.index]
  by_cases h0 : 0 ≤ i
  · by_cases hl : i.toNat < (MObj.elems a (hp.get r)).length
    · simp only [List.length_map, h0, hl, and_self, ↓reduceDIte, ↓reduceIte, List.get_eq_getElem,
        List.getElem_map, List.getElem?_eq_getElem hl, toRes]
      rfl
    · simp only [List.length_map, h0, hl, and_false, ↓reduceDIte, ↓reduceIte,
        List.getElem?_eq_none (Nat.le_of_not_lt hl), toRes]
  · simp only [h0, false_and, ↓reduceDIte, ↓reduceIte, toRes]

end Heap

end Solidity.Core
