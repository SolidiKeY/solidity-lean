import Solidity.Calculus.StateFacts
import Solidity.Typing.Values

/-!
# The Theory of memory, typed

solkey's memory theory (`memoryRules.key`, `structMemoryRules.key`) read on
the typed heap: a memory is a heap grown from the global part's
(`Grown H`), an address an identity with a member or an element
(`MAddrT T`), and each law a statement about `Grown.readT`, `writeT` and
the allocations (`Heap.allocDefault`, `SVal.copyStToM`), generic in the
types it is read at, as the storage laws are generic over their
locations (`Theory/Typed/Obs.lean`).

* **readOnWrite**, its `\then` and its `\else`: a write reads back where it
  lands, and leaves every address apart from it (`Grown.writeT_facts`,
  `Heap.readAddr_writeAddr_same`, `Heap.readAddr_writeAddr_apart`).
* **readOnAddM** `\else`: an allocation keeps every older object
  (`Heap.Keeps`, `Heap.readAddr_allocDefault`, `MAddrT.resolve_wk`); and,
  Lean only, its objects are new (`Grown.alloc_id_ge`), the freshness
  behind `newFromAdd`.
* **readOnAddM** `\then`, then **initMember**, **initSize**: a fresh object
  reads its default (`Heap.Dflt`, `Heap.dflt_allocDefault`,
  `Heap.initMember`, `Heap.initSize`).
* **readFromCopyToStorage**, its `\then` and its `\else`, and
  **findOnCopy**: a copy between storage and memory reads what it copied,
  and leaves the older objects (`SVal.copyStToM_field`,
  `SVal.keeps_copyStToM`, `Heap.readAddr_copyStToM`, `MVal.copyMToSt_field`).

The section at the end restates each law under its solkey taclet's name,
a taclet's `\else` as its frame (`readOnWriteFrame`), as the storage laws
name theirs (`Obs.findOnSaveFrame`).

The laws are proved on the typed heap alone: no erasure is read (W10.5.4,
`docs/intrinsic.md`).
-/

namespace Solidity

open Semantics (lookupBy structDef tyRank fieldsRank)

section Heap

theorem Objs.get_set_same {H : HTy} {R : RefTy} : (Rs : List RefTy) → (os : Objs H Rs) →
    (i : Nat) → (h : Rs[i]? = some R) → (o : MObj H R) → Objs.get Rs (Objs.set Rs os i h o) i h = o
  | [], _, _, h, _ => absurd h (by simp only [List.getElem?_nil, reduceCtorEq, not_false_eq_true])
  | R' :: _, _, 0, h, _ => by
    obtain rfl : R' = R := Option.some.inj (by simpa only [List.getElem?_cons_zero] using h)
    rfl
  | _ :: Rs, os, i + 1, h, o => Objs.get_set_same Rs os.2 i _ o

theorem Objs.get_set_ne {H : HTy} {R R₂ : RefTy} : (Rs : List RefTy) → (os : Objs H Rs) →
    (i j : Nat) → i ≠ j → (h : Rs[i]? = some R) → (h₂ : Rs[j]? = some R₂) → (o : MObj H R) →
    Objs.get Rs (Objs.set Rs os i h o) j h₂ = Objs.get Rs os j h₂
  | [], _, _, _, _, h, _, _ => absurd h (by simp only [List.getElem?_nil, reduceCtorEq, not_false_eq_true])
  | _ :: _, _, 0, 0, hij, _, _, _ => absurd rfl hij
  | _ :: _, _, 0, _ + 1, _, _, _, _ => rfl
  | _ :: _, _, _ + 1, 0, _, _, _, _ => rfl
  | _ :: Rs, os, i + 1, j + 1, hij, h, h₂, o =>
    Objs.get_set_ne Rs os.2 i j (fun e => hij (congrArg (· + 1) e)) _ _ o

theorem Heap.get_set_same {H : HTy} {R : RefTy} (hp : Heap H) (r : HRef H R) (o : MObj H R) :
    (hp.set r o).get r = o :=
  Objs.get_set_same H hp r.id r.get? o

theorem Heap.get_set_ne {H : HTy} {R R₂ : RefTy} (hp : Heap H) (r : HRef H R) (r₂ : HRef H R₂)
    (hne : r.id ≠ r₂.id) (o : MObj H R) : (hp.set r o).get r₂ = hp.get r₂ :=
  Objs.get_set_ne H hp r.id r₂.id hne r.get? r₂.get? o

/-- Two references of one identity are one reference. -/
theorem HRef.heq_of_id {H : HTy} {R R₂ : RefTy} (r : HRef H R) (r₂ : HRef H R₂) (e : r.id = r₂.id) :
    R = R₂ ∧ HEq r r₂ := by
  rcases r with ⟨i, h⟩
  rcases r₂ with ⟨j, h₂⟩
  simp only at e
  subst e
  obtain rfl : R = R₂ := Option.some.inj (h.symm.trans h₂)
  exact ⟨rfl, HEq.rfl⟩

theorem MFields.get_set_same {H : HTy} {f : Name} : (fs : List (Name × Ty)) → {T : Ty} →
    (x : MFields H fs) → (h : Semantics.lookupBy f fs = some T) → (v : MVal H T) →
    MFields.get fs (MFields.set fs x h v) h = v
  | [], _, _, h, _ => absurd h (by simp only [Semantics.lookupBy, reduceCtorEq, not_false_eq_true])
  | (f', T') :: fs, T, x, h, v => by
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      simp only [MFields.get, MFields.set, e, dite_true]
    · simp only [MFields.get, MFields.set, e, dite_false]
      exact MFields.get_set_same fs x.2 _ v

theorem MFields.get_set_ne {H : HTy} {f g : Name} : (fs : List (Name × Ty)) → {T U : Ty} →
    (x : MFields H fs) → (h : Semantics.lookupBy f fs = some T) →
    (hg : Semantics.lookupBy g fs = some U) → f ≠ g →
    (v : MVal H T) → MFields.get fs (MFields.set fs x h v) hg = MFields.get fs x hg
  | [], _, _, _, h, _, _, _ => absurd h (by simp only [Semantics.lookupBy, reduceCtorEq, not_false_eq_true])
  | (f', T') :: fs, T, U, x, h, hg, hfg, v => by
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      have eg : ¬ g = f' := fun h' => hfg (e.trans h'.symm)
      simp only [MFields.get, MFields.set, e, dite_true, eg, dite_false]
    · by_cases eg : g = f'
      · simp only [MFields.get, MFields.set, e, dite_false, eg, dite_true]
      · simp only [MFields.get, MFields.set, e, dite_false, eg]
        exact MFields.get_set_ne fs x.2 _ _ hfg v

theorem MObj.elems_setElem {H : HTy} {R : RefTy} {E : Ty} (a : ArrTy R E) (o : MObj H R) (i : Nat)
    (v : MVal H E) : MObj.elems a (MObj.setElem a o i v) = (MObj.elems a o).set i v := by
  cases a <;> simp only [MObj.setElem_dyn, MObj.elems_dyn, MObj.setElem_fixed, MObj.elems_fixed]

/-- An array object is not a struct. -/
theorem ArrTy.ne_struct {R : RefTy} {E : Ty} (a : ArrTy R E) (s : Name) : R ≠ .struct s := by
  cases a <;> exact fun h => RefTy.noConfusion h

/-- Two addresses that never meet: two members, or a member and an element
(two kinds of object), or two elements of one array at two indices. -/
def MAddr.Apart {H : HTy} {T U : Ty} : MAddr H T → MAddr H U → Prop
  | @MAddr.field _ _ f _ _ _, @MAddr.field _ _ g _ _ _ => f ≠ g
  | .field .., .index .. => True
  | .index .., .field .. => True
  | .index r _ i, .index r' _ j => r.id = r'.id → i ≠ j

/-- **A write reads back where it lands** (`readOnWrite`). -/
theorem Heap.readAddr_writeAddr_same {H : HTy} {T : Ty} {hp hp' : Heap H} {ad : MAddr H T}
    {v : MVal H T} (h : hp.writeAddr ad v = some hp') : hp'.readAddr ad = some v := by
  cases ad with
  | field r hf =>
    simp only [Heap.writeAddr, Option.some.injEq] at h
    subst h
    simp only [Heap.readAddr, Heap.field, Heap.setField, Heap.get_set_same, MFields.get_set_same]
  | index r a i =>
    simp only [Heap.writeAddr, Heap.setIndex] at h
    split at h
    · rename_i hb
      simp only [Option.some.injEq] at h
      subst h
      simp only [Heap.readAddr, Heap.index, Heap.get_set_same, MObj.elems_setElem,
        List.getElem?_set_self hb]
    · simp only [reduceCtorEq] at h

/-- **A write leaves an address apart from it** (`readOnWrite` `\else`). -/
theorem Heap.readAddr_writeAddr_apart {H : HTy} {T U : Ty} {hp hp' : Heap H} {ad : MAddr H T}
    {bd : MAddr H U} {v : MVal H T} (h : hp.writeAddr ad v = some hp') (hab : ad.Apart bd) :
    hp'.readAddr bd = hp.readAddr bd := by
  cases ad with
  | field r hf =>
    simp only [Heap.writeAddr, Option.some.injEq] at h
    subst h
    cases bd with
    | field r' hg =>
      simp only [Heap.readAddr, Heap.field, Heap.setField, Option.some.injEq]
      by_cases e : r.id = r'.id
      · obtain ⟨hR, hr⟩ := HRef.heq_of_id r r' e
        cases hR
        cases hr
        rw [Heap.get_set_same, MFields.get_set_ne _ _ _ _ hab]
      · rw [Heap.get_set_ne _ r r' e]
    | index r' a j =>
      have e : r.id ≠ r'.id := fun e => ArrTy.ne_struct a _ (HRef.heq_of_id r r' e).1.symm
      simp only [Heap.readAddr, Heap.index, Heap.setField, Heap.get_set_ne _ r r' e]
  | index r a i =>
    simp only [Heap.writeAddr, Heap.setIndex] at h
    split at h
    · rename_i hb
      simp only [Option.some.injEq] at h
      subst h
      cases bd with
      | field r' hg =>
        have e : r.id ≠ r'.id := fun e => ArrTy.ne_struct a _ (HRef.heq_of_id r r' e).1
        simp only [Heap.readAddr, Heap.field, Heap.get_set_ne _ r r' e]
      | index r' a' j =>
        by_cases e : r.id = r'.id
        · obtain ⟨hR, hr⟩ := HRef.heq_of_id r r' e
          cases hR
          cases hr
          have hij : i ≠ j := hab e
          cases a <;> cases a' <;>
          · simp only [Heap.readAddr, Heap.index, Heap.get_set_same, MObj.elems_setElem]
            have hij' : i.1 ≠ j.1 := fun e => hij (Subtype.ext e)
            have hn : i.1.toNat ≠ j.1.toNat := by
              have := PrimTy.uint_nonneg i; have := PrimTy.uint_nonneg j; omega
            simp only [List.getElem?_set_ne hn]
        · simp only [Heap.readAddr, Heap.index, Heap.get_set_ne _ r r' e]
    · simp only [reduceCtorEq] at h

end Heap

/-- The object an address is in. -/
def MAddrT.id {T : Ty} : MAddrT T → Nat
  | .field id _ => id
  | .index id _ _ => id


theorem HRef.id_lt {H : HTy} {R : RefTy} (r : HRef H R) : r.id < H.length :=
  (List.getElem?_eq_some_iff.1 r.get?).1


/-! ## A grown heap keeps the older objects

An allocation appends an object and leaves every older one as it was, its
references weakened into the grown typing (`Heap.Keeps`): so does a copy
into memory (`SVal.keeps_copyStToM`), a chain of allocations, and so
`Heap.allocDefault`.  An address of an older object therefore reads what
it read, weakened (`Heap.Keeps.readAddr`): `readOnAddM`'s `\else`. -/

section Keeps

theorem MVal.wk_wk {H H₁ H₂ : HTy} (e₁ : H <+: H₁) (e₂ : H₁ <+: H₂) :
    (T : Ty) → (v : MVal H T) → MVal.wk e₂ T (MVal.wk e₁ T v) = MVal.wk (e₁.trans e₂) T v
  | .prim _, _ => rfl
  | .ref _, _ => rfl

theorem MVal.wk_refl {H : HTy} : (T : Ty) → (v : MVal H T) → MVal.wk (List.prefix_refl H) T v = v
  | .prim _, _ => rfl
  | .ref _, _ => rfl

theorem MFields.wk_wk {H H₁ H₂ : HTy} (e₁ : H <+: H₁) (e₂ : H₁ <+: H₂) :
    (fs : List (Name × Ty)) → (x : MFields H fs) →
    MFields.wk e₂ fs (MFields.wk e₁ fs x) = MFields.wk (e₁.trans e₂) fs x
  | [], _ => rfl
  | (_, T) :: fs, x => by
    simp only [MFields.wk, MVal.wk_wk e₁ e₂ T, MFields.wk_wk e₁ e₂ fs]

theorem MFields.wk_refl {H : HTy} : (fs : List (Name × Ty)) → (x : MFields H fs) →
    MFields.wk (List.prefix_refl H) fs x = x
  | [], _ => rfl
  | (_, T) :: fs, x => by
    simp only [MFields.wk, MVal.wk_refl T, MFields.wk_refl fs]
    rfl

theorem MObj.elems_wk {H H' : HTy} (e : H <+: H') {R : RefTy} {E : Ty} (a : ArrTy R E)
    (o : MObj H R) : MObj.elems a (MObj.wk e R o) = (MObj.elems a o).map (MVal.wk e E) := by
  cases a <;> simp only [MObj.wk, MObj.elems_dyn, MObj.elems_fixed]

theorem MObj.wk_wk {H H₁ H₂ : HTy} (e₁ : H <+: H₁) (e₂ : H₁ <+: H₂) :
    (R : RefTy) → (o : MObj H R) → MObj.wk e₂ R (MObj.wk e₁ R o) = MObj.wk (e₁.trans e₂) R o
  | .struct s, o => MFields.wk_wk e₁ e₂ (structDef s) o
  | .array E, o => Subtype.ext (by
      show ((o : {l : List (MVal H E) // l.length < 2 ^ 256}).1.map (MVal.wk e₁ E)).map
        (MVal.wk e₂ E) = (o : {l : List (MVal H E) // l.length < 2 ^ 256}).1.map
          (MVal.wk (e₁.trans e₂) E)
      rw [List.map_map]
      exact congrArg (fun f => List.map f _) (funext (MVal.wk_wk e₁ e₂ E)))
  | .fixed E n, o => Subtype.ext (by
      show ((o : {l : List (MVal H E) // l.length = n}).1.map (MVal.wk e₁ E)).map
        (MVal.wk e₂ E) = (o : {l : List (MVal H E) // l.length = n}).1.map
          (MVal.wk (e₁.trans e₂) E)
      rw [List.map_map]
      exact congrArg (fun f => List.map f _) (funext (MVal.wk_wk e₁ e₂ E)))
  | .mapping _ _, o => (o : Empty).elim

theorem MObj.wk_refl {H : HTy} : (R : RefTy) → (o : MObj H R) →
    MObj.wk (List.prefix_refl H) R o = o
  | .struct s, o => MFields.wk_refl (structDef s) o
  | .array E, o => Subtype.ext (by
      show (o : {l : List (MVal H E) // l.length < 2 ^ 256}).1.map (MVal.wk (List.prefix_refl H) E) =
        (o : {l : List (MVal H E) // l.length < 2 ^ 256}).1
      exact (congrArg (fun f => List.map f _) (funext (MVal.wk_refl E))).trans (List.map_id _))
  | .fixed E n, o => Subtype.ext (by
      show (o : {l : List (MVal H E) // l.length = n}).1.map (MVal.wk (List.prefix_refl H) E) =
        (o : {l : List (MVal H E) // l.length = n}).1
      exact (congrArg (fun f => List.map f _) (funext (MVal.wk_refl E))).trans (List.map_id _))
  | .mapping _ _, o => (o : Empty).elim

theorem Objs.get_wk {H H' : HTy} (e : H <+: H') {R : RefTy} : (Rs : List RefTy) →
    (os : Objs H Rs) → (i : Nat) → (h : Rs[i]? = some R) →
    Objs.get Rs (Objs.wk e Rs os) i h = MObj.wk e R (Objs.get Rs os i h)
  | [], _, _, h => absurd h (by simp only [List.getElem?_nil, reduceCtorEq, not_false_eq_true])
  | R' :: _, _, 0, h => by
    obtain rfl : R' = R := Option.some.inj (by simpa only [List.getElem?_cons_zero] using h)
    rfl
  | _ :: Rs, os, i + 1, h => Objs.get_wk e Rs os.2 i _

theorem Objs.get_snoc_lt {H : HTy} {R R₂ : RefTy} (o : MObj H R) : (Rs : List RefTy) →
    (os : Objs H Rs) → (i : Nat) → (h : (Rs ++ [R])[i]? = some R₂) → (h' : Rs[i]? = some R₂) →
    Objs.get (Rs ++ [R]) (Objs.snoc o Rs os) i h = Objs.get Rs os i h'
  | [], _, _, _, h' => absurd h' (by simp only [List.getElem?_nil, reduceCtorEq, not_false_eq_true])
  | R' :: _, _, 0, _, h' => by
    obtain rfl : R' = R₂ := Option.some.inj (by simpa only [List.getElem?_cons_zero] using h')
    rfl
  | _ :: Rs, os, i + 1, _, _ => Objs.get_snoc_lt o Rs os.2 i _ _

theorem Objs.get_snoc_last {H : HTy} {R : RefTy} (o : MObj H R) : (Rs : List RefTy) →
    (os : Objs H Rs) → (h : (Rs ++ [R])[Rs.length]? = some R) →
    Objs.get (Rs ++ [R]) (Objs.snoc o Rs os) Rs.length h = o
  | [], _, _ => rfl
  | _ :: Rs, os, _ => Objs.get_snoc_last o Rs os.2 _

/-- The object allocated is the one given. -/
theorem Heap.get_alloc {H : HTy} {R : RefTy} (hp : Heap H) (o : MObj H R) :
    (hp.alloc o).1.get (hp.alloc o).2 = MObj.wk (List.prefix_append H [R]) R o :=
  Objs.get_snoc_last _ H _ _

/-- `hp'`, over a grown typing, holds every object of `hp`, its references
weakened. -/
def Heap.Keeps {H H' : HTy} (e : H <+: H') (hp : Heap H) (hp' : Heap H') : Prop :=
  ∀ {R : RefTy} (r : HRef H R), hp'.get (r.wk e) = MObj.wk e R (hp.get r)

theorem Heap.Keeps.refl {H : HTy} (hp : Heap H) : Heap.Keeps (List.prefix_refl H) hp hp :=
  fun r => (MObj.wk_refl _ (hp.get r)).symm

theorem Heap.Keeps.trans {H H₁ H₂ : HTy} {e₁ : H <+: H₁} {e₂ : H₁ <+: H₂} {hp : Heap H}
    {hp₁ : Heap H₁} {hp₂ : Heap H₂} (h₁ : Heap.Keeps e₁ hp hp₁) (h₂ : Heap.Keeps e₂ hp₁ hp₂) :
    Heap.Keeps (e₁.trans e₂) hp hp₂ := fun r => by
  show hp₂.get ((r.wk e₁).wk e₂) = _
  rw [h₂, h₁, MObj.wk_wk]

/-- **An allocation keeps every older object.** -/
theorem Heap.keeps_alloc {H : HTy} {R : RefTy} (hp : Heap H) (o : MObj H R) :
    Heap.Keeps (List.prefix_append H [R]) hp (hp.alloc o).1 := fun r => by
  show Objs.get (H ++ [R]) (Objs.snoc _ H (Objs.wk _ H hp)) r.id _ = _
  rw [Objs.get_snoc_lt _ H _ r.id _ r.get?, Objs.get_wk]
  rfl

theorem Grown.keeps_alloc {H : HTy} {R : RefTy} {hp : Heap H} (g : Grown H (MObj · R))
    (hg : Heap.Keeps g.ext hp g.heap) : Heap.Keeps (Grown.alloc g).ext hp (Grown.alloc g).heap :=
  hg.trans (Heap.keeps_alloc g.heap g.val)

mutual
/-- **A copy into memory keeps every older object.** -/
theorem SVal.keeps_copyStToM : {T : Ty} → (v : SVal T) → (h : T.mapFree = true) →
    {H : HTy} → (hp : Heap H) → Heap.Keeps (v.copyStToM hp h).ext hp (v.copyStToM hp h).heap
  | _, .prim _, _, _, hp => by
    rw [SVal.copyStToM_prim]
    exact Heap.Keeps.refl hp
  | _, .struct fs, _, _, hp => by
    rw [SVal.copyStToM_struct]
    exact Grown.keeps_alloc _ (SFields.keeps_copyStToM fs _ hp)
  | _, .array e _ _, _, _, hp => by
    rw [SVal.copyStToM_array]
    exact Grown.keeps_alloc _ (SVec.keeps_copyStToM e _ hp)
  | _, .fixed e, _, _, hp => by
    rw [SVal.copyStToM_fixed]
    exact Grown.keeps_alloc _ (SVec.keeps_copyStToM e _ hp)
  | _, .map _ _, h, _, _ => by simp only [Ty.mapFree, Bool.false_eq_true] at h

theorem SFields.keeps_copyStToM : {fs : List (Name × Ty)} → (x : SFields fs) →
    (h : ∀ fT ∈ fs, fT.2.mapFree = true) → {H : HTy} → (hp : Heap H) →
    Heap.Keeps (x.copyStToM hp h).ext hp (x.copyStToM hp h).heap
  | _, .nil, _, _, hp => by
    rw [SFields.copyStToM_nil]
    exact Heap.Keeps.refl hp
  | _, .cons v rest, _, _, hp => by
    rw [SFields.copyStToM_cons]
    exact Heap.Keeps.trans (SVal.keeps_copyStToM v _ hp) (SFields.keeps_copyStToM rest _ _)

theorem SList.keeps_copyStToM : {E : Ty} → (l : SList E) → (h : E.mapFree = true) →
    {H : HTy} → (hp : Heap H) → Heap.Keeps (l.copyStToM hp h).ext hp (l.copyStToM hp h).heap
  | _, .nil, _, _, hp => by
    rw [SList.copyStToM_nil]
    exact Heap.Keeps.refl hp
  | _, .cons v rest, h, _, hp => by
    rw [SList.copyStToM_cons]
    exact Heap.Keeps.trans (SVal.keeps_copyStToM v h hp) (SList.keeps_copyStToM rest h _)

theorem SVec.keeps_copyStToM : {E : Ty} → {n : Nat} → (l : SVec E n) → (h : E.mapFree = true) →
    {H : HTy} → (hp : Heap H) → Heap.Keeps (l.copyStToM hp h).ext hp (l.copyStToM hp h).heap
  | _, _, .nil, _, _, hp => by
    rw [SVec.copyStToM_nil]
    exact Heap.Keeps.refl hp
  | _, _, .cons v rest, h, _, hp => by
    rw [SVec.copyStToM_cons]
    exact Heap.Keeps.trans (SVal.keeps_copyStToM v h hp) (SVec.keeps_copyStToM rest h _)
end

theorem MFields.get_wk {H H' : HTy} (e : H <+: H') {f : Name} : (fs : List (Name × Ty)) →
    {T : Ty} → (x : MFields H fs) → (h : lookupBy f fs = some T) →
    MFields.get fs (MFields.wk e fs x) h = MVal.wk e T (MFields.get fs x h)
  | [], _, _, h => absurd h (by simp only [lookupBy, reduceCtorEq, not_false_eq_true])
  | (f', T') :: fs, T, x, h => by
    by_cases e' : f = f'
    · have hT := SFields.lookupBy_cons_pos e' h
      subst hT
      simp only [MFields.get, MFields.wk, e', dite_true]
    · simp only [MFields.get, MFields.wk, e', dite_false]
      exact MFields.get_wk e fs x.2 _

theorem Heap.Keeps.field {H H' : HTy} {e : H <+: H'} {hp : Heap H} {hp' : Heap H'}
    (hk : Heap.Keeps e hp hp') {s f : Name} {T : Ty} (r : HRef H (.struct s))
    (h : lookupBy f (structDef s) = some T) : hp'.field (r.wk e) h = MVal.wk e T (hp.field r h) := by
  simp only [Heap.field, hk r]
  exact MFields.get_wk e _ (hp.get r) h

theorem Heap.Keeps.len {H H' : HTy} {e : H <+: H'} {hp : Heap H} {hp' : Heap H'}
    (hk : Heap.Keeps e hp hp') {R : RefTy} {E : Ty} (r : HRef H R) (a : ArrTy R E) :
    hp'.len (r.wk e) a = hp.len r a := by
  simp only [Heap.len, hk r, MObj.elems_wk, List.length_map]

/-- **A grown heap reads an older address as before**, weakened. -/
theorem Heap.Keeps.readAddr {H H' : HTy} {e : H <+: H'} {hp : Heap H} {hp' : Heap H'}
    (hk : Heap.Keeps e hp hp') {T : Ty} (ra : MAddr H T) :
    hp'.readAddr (ra.wk e) = (hp.readAddr ra).map (MVal.wk e T) := by
  cases ra with
  | field r h => simp only [MAddr.wk, Heap.readAddr, hk.field r h, Option.map_some]
  | index r a i =>
    simp only [MAddr.wk, Heap.readAddr, Heap.index, hk r, MObj.elems_wk, List.getElem?_map]

/-- An allocation keeps every object below it: the slot at an address
there reads the same, weakened. -/
theorem Heap.readAddr_allocDefault {H : HTy} (hp : Heap H) (R : RefTy)
    (hR : (Ty.ref R).mapFree = true) {T : Ty} (ra : MAddr H T) :
    (hp.allocDefault R hR).heap.readAddr (ra.wk (hp.allocDefault R hR).ext) =
      (hp.readAddr ra).map (MVal.wk (hp.allocDefault R hR).ext T) :=
  Heap.Keeps.readAddr (SVal.keeps_copyStToM _ hR hp) ra

/-- A copy into memory keeps every object below it. -/
theorem Heap.readAddr_copyStToM {H : HTy} (hp : Heap H) {U : Ty} (v : SVal U)
    (hU : U.mapFree = true) {T : Ty} (ra : MAddr H T) :
    (v.copyStToM hp hU).heap.readAddr (ra.wk (v.copyStToM hp hU).ext) =
      (hp.readAddr ra).map (MVal.wk (v.copyStToM hp hU).ext T) :=
  Heap.Keeps.readAddr (SVal.keeps_copyStToM v hU hp) ra

end Keeps

/-- The address in a grown typing: the same object, where it is below the
smaller one. -/
theorem MAddrT.resolve_wk {H H' : HTy} (e : H <+: H') {T : Ty} (a : MAddrT T)
    (hid : a.id < H.length) : a.resolve H' = (a.resolve H).map (MAddr.wk e) := by
  obtain ⟨t, rfl⟩ := e
  have hg : ∀ (R : RefTy) (id : Nat), id < H.length →
      HRef.ofId? (H ++ t) R id = (HRef.ofId? H R id).map (HRef.wk ⟨t, rfl⟩) := by
    intro R id hl
    simp only [HRef.ofId?, List.getElem?_append_left hl]
    split <;> rfl
  cases a with
  | field id h =>
    simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM, hg _ id hid, Option.map_map]
    rfl
  | index id a i =>
    simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM, hg _ id hid, Option.map_map]
    rfl

theorem HRef.ofId?_self {H : HTy} {R : RefTy} (r : HRef H R) : HRef.ofId? H R r.id = some r := by
  simp only [HRef.ofId?, r.get?, dite_true]


/-! ## Memory, read by identity

A memory read returns a value over the heap typing it reads in, so two
reads over two typings are not of one type; read as a word or an identity
(`Grown.readId`, `MvT`), they are, and a write is named with what it leaves
there. -/

/-- A slot value as a word or an identity (`MvT`), whatever the heap
typing. -/
def MVal.toMvT (H : HTy) : (T : Ty) → MVal H T → MvT T
  | .prim _, v => v
  | .ref _, r => (r : HRef H _).id

/-- `read(m, a)` as a word or an identity. -/
def Grown.readId {H : HTy} {T : Ty} (m : Grown H (fun _ => Unit)) (a : MAddrT T) :
    Option (MvT T) :=
  (m.readT a).map (MVal.toMvT m.H' T)

/-- A dynamic array's length by identity, independent of the heap typing in
the result, as the memory `size` read of `memoryLengthRead`. -/
def Grown.lenId {H : HTy} (m : Grown H (fun _ => Unit)) (E : Ty) (id : Nat) :
    Option PrimTy.uint.Denote :=
  (HRef.ofId? m.H' (.array E) id).bind fun r => some (m.heap.lenU r)

theorem Grown.lenId_ref {H : HTy} (m : Grown H (fun _ => Unit)) {E : Ty}
    (r : HRef m.H' (.array E)) : m.lenId E r.id = some (m.heap.lenU r) := by
  simp only [Grown.lenId, HRef.ofId?_self, Option.bind_some]

/-- Two memory addresses that never meet: two objects, two members of one
object, or two elements of one array; or a member and an element. -/
def MAddrT.Apart {T U : Ty} : MAddrT T → MAddrT U → Prop
  | @MAddrT.field _ f _ id _, @MAddrT.field _ g _ id' _ => ¬ id = id' ∨ ¬ f = g
  | .field .., .index .. => True
  | .index .., .field .. => True
  | .index id _ i, .index id' _ j => ¬ id = id' ∨ ¬ i = j

/-- The object of an address. -/
def MAddr.id {H : HTy} {T : Ty} : MAddr H T → Nat
  | .field r _ => r.id
  | .index r _ _ => r.id

theorem HRef.id_of_ofId? {H : HTy} {R : RefTy} {id : Nat} {r : HRef H R}
    (h : HRef.ofId? H R id = some r) : r.id = id := by
  unfold HRef.ofId? at h
  split at h
  · cases h; rfl
  · cases h

theorem MVal.toMvT_toMVal {H : HTy} : {T : Ty} → {v : MvT T} → {w : MVal H T} →
    MvT.toMVal H T v = some w → MVal.toMvT H T w = v
  | .prim _, _, _, h => by cases h; rfl
  | .ref _, _, _, h => HRef.id_of_ofId? h

/-- **A write leaves an address on another object**, or apart on its own. -/
theorem Heap.readAddr_writeAddr_frame {H : HTy} {T U : Ty} {hp hp' : Heap H} {ad : MAddr H T}
    {bd : MAddr H U} {v : MVal H T} (h : hp.writeAddr ad v = some hp')
    (hab : ¬ ad.id = bd.id ∨ ad.Apart bd) : hp'.readAddr bd = hp.readAddr bd := by
  rcases hab with hne | hab
  · cases ad with
    | field r hf =>
      simp only [Heap.writeAddr, Option.some.injEq] at h
      subst h
      cases bd with
      | field r' hg =>
        simp only [Heap.readAddr, Heap.field, Heap.setField, Heap.get_set_ne _ r r' hne]
      | index r' a j =>
        simp only [Heap.readAddr, Heap.index, Heap.setField, Heap.get_set_ne _ r r' hne]
    | index r a i =>
      simp only [Heap.writeAddr, Heap.setIndex] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        cases bd with
        | field r' hg => simp only [Heap.readAddr, Heap.field, Heap.get_set_ne _ r r' hne]
        | index r' a' j => simp only [Heap.readAddr, Heap.index, Heap.get_set_ne _ r r' hne]
      · simp only [reduceCtorEq] at h
  · exact Heap.readAddr_writeAddr_apart h hab

theorem MAddrT.apart_resolve {H : HTy} {T U : Ty} {a : MAddrT T} {b : MAddrT U}
    {ad : MAddr H T} {bd : MAddr H U} (hab : a.Apart b) (ha : a.resolve H = some ad)
    (hb : b.resolve H = some bd) : ¬ ad.id = bd.id ∨ ad.Apart bd := by
  cases a with
  | field id h =>
    cases b with
    | field id' h' =>
      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 ha
      obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 hb
      simp only [MAddr.id, HRef.id_of_ofId? hr, HRef.id_of_ofId? hr']
      rcases hab with hne | hne
      · exact .inl hne
      · by_cases e : id = id'
        · exact .inr hne
        · exact .inl e
    | index id' a' j =>
      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 ha
      obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 hb
      exact .inr trivial
  | index id a i =>
    cases b with
    | field id' h' =>
      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 ha
      obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 hb
      exact .inr trivial
    | index id' a' j =>
      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 ha
      obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 hb
      simp only [MAddr.id, HRef.id_of_ofId? hr, HRef.id_of_ofId? hr']
      rcases hab with hne | hne
      · exact .inl hne
      · exact .inr fun _ => hne

/-- What a write to memory leaves: the word or identity written at its
address, and every address apart from it as it was. -/
theorem Grown.writeT_facts {H : HTy} {T : Ty} {m m' : Grown H (fun _ => Unit)} {a : MAddrT T}
    {v : MvT T} (h : m.writeT a v = some m') :
    m'.readId a = some v ∧ ∀ {U : Ty} (b : MAddrT U), a.Apart b → m'.readId b = m.readId b := by
  unfold Grown.writeT at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨ad, had, w, hw, hp, hhp, rfl⟩ := h
  refine ⟨?_, fun b hab => ?_⟩
  · show ((a.resolve m.H').bind hp.readAddr).map _ = _
    rw [had, Option.bind_some, Heap.readAddr_writeAddr_same hhp, Option.map_some,
      MVal.toMvT_toMVal hw]
  · show ((b.resolve m.H').bind hp.readAddr).map _ = ((b.resolve m.H').bind m.heap.readAddr).map _
    cases hb : b.resolve m.H' with
    | none => rfl
    | some bd =>
      simp only [Option.bind_some]
      rw [Heap.readAddr_writeAddr_frame hhp (MAddrT.apart_resolve hab had hb)]


/-! ## A copy into memory, at a member -/

/-- The fresh object of an allocation is the one given, weakened. -/
theorem Grown.alloc_get {H : HTy} {R : RefTy} (g : Grown H (MObj · R)) :
    (Grown.alloc g).heap.get (Grown.alloc g).val = MObj.wk (List.prefix_append g.H' [R]) R g.val :=
  Heap.get_alloc g.heap g.val

/-- A member of a fresh struct: the member given, weakened. -/
theorem Grown.alloc_field {H : HTy} {s f : Name} {T : Ty} (g : Grown H (MObj · (.struct s)))
    (hf : lookupBy f (structDef s) = some T) :
    (Grown.alloc g).heap.field (Grown.alloc g).val hf =
      MVal.wk (List.prefix_append g.H' [.struct s]) T (MFields.get (structDef s) g.val hf) := by
  show MFields.get _ ((Grown.alloc g).heap.get (Grown.alloc g).val) hf = _
  rw [Grown.alloc_get]
  exact MFields.get_wk _ _ g.val hf

/-- The members a struct copy into memory holds: a word member is the
storage member's word. -/
theorem SFields.copyStToM_get_prim {H : HTy} (hp : Heap H) {f : Name} {p : PrimTy} :
    {fs : List (Name × Ty)} → (x : SFields fs) → (h : ∀ fT ∈ fs, fT.2.mapFree = true) →
    (hf : lookupBy f fs = some (.prim p)) →
    (MFields.get fs (x.copyStToM hp h).val hf : p.Denote) = ((x.get hf).view : p.Denote)
  | [], .nil, _, hf => absurd hf (by simp only [lookupBy, reduceCtorEq, not_false_eq_true])
  | (f', T') :: fs, .cons v rest, h, hf => by
    rw [SFields.copyStToM_cons, SFields.get_cons]
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e hf
      subst hT
      cases v with
      | prim x =>
        simp only [MFields.get, e, dite_true]
        rw [SVal.copyStToM_prim]
        rfl
    · simp only [MFields.get, e, dite_false]
      exact SFields.copyStToM_get_prim _ rest _ _

/-- **A member of a storage struct copied into memory** reads what the
struct held there. -/
theorem SVal.copyStToM_field {H : HTy} (hp : Heap H) {s f : Name} {p : PrimTy}
    (sv : SVal (.ref (.struct s))) (hT : (Ty.ref (.struct s)).mapFree = true)
    (hf : lookupBy f (structDef s) = some (.prim p)) :
    (sv.copyStToM hp hT).heap.field (sv.copyStToM hp hT).val hf =
      (((SVal.view sv : SFields _).get hf).view : p.Denote) := by
  cases sv with
  | struct fs =>
    rw [SVal.copyStToM_struct, Grown.alloc_field, SVal.view_struct]
    exact SFields.copyStToM_get_prim hp fs _ hf


/-! ## Allocations: older objects -/

/-- A read of an address the grown heap `μ₀.then g` resolves as `μ₀` does:
the old object, read there, weakened. -/
theorem Grown.read_then_old {H : HTy} (μ₀ : Grown H (fun _ => Unit)) {α : HTy → Type}
    (g : Grown μ₀.H' α) (hg : Heap.Keeps g.ext μ₀.heap g.heap)
    {T : Ty} (bd : MAddrT T) (hid : bd.id < μ₀.H'.length) :
    ((bd.resolve (μ₀.then g).H').bind fun rb => (μ₀.then g).heap.readAddr rb) =
      ((bd.resolve μ₀.H').bind fun rb => μ₀.heap.readAddr rb).map (MVal.wk g.ext T) := by
  show ((bd.resolve g.H').bind fun rb => g.heap.readAddr rb) = _
  rw [MAddrT.resolve_wk g.ext bd hid]
  cases bd.resolve μ₀.H' with
  | none => rfl
  | some rb =>
    simp only [Option.map_some, Option.bind_some]
    exact hg.readAddr rb

/-- A word read in a grown heap is the word. -/
theorem MVal.map_wk_prim {H H' : HTy} (e : H <+: H') {p : PrimTy} (x : Option (MVal H (.prim p))) :
    (x.map (MVal.wk e (.prim p)) : Option p.Denote) = (x : Option p.Denote) := by
  cases x <;> rfl

/-- An identity read in a grown heap is the identity. -/
theorem MVal.bind_id_map_wk {H H' : HTy} (e : H <+: H') {R : RefTy} (x : Option (MVal H (.ref R))) :
    (x.map (MVal.wk e (.ref R))).bind (fun r => some (r : HRef H' R).id) =
      x.bind (fun r => some (r : HRef H R).id) := by
  cases x <;> rfl

theorem MVal.toMvT_comp_wk {H H' : HTy} (e : H <+: H') (T : Ty) :
    MVal.toMvT H' T ∘ MVal.wk e T = MVal.toMvT H T := by
  cases T <;> rfl

/-- Below a growth that keeps the older objects, an address whose object is
older reads what it read, as a word or an identity. -/
theorem Grown.readId_then_old {H : HTy} (μ₀ : Grown H (fun _ => Unit)) {α : HTy → Type}
    (g : Grown μ₀.H' α) (hg : Heap.Keeps g.ext μ₀.heap g.heap)
    {T : Ty} (bd : MAddrT T) (hid : bd.id < μ₀.H'.length) :
    (μ₀.then g).readId bd = μ₀.readId bd := by
  show (((bd.resolve (μ₀.then g).H').bind fun rb => (μ₀.then g).heap.readAddr rb)).map
      (MVal.toMvT (μ₀.then g).H' T) =
    ((bd.resolve μ₀.H').bind fun rb => μ₀.heap.readAddr rb).map (MVal.toMvT μ₀.H' T)
  rw [Grown.read_then_old μ₀ g hg bd hid, Option.map_map]
  exact congrArg (fun f => Option.map f _) (MVal.toMvT_comp_wk g.ext T)


/-! ## Lengths: what a read of an element needs -/

section Len

/-- An element reads exactly below the array's length. -/
theorem Heap.readAddr_index_isSome {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H) (r : HRef H R)
    (a : ArrTy R E) (i : PrimTy.uint.Denote) :
    (hp.readAddr (.index r a i)).isSome = decide (i.1.toNat < hp.len r a) := by
  simp only [Heap.readAddr, Heap.index, Heap.len]
  by_cases hl : i.1.toNat < (MObj.elems a (hp.get r)).length
  · simp only [hl, getElem?_pos, Option.isSome_some, decide_true]
  · simp only [hl, not_false_eq_true, getElem?_neg, Option.isSome_none, decide_false]

/-- A slot writes exactly where it reads. -/
theorem Heap.writeAddr_isSome {H : HTy} {T : Ty} (hp : Heap H) (ad : MAddr H T) (v : MVal H T) :
    (hp.writeAddr ad v).isSome = (hp.readAddr ad).isSome := by
  cases ad with
  | field r h => rfl
  | index r a i =>
    rw [Heap.readAddr_index_isSome]
    simp only [Heap.writeAddr, Heap.setIndex, Heap.len]
    split
    · simp_all only [Option.isSome_some, and_self, decide_true]
    · simp_all only [Option.isSome_none, decide_false]

/-- **A write keeps every length**: a member is no array, and an element
written keeps its array's length. -/
theorem Heap.len_writeAddr {H : HTy} {T : Ty} {hp hp' : Heap H} {ad : MAddr H T} {v : MVal H T}
    (h : hp.writeAddr ad v = some hp') {R : RefTy} {E : Ty} (r : HRef H R) (a : ArrTy R E) :
    hp'.len r a = hp.len r a := by
  cases ad with
  | field r' hf =>
    simp only [Heap.writeAddr, Option.some.injEq] at h
    subst h
    unfold Heap.len Heap.setField
    by_cases e : r'.id = r.id
    · obtain ⟨hR, -⟩ := HRef.heq_of_id r' r e
      exact absurd hR.symm (a.ne_struct _)
    · rw [Heap.get_set_ne _ _ _ e]
  | index r' a' i =>
    simp only [Heap.writeAddr, Heap.setIndex] at h
    split at h
    · cases h
      unfold Heap.len
      by_cases e : r'.id = r.id
      · obtain ⟨rfl, hr⟩ := HRef.heq_of_id r' r e
        cases hr
        cases a <;> cases a' <;>
          simp only [Heap.get_set_same, MObj.elems_setElem, List.length_set]
      · rw [Heap.get_set_ne _ _ _ e]
    · cases h

theorem MObj.elems_wk_length {H H' : HTy} (e : H <+: H') {R : RefTy} {E : Ty} (a : ArrTy R E)
    (o : MObj H R) : (MObj.elems a (MObj.wk e R o)).length = (MObj.elems a o).length := by
  cases a <;> simp only [MObj.wk, MObj.elems_dyn, MObj.elems_fixed, List.length_map]

/-- **A fresh array's length** is the length of the elements it was given. -/
theorem Grown.alloc_len {H : HTy} {R : RefTy} {E : Ty} (g : Grown H (MObj · R)) (a : ArrTy R E) :
    (Grown.alloc g).heap.len (Grown.alloc g).val a = (MObj.elems a g.val).length := by
  show (MObj.elems a ((g.heap.alloc g.val).1.get (g.heap.alloc g.val).2)).length = _
  rw [Heap.get_alloc, MObj.elems_wk_length]

/-- A fresh array's length as a `uint`, of the length it was given. -/
theorem lenU_eq {n : Nat} (h : n < 2 ^ 256) (x : PrimTy.uint.Denote) (e : (n : Int) = x.1) :
    Solidity.lenU n h = x := Subtype.ext e

theorem HRef.ofId?_wk {H H' : HTy} (e : H <+: H') (R : RefTy) {id : Nat} (hid : id < H.length) :
    HRef.ofId? H' R id = (HRef.ofId? H R id).map (HRef.wk e) := by
  obtain ⟨t, rfl⟩ := e
  simp only [HRef.ofId?, List.getElem?_append_left hid]
  split <;> rfl

theorem Heap.lenU_eq {H H' : HTy} {E : Ty} {hp : Heap H} {hp' : Heap H'} {r : HRef H (.array E)}
    {r' : HRef H' (.array E)} (h : hp.len r .dyn = hp'.len r' .dyn) : hp.lenU r = hp'.lenU r' :=
  Subtype.ext (congrArg Nat.cast h)

/-- **A grown heap keeps every older array's length**, where it keeps the
older objects. -/
theorem Grown.lenU_then_old {H : HTy} (μ₀ : Grown H (fun _ => Unit)) {α : HTy → Type}
    (g : Grown μ₀.H' α) (hg : Heap.Keeps g.ext μ₀.heap g.heap)
    {E : Ty} (id : Nat) (hid : id < μ₀.H'.length) :
    (HRef.ofId? (μ₀.then g).H' (.array E) id).map (fun r => (μ₀.then g).heap.lenU r) =
      (HRef.ofId? μ₀.H' (.array E) id).map (fun r => μ₀.heap.lenU r) := by
  show (HRef.ofId? g.H' (.array E) id).map (fun r => g.heap.lenU r) = _
  rw [HRef.ofId?_wk g.ext _ hid]
  cases HRef.ofId? μ₀.H' (.array E) id with
  | none => rfl
  | some r =>
    simp only [Option.map_some, Option.some.injEq]
    exact Heap.lenU_eq (hg.len r .dyn)

theorem Grown.lenU_addM_old {H : HTy} (μ₀ : Grown H (fun _ => Unit)) (R : RefTy)
    (hR : (Ty.ref R).mapFree = true) {E : Ty} (id : Nat) (hid : id < μ₀.H'.length) :
    (HRef.ofId? (μ₀.then (μ₀.heap.allocDefault R hR)).H' (.array E) id).map
        (fun r => (μ₀.then (μ₀.heap.allocDefault R hR)).heap.lenU r) =
      (HRef.ofId? μ₀.H' (.array E) id).map (fun r => μ₀.heap.lenU r) :=
  Grown.lenU_then_old μ₀ _ (SVal.keeps_copyStToM _ hR μ₀.heap) id hid

theorem Grown.lenU_copySt_old {H : HTy} (μ₀ : Grown H (fun _ => Unit)) {U : Ty} (v : SVal U)
    (hU : U.mapFree = true) {E : Ty} (id : Nat) (hid : id < μ₀.H'.length) :
    (HRef.ofId? (μ₀.then (v.copyStToM μ₀.heap hU)).H' (.array E) id).map
        (fun r => (μ₀.then (v.copyStToM μ₀.heap hU)).heap.lenU r) =
      (HRef.ofId? μ₀.H' (.array E) id).map (fun r => μ₀.heap.lenU r) :=
  Grown.lenU_then_old μ₀ _ (SVal.keeps_copyStToM v hU μ₀.heap) id hid

/-- **A fresh dynamic array is empty.** -/
theorem Heap.allocDefault_array_len {H : HTy} (hp : Heap H) (E : Ty)
    (hR : (Ty.ref (.array E)).mapFree = true) :
    (hp.allocDefault (.array E) hR).heap.len (hp.allocDefault (.array E) hR).val .dyn = 0 := by
  unfold Heap.allocDefault
  show (fun x : Grown H (MVal · (.ref (.array E))) => x.heap.len x.val .dyn)
    ((SVal.array .nil .nil SVal.zero_lt_bound : SVal (.ref (.array E))).copyStToM hp hR) = 0
  rw [SVal.copyStToM_array]
  exact (Grown.alloc_len _ .dyn).trans (by rw [MObj.elems_dyn]; exact (SVec.copyStToM hp .nil _).val.2)

/-- **A fresh array of `n` elements** (`new T[](n)`) has length `n`. -/
theorem newArrT_copy_len {H : HTy} (hp : Heap H) (E : Ty) (n : PrimTy.uint.Denote)
    (h : (RefTy.array E).newArrOk = true) (hU : (Ty.ref (.array E)).mapFree = true) :
    ((newArrT (.array E) n h).copyStToM hp hU).heap.len ((newArrT (.array E) n h).copyStToM hp hU).val
      .dyn = n.1.toNat := by
  show (fun x : Grown H (MVal · (.ref (.array E))) => x.heap.len x.val .dyn)
    ((SVal.array (SVec.ofList (List.replicate n.1.toNat (SVal.dflt E))) .nil (newArr_lt n _) :
      SVal (.ref (.array E))).copyStToM hp hU) = _
  rw [SVal.copyStToM_array]
  refine (Grown.alloc_len _ .dyn).trans ?_
  rw [MObj.elems_dyn]
  exact (SVec.copyStToM hp _ _).val.2.trans (List.length_replicate ..)

/-- A fresh array's element is a default in range and absent past its end.
This is the typed observation behind allocation's initialized memory reads. -/
theorem newArrT_find_at {E V : Ty} (n k : PrimTy.uint.Denote)
    (h : (RefTy.array E).newArrOk = true) (p : Path E V) :
    (newArrT (.array E) n h).findM (.at k p) =
      if k.1.toNat < n.1.toNat then (SVal.dflt E).findM p else none := by
  simp only [newArrT, SVal.findM_at', SVec.toList_ofList, SList.toList_nil,
    List.append_nil, List.getElem?_replicate]
  split <;> rfl

/-- Copying primitive defaults allocates no child objects. -/
theorem SVec.copyStToM_prim_defaults {H : HTy} (hp : Heap H) (P : PrimTy) (n : Nat) :
    (SVec.ofList (List.replicate n (SVal.prim (PrimTy.dflt P)))).copyStToM hp rfl =
      (⟨List.prefix_refl H, hp, ⟨List.replicate n (PrimTy.dflt P), by
        simp only [List.length_replicate]⟩⟩ :
        Grown H (fun H' => {l : List (MVal H' (.prim P)) //
          l.length = (List.replicate n (SVal.prim (PrimTy.dflt P))).length})) := by
  induction n with
  | zero => simp only [List.replicate_zero, SVec.ofList, SVec.copyStToM_nil]
  | succ n ih =>
    let step : Grown H (fun H' => {l : List (MVal H' (.prim P)) //
        l.length = (List.replicate n (SVal.prim (PrimTy.dflt P))).length}) →
        Grown H (fun H' => {l : List (MVal H' (.prim P)) //
          l.length = (List.replicate (n + 1) (SVal.prim (PrimTy.dflt P))).length}) :=
      fun g => ⟨g.ext, g.heap, ⟨PrimTy.dflt P :: g.val.1, by
        simpa only [List.length_cons, List.length_replicate] using congrArg Nat.succ g.val.2⟩⟩
    simpa only [step, List.replicate_succ, SVec.ofList, SVec.copyStToM_cons,
      SVal.copyStToM_prim, MVal.wk] using congrArg step ih

/-- `initElement` for a primitive element of a freshly allocated array;
an out-of-range address remains absent in the typed heap. -/
theorem newArrT_copy_prim_index {H : HTy} (hp : Heap H) (P : PrimTy)
    (n i : PrimTy.uint.Denote) (h : (RefTy.array (.prim P)).newArrOk = true) :
    let g := (newArrT (.array (.prim P)) n h).copyStToM hp rfl
    g.heap.readAddr (.index g.val .dyn i) =
      if i.1.toNat < n.1.toNat then some (PrimTy.dflt P) else none := by
  simp only [newArrT, SVal.dflt_prim, SVal.copyStToM_array,
    Heap.readAddr, Heap.index, Grown.alloc_get, MObj.elems_wk, MObj.elems_dyn]
  have hwk : ∀ {A B : HTy} (e : A <+: B),
      MVal.wk e (.prim P) = (id : P.Denote → P.Denote) := by
    intro A B e
    rfl
  simp only [hwk, List.map_id]
  change ((SVec.ofList (List.replicate n.1.toNat (SVal.prim (PrimTy.dflt P)))).copyStToM hp
    rfl).val.1[i.1.toNat]? = _
  rw [SVec.copyStToM_prim_defaults]
  exact List.getElem?_replicate

/-- **A write keeps every length**, on the grown heap. -/
theorem Grown.writeT_lenU {H : HTy} {T : Ty} {m m' : Grown H (fun _ => Unit)} {a : MAddrT T}
    {v : MvT T} (h : m.writeT a v = some m') {E : Ty} (id : Nat) :
    (HRef.ofId? m'.H' (.array E) id).map (fun r => m'.heap.lenU r) =
      (HRef.ofId? m.H' (.array E) id).map (fun r => m.heap.lenU r) := by
  unfold Grown.writeT at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨ad, -, w, -, hp, hhp, rfl⟩ := h
  show (HRef.ofId? m.H' (.array E) id).map (fun r => hp.lenU r) = _
  cases HRef.ofId? m.H' (.array E) id with
  | none => rfl
  | some r => exact congrArg some (Heap.lenU_eq (Heap.len_writeAddr hhp r .dyn))

/-- **An allocation's identity is new** (Lean only, the freshness behind
solkey's `newFromAdd`): past every identity of the heap it grows. -/
theorem Grown.alloc_id_ge {H : HTy} {R : RefTy} (g : Grown H (MObj · R)) :
    H.length ≤ ((Grown.alloc g).val : HRef _ R).id :=
  g.ext.length_le

/-- A copy into memory of a reference is a fresh object: its identity is
past the heap's. -/
theorem SVal.copyStToM_id_ge {H : HTy} (hp : Heap H) {R : RefTy} (v : SVal (.ref R))
    (h : (Ty.ref R).mapFree = true) :
    H.length ≤ ((v.copyStToM hp h).val : HRef _ R).id := by
  cases v with
  | struct fs => rw [SVal.copyStToM_struct]; exact Grown.alloc_id_ge _
  | array e sh hn =>
    rw [SVal.copyStToM_array]; exact Grown.alloc_id_ge _
  | fixed e =>
    rw [SVal.copyStToM_fixed]; exact Grown.alloc_id_ge _
  | map m d => exact absurd h (by simp only [Ty.mapFree, Bool.false_eq_true, not_false_eq_true])

end Len

/-! ## A fresh default object

`addM(m, R)` copies the default of `R` into memory (`Heap.allocDefault`):
the fresh object, and every object it reaches by its members and its
fixed arrays' elements, holds its type's default (`Heap.Dflt`).  A read
below the fresh root at a path its type declares is therefore a default
(`readOnAddM`, `initMember`, `initSize`). -/

section Dflt

/-- The slot `v` holds what a default copied into memory holds: a word its
type's default; a struct each member's; a dynamic array no element; a fixed
array each element's. -/
inductive Heap.Dflt {H : HTy} (hp : Heap H) : (T : Ty) → MVal H T → Prop
  | prim {p : PrimTy} : Heap.Dflt hp (.prim p) (PrimTy.dflt p : MVal H (.prim p))
  | struct {s : Name} (r : HRef H (.struct s))
      (h : ∀ {f : Name} {T : Ty} (hf : lookupBy f (structDef s) = some T),
        Heap.Dflt hp T (hp.field r hf)) :
      Heap.Dflt hp (.ref (.struct s)) r
  | array {E : Ty} (r : HRef H (.array E)) (h : hp.len r .dyn = 0) : Heap.Dflt hp (.ref (.array E)) r
  | fixed {E : Ty} {n : Nat} (r : HRef H (.fixed E n))
      (h : ∀ v ∈ MObj.elems .fixed (hp.get r), Heap.Dflt hp E v) :
      Heap.Dflt hp (.ref (.fixed E n)) r

/-- A default stays one in a heap that keeps its objects. -/
theorem Heap.Dflt.wk {H H' : HTy} {e : H <+: H'} {hp : Heap H} {hp' : Heap H'}
    (hk : Heap.Keeps e hp hp') {T : Ty} {v : MVal H T} (hd : hp.Dflt T v) :
    hp'.Dflt T (MVal.wk e T v) := by
  induction hd with
  | prim => exact .prim
  | struct r _ ih => exact .struct (r.wk e) fun hf => by rw [hk.field r hf]; exact ih hf
  | array r h => exact .array (r.wk e) (by rw [hk.len]; exact h)
  | fixed r _ ih =>
    refine .fixed (r.wk e) fun v hv => ?_
    rw [hk r, MObj.elems_wk] at hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
    exact ih w hw

/-- Every member at its default. -/
def MFields.AllDflt {H : HTy} (hp : Heap H) : (fs : List (Name × Ty)) → MFields H fs → Prop
  | [], _ => True
  | (_, T) :: fs, x => hp.Dflt T x.1 ∧ MFields.AllDflt hp fs x.2

theorem MFields.AllDflt.get {H : HTy} {hp : Heap H} {f : Name} : (fs : List (Name × Ty)) →
    {x : MFields H fs} → MFields.AllDflt hp fs x → {T : Ty} → (hf : lookupBy f fs = some T) →
    hp.Dflt T (MFields.get fs x hf)
  | [], _, _, _, hf => absurd hf (by simp only [lookupBy, reduceCtorEq, not_false_eq_true])
  | (f', T') :: fs, x, hx, T, hf => by
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e hf
      subst hT
      simp only [MFields.get, e, dite_true]
      exact hx.1
    · simp only [MFields.get, e, dite_false]
      exact MFields.AllDflt.get fs hx.2 _

/-- A fresh struct whose members are defaults is one. -/
theorem Grown.dflt_alloc_struct {H : HTy} {s : Name} (g : Grown H (MObj · (.struct s)))
    (hg : MFields.AllDflt g.heap (structDef s) g.val) :
    (Grown.alloc g).heap.Dflt (.ref (.struct s)) (Grown.alloc g).val :=
  .struct _ fun hf => by
    rw [Grown.alloc_field]
    exact (MFields.AllDflt.get _ hg hf).wk (Heap.keeps_alloc g.heap g.val)

/-- A fresh fixed array whose elements are defaults is one. -/
theorem Grown.dflt_alloc_fixed {H : HTy} {E : Ty} {n : Nat} (g : Grown H (MObj · (.fixed E n)))
    (hg : ∀ w ∈ (g.val : {l : List (MVal g.H' E) // l.length = n}).1, g.heap.Dflt E w) :
    (Grown.alloc g).heap.Dflt (.ref (.fixed E n)) (Grown.alloc g).val :=
  .fixed _ fun v hv => by
    rw [Grown.alloc_get, MObj.elems_wk, MObj.elems_fixed] at hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
    exact (hg w hw).wk (Heap.keeps_alloc g.heap g.val)

/-- The members of a default struct, copied into memory, are defaults. -/
theorem MFields.allDflt_copy_dfltBelow (k : Nat) {ih : (T : Ty) → tyRank T < k → SVal T}
    (hih : ∀ (T : Ty) (hT : tyRank T < k) (hm : T.mapFree = true) {H : HTy} (hp : Heap H),
      ((ih T hT).copyStToM hp hm).heap.Dflt T ((ih T hT).copyStToM hp hm).val) :
    (fs : List (Name × Ty)) → (hk : fieldsRank fs < k) → (hm : ∀ fT ∈ fs, fT.2.mapFree = true) →
    {H : HTy} → (hp : Heap H) →
    MFields.AllDflt ((SFields.dfltBelow k ih fs hk).copyStToM hp hm).heap fs
      ((SFields.dfltBelow k ih fs hk).copyStToM hp hm).val
  | [], _, _, _, hp => by
    rw [SFields.dfltBelow, SFields.copyStToM_nil]
    trivial
  | (_, T) :: fs, _, _, _, hp => by
    rw [SFields.dfltBelow, SFields.copyStToM_cons]
    exact ⟨(hih T _ _ hp).wk (SFields.keeps_copyStToM _ _ _),
      MFields.allDflt_copy_dfltBelow k hih fs _ _ _⟩

/-- The elements of `n` copies of a default, copied into memory, are
defaults. -/
theorem SVec.allDflt_copy_replicate {E : Ty} (v : SVal E)
    (hv : ∀ (hm : E.mapFree = true) {H : HTy} (hp : Heap H),
      (v.copyStToM hp hm).heap.Dflt E (v.copyStToM hp hm).val) :
    (n : Nat) → (hm : E.mapFree = true) → {H : HTy} → (hp : Heap H) →
    ∀ w ∈ ((SVec.replicate v n).copyStToM hp hm).val.1,
      ((SVec.replicate v n).copyStToM hp hm).heap.Dflt E w
  | 0, hm, _, hp => by
    rw [SVec.replicate, SVec.copyStToM_nil]
    intro w hw
    cases hw
  | n + 1, hm, _, hp => by
    rw [SVec.replicate, SVec.copyStToM_cons]
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact (hv hm hp).wk (SVec.keeps_copyStToM _ _ _)
    · exact SVec.allDflt_copy_replicate v hv n hm _ w hw

/-- **A default copied into memory is a default**, at every rank. -/
theorem Heap.dflt_copy_dfltBelow : (k : Nat) → (T : Ty) → (h : tyRank T < k) →
    (hm : T.mapFree = true) → {H : HTy} → (hp : Heap H) →
    ((SVal.dfltBelow k T h).copyStToM hp hm).heap.Dflt T ((SVal.dfltBelow k T h).copyStToM hp hm).val
  | 0, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | k + 1, .prim p, _, hm, _, hp => by
    show Heap.Dflt (SVal.copyStToM hp (.prim (PrimTy.dflt p)) hm).heap _
      (SVal.copyStToM hp (.prim (PrimTy.dflt p)) hm).val
    rw [SVal.copyStToM_prim]
    exact .prim
  | k + 1, .ref (.struct s), h, hm, _, hp => by
    have hc := Grown.dflt_alloc_struct _ (MFields.allDflt_copy_dfltBelow k
      (fun T hT hmT _ hp' => Heap.dflt_copy_dfltBelow k T hT hmT hp') (structDef s)
      (Nat.lt_of_lt_of_le (Semantics.structDef_rank_lt s) (Nat.le_of_lt_succ h))
      (mapFree_structDef s (by simpa only [Ty.mapFree, decide_eq_true_eq] using hm)) hp)
    rw [← SVal.copyStToM_struct hp _ hm] at hc
    exact hc
  | k + 1, .ref (.array E), _, hm, _, hp => .array _ (Heap.allocDefault_array_len hp E hm)
  | k + 1, .ref (.fixed E n), h, hm, _, hp => by
    have hE : tyRank E < k + 1 := Nat.lt_of_succ_lt (by simpa only [tyRank] using h)
    have hc := Grown.dflt_alloc_fixed _ (SVec.allDflt_copy_replicate (SVal.dfltBelow (k + 1) E hE)
      (fun hmE _ hp' => Heap.dflt_copy_dfltBelow (k + 1) E hE hmE hp') n
      (by simpa only [Ty.mapFree] using hm) hp)
    rw [← SVal.copyStToM_fixed hp _ hm] at hc
    exact hc
  | k + 1, .ref (.mapping _ _), _, hm, _, _ => by
    simp only [Ty.mapFree, Bool.false_eq_true] at hm
termination_by k T => (k, sizeOf T)

/-- **The fresh object of `addM(m, R)` is a default.** -/
theorem Heap.dflt_allocDefault {H : HTy} (hp : Heap H) (R : RefTy)
    (hR : (Ty.ref R).mapFree = true) :
    (hp.allocDefault R hR).heap.Dflt (.ref R) (hp.allocDefault R hR).val :=
  Heap.dflt_copy_dfltBelow _ _ _ hR hp

/-- A word that is a default is the type's default. -/
theorem Heap.Dflt.prim_eq {H : HTy} {hp : Heap H} {p : PrimTy} {v : MVal H (.prim p)}
    (h : hp.Dflt (.prim p) v) : (v : p.Denote) = PrimTy.dflt p := by
  cases h
  rfl

end Dflt


/-! ## Copies into storage: what a copy reads (`copyMem`) -/

section CopyMem

theorem SVec.toList_ofLen {α : Type} {E : Ty} (f : α → SVal E) : (n : Nat) → (l : List α) →
    (h : l.length = n) → (SVec.ofLen f n l h).toList = l.map f
  | 0, [], _ => by simp only [SVec.ofLen, SVec.toList_nil, List.map_nil]
  | n + 1, x :: xs, h => by
    simp only [SVec.ofLen, SVec.toList_cons, List.map_cons, SVec.toList_ofLen f n xs]
  | 0, _ :: _, h => by simp only [List.length_cons, Nat.add_one_ne_zero] at h
  | _ + 1, [], h => by simp only [List.length_nil, Nat.zero_ne_add_one] at h

theorem MFields.copyBelow_congr {H : HTy} {k k' : Nat}
    {ih : (T : Ty) → tyRank T < k → MVal H T → SVal T}
    {ih' : (T : Ty) → tyRank T < k' → MVal H T → SVal T}
    (hih : ∀ (T : Ty) (h : tyRank T < k) (h' : tyRank T < k') (v : MVal H T), ih T h v = ih' T h' v) :
    (fs : List (Name × Ty)) → (h : fieldsRank fs < k) → (h' : fieldsRank fs < k') →
    (x : MFields H fs) → MFields.copyBelow k ih fs h x = MFields.copyBelow k' ih' fs h' x
  | [], _, _, _ => rfl
  | (_, T) :: fs, _, _, x => by
    simp only [MFields.copyBelow]
    exact congr (congrArg SFields.cons (hih T _ _ x.1)) (MFields.copyBelow_congr hih fs _ _ x.2)

theorem SVal.array_ofList_congr {E : Ty} {l l' : List (SVal E)} (e : l = l')
    (h : l.length < 2 ^ 256) (h' : l'.length < 2 ^ 256) :
    SVal.array (SVec.ofList l) .nil h = SVal.array (SVec.ofList l') .nil h' := by
  subst e
  rfl

mutual
/-- The copy at one rank reads only the copies below it. -/
theorem MVal.copyAt_congr {H : HTy} (hp : Heap H) {k k' : Nat}
    {ih : (T : Ty) → tyRank T < k → MVal H T → SVal T}
    {ih' : (T : Ty) → tyRank T < k' → MVal H T → SVal T}
    (hih : ∀ (T : Ty) (h : tyRank T < k) (h' : tyRank T < k') (v : MVal H T), ih T h v = ih' T h' v) :
    (T : Ty) → (h : tyRank T < k + 1) → (h' : tyRank T < k' + 1) → (v : MVal H T) →
    MVal.copyAt hp k ih T h v = MVal.copyAt hp k' ih' T h' v
  | .prim _, _, _, _ => rfl
  | .ref R, h, h', v => MVal.copyRefAt_congr hp hih R h h' v

theorem MVal.copyRefAt_congr {H : HTy} (hp : Heap H) {k k' : Nat}
    {ih : (T : Ty) → tyRank T < k → MVal H T → SVal T}
    {ih' : (T : Ty) → tyRank T < k' → MVal H T → SVal T}
    (hih : ∀ (T : Ty) (h : tyRank T < k) (h' : tyRank T < k') (v : MVal H T), ih T h v = ih' T h' v) :
    (R : RefTy) → (h : tyRank (.ref R) < k + 1) → (h' : tyRank (.ref R) < k' + 1) →
    (r : HRef H R) → MVal.copyRefAt hp k ih R h r = MVal.copyRefAt hp k' ih' R h' r
  | .struct s, _, _, r => by
    simp only [MVal.copyRefAt]
    exact congrArg SVal.struct (MFields.copyBelow_congr hih (structDef s) _ _ (hp.get r))
  | .array E, h, h', r => by
    have e : MVal.copyAt hp k ih E (by simpa only [tyRank] using h) =
        MVal.copyAt hp k' ih' E (by simpa only [tyRank] using h') :=
      funext fun v => MVal.copyAt_congr hp hih E _ _ v
    simp only [MVal.copyRefAt]
    exact SVal.array_ofList_congr (congrArg (fun f => List.map f _) e) _ _
  | .fixed E n, h, h', r => by
    have e : MVal.copyAt hp k ih E (Nat.lt_of_succ_lt (by simpa only [tyRank] using h)) =
        MVal.copyAt hp k' ih' E (Nat.lt_of_succ_lt (by simpa only [tyRank] using h')) :=
      funext fun v => MVal.copyAt_congr hp hih E _ _ v
    simp only [MVal.copyRefAt, e]
  | .mapping _ _, _, _, r => (hp.get r : Empty).elim
end

/-- The copy at any two fuels past the type's rank is one copy. -/
theorem MVal.copyBelow_fuel {H : HTy} (hp : Heap H) : (k k' : Nat) → (T : Ty) →
    (h : tyRank T < k) → (h' : tyRank T < k') → (v : MVal H T) →
    MVal.copyBelow hp k T h v = MVal.copyBelow hp k' T h' v
  | 0, _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, h', _ => absurd h' (Nat.not_lt_zero _)
  | k + 1, k' + 1, T, h, h', v =>
    MVal.copyAt_congr hp (fun T h h' v => MVal.copyBelow_fuel hp k k' T h h' v) T h h' v

/-- The copy at any fuel past the type's rank is the copy. -/
theorem MVal.copyBelow_eq {H : HTy} (hp : Heap H) (k : Nat) (T : Ty) (h : tyRank T < k)
    (v : MVal H T) : MVal.copyBelow hp k T h v = v.copyMToSt hp :=
  MVal.copyBelow_fuel hp _ _ T h _ v

theorem MFields.copyBelow_get {H : HTy} (k : Nat) (ih : (T : Ty) → tyRank T < k → MVal H T → SVal T)
    {f : Name} : (fs : List (Name × Ty)) → (hfs : fieldsRank fs < k) → (x : MFields H fs) →
    {T : Ty} → (h : lookupBy f fs = some T) →
    ∃ hT, (MFields.copyBelow k ih fs hfs x).get h = ih T hT (MFields.get fs x h)
  | [], _, _, _, h => absurd h (by simp only [lookupBy, reduceCtorEq, not_false_eq_true])
  | (f', T') :: fs, hfs, x, T, h => by
    by_cases e : f = f'
    · have hT' := SFields.lookupBy_cons_pos e h
      subst hT'
      exact ⟨Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hfs, by
        simp only [MFields.copyBelow, SFields.get_cons, MFields.get, e, dite_true]⟩
    · obtain ⟨hT, he⟩ := MFields.copyBelow_get k ih fs (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hfs)
        x.2 (SFields.lookupBy_cons_neg e h)
      exact ⟨hT, by simp only [MFields.copyBelow, SFields.get_cons, MFields.get, e, dite_false, he]⟩

/-- **A struct copied to storage, at a member** (`selectOnCopyMem`): the
copy of the member's value. -/
theorem MVal.copyMToSt_findM_field {H : HTy} (hp : Heap H) {s f : Name} {T U : Ty}
    (r : HRef H (.struct s)) (hf : lookupBy f (structDef s) = some T) (p : Path T U) :
    (MVal.copyMToSt hp (T := .ref (.struct s)) r).findM (.field hf p) =
      (MVal.copyMToSt hp (hp.field r hf)).findM p := by
  obtain ⟨hT, he⟩ := MFields.copyBelow_get 4 (MVal.copyBelow hp 4) (structDef s)
    (Nat.lt_of_lt_of_le (Semantics.structDef_rank_lt s) (tyRank_le_rankBound (.ref (.struct s))))
    (hp.get r) hf
  show ((MFields.copyBelow 4 (MVal.copyBelow hp 4) (structDef s) _ (hp.get r)).get hf).findM p = _
  rw [he, MVal.copyBelow_eq]
  rfl

/-- **A dynamic array copied to storage, at an element**: the copy of the
element, within the array's length. -/
theorem MVal.copyMToSt_findM_at {H : HTy} (hp : Heap H) {E U : Ty} (r : HRef H (.array E))
    (i : PrimTy.uint.Denote) (p : Path E U) :
    (MVal.copyMToSt hp (T := .ref (.array E)) r).findM (.at i p) =
      ((MObj.elems .dyn (hp.get r))[i.1.toNat]?).bind (fun v => (MVal.copyMToSt hp v).findM p) := by
  simp only [MVal.copyMToSt, MVal.copyBelow, MVal.copyAt, MVal.copyRefAt, SVal.findM,
    SVec.toList_ofList, SList.toList_nil, List.append_nil, List.getElem?_map, MObj.elems_dyn]
  cases (hp.get r : {l : List (MVal H E) // l.length < 2 ^ 256}).1[i.1.toNat]? <;> rfl

/-- A fixed array copied to storage, at an element. -/
theorem MVal.copyMToSt_findM_atF {H : HTy} (hp : Heap H) {E U : Ty} {n : Nat}
    (r : HRef H (.fixed E n)) (i : PrimTy.uint.Denote) (p : Path E U) :
    (MVal.copyMToSt hp (T := .ref (.fixed E n)) r).findM (.atF i p) =
      ((MObj.elems .fixed (hp.get r))[i.1.toNat]?).bind (fun v => (MVal.copyMToSt hp v).findM p) := by
  simp only [MVal.copyMToSt, MVal.copyBelow, MVal.copyAt, MVal.copyRefAt, SVal.findM,
    SVec.toList_ofLen, List.getElem?_map, MObj.elems_fixed]
  cases (hp.get r : {l : List (MVal H E) // l.length = n}).1[i.1.toNat]? with
  | none => rfl
  | some v =>
    simp only [Option.map_some, Option.bind_some]
    exact congrArg (·.findM p) ((MVal.copyBelow_eq hp (rankBound E + 2) E _ v).trans
      (MVal.copyBelow_eq hp (rankBound E + 1) E _ v).symm)

/-- A dynamic array copied to storage has the array's length. -/
theorem MVal.copyMToSt_len {H : HTy} (hp : Heap H) {E : Ty} (r : HRef H (.array E)) :
    ((MVal.copyMToSt hp (T := .ref (.array E)) r).view : ArrView E).n = hp.len r .dyn := by
  simp only [MVal.copyMToSt, MVal.copyBelow, MVal.copyAt, MVal.copyRefAt, SVal.view_array,
    Heap.len, MObj.elems_dyn]
  exact (List.length_map _).trans rfl

/-- A word copied to storage is the word. -/
theorem MVal.copyMToSt_prim {H : HTy} (hp : Heap H) {P : PrimTy} (v : MVal H (.prim P)) :
    MVal.copyMToSt hp v = .prim v := by
  cases P <;> rfl

/-- **A member of a memory struct copied into storage** holds what the
object held there. -/
theorem MVal.copyMToSt_field {H : HTy} (hp : Heap H) {s f : Name} {p : PrimTy}
    (r : HRef H (.struct s)) (hf : lookupBy f (structDef s) = some (.prim p)) :
    (MVal.copyMToSt hp (T := .ref (.struct s)) r).find (.field hf .nil) =
      some (.prim (hp.field r hf)) := by
  rw [SVal.find_eq_findM, MVal.copyMToSt_findM_field]
  exact congrArg some (MVal.copyMToSt_prim hp _)

end CopyMem

/-! ## The laws by solkey's taclets

`memoryRules.key`, `structMemoryRules.key` and the cross-domain taclets,
each stated on the typed heap and proved by the lemma above it; a taclet's
`\then` is its name, its `\else` (the frame) its name with `Frame`.  A rule
whose term has no counterpart on the typed heap is not restated:
`readFromEmptyMemory` and `newFromEmptyMemory` (a memory grows from the
global part's heap, never from an empty one), `readR*` (a path is read one
address at a time), and `initIdentity` (a reference member is allocated
with its parent, so it is a member read like a word). -/

section Solkey

/-- **readOnWrite** `\then`: a write reads back where it lands. -/
theorem Grown.readOnWrite {H : HTy} {T : Ty} {m m' : Grown H (fun _ => Unit)} {a : MAddrT T}
    {v : MvT T} (h : m.writeT a v = some m') : m'.readId a = some v :=
  (Grown.writeT_facts h).1

/-- **readOnWrite** `\else`: a write leaves every address apart from it. -/
theorem Grown.readOnWriteFrame {H : HTy} {T U : Ty} {m m' : Grown H (fun _ => Unit)}
    {a : MAddrT T} {v : MvT T} (h : m.writeT a v = some m') (b : MAddrT U) (hab : a.Apart b) :
    m'.readId b = m.readId b :=
  (Grown.writeT_facts h).2 b hab

/-- **readOnAddM** `\else`: an allocation leaves every older object. -/
theorem Grown.readOnAddMFrame {H : HTy} (μ₀ : Grown H (fun _ => Unit)) (R : RefTy)
    (hR : (Ty.ref R).mapFree = true) {T : Ty} (bd : MAddrT T) (hid : bd.id < μ₀.H'.length) :
    (μ₀.then (μ₀.heap.allocDefault R hR)).readId bd = μ₀.readId bd :=
  Grown.readId_then_old μ₀ _ (SVal.keeps_copyStToM _ hR μ₀.heap) bd hid

/-- An allocation's identity is past every older one (Lean only: the
freshness behind `newFromAdd`, KeY's `idp1 ≠ idp2`). -/
theorem Grown.alloc_fresh {H : HTy} {R : RefTy} (g : Grown H (MObj · R)) :
    H.length ≤ ((Grown.alloc g).val : HRef _ R).id :=
  Grown.alloc_id_ge g

/-- **readOnAddM** `\then`, then **initMember**: a member of a fresh struct
reads the default of its type. -/
theorem Heap.initMember {H : HTy} (hp : Heap H) {s f : Name} {p : PrimTy}
    (hR : (Ty.ref (.struct s)).mapFree = true) (hf : lookupBy f (structDef s) = some (.prim p)) :
    (hp.allocDefault (.struct s) hR).heap.field (hp.allocDefault (.struct s) hR).val hf =
      (((SVal.view (SVal.dflt (.ref (.struct s))) : SFields _).get hf).view : p.Denote) :=
  SVal.copyStToM_field hp _ hR hf

/-- **initSize**: a fresh dynamic array has no elements. -/
theorem Heap.initSize {H : HTy} (hp : Heap H) (E : Ty)
    (hR : (Ty.ref (.array E)).mapFree = true) :
    (hp.allocDefault (.array E) hR).heap.len (hp.allocDefault (.array E) hR).val .dyn = 0 :=
  Heap.allocDefault_array_len hp E hR

/-- **readFromCopyToStorage** `\then`: a member of a storage struct copied
into memory reads what the struct held there. -/
theorem SVal.readFromCopyToStorage {H : HTy} (hp : Heap H) {s f : Name} {p : PrimTy}
    (sv : SVal (.ref (.struct s))) (hT : (Ty.ref (.struct s)).mapFree = true)
    (hf : lookupBy f (structDef s) = some (.prim p)) :
    (sv.copyStToM hp hT).heap.field (sv.copyStToM hp hT).val hf =
      (((SVal.view sv : SFields _).get hf).view : p.Denote) :=
  SVal.copyStToM_field hp sv hT hf

/-- **readFromCopyToStorage** `\else`, and **readFromCopyToStorageIdentity**
`\else`: a copy into memory leaves every older object (the premise the
object older than the copy, where KeY's is `idp1 ≠ idp2`). -/
theorem Grown.readFromCopyToStorageFrame {H : HTy} (μ₀ : Grown H (fun _ => Unit)) {U : Ty}
    (v : SVal U) (hU : U.mapFree = true) {T : Ty} (bd : MAddrT T) (hid : bd.id < μ₀.H'.length) :
    (μ₀.then (v.copyStToM μ₀.heap hU)).readId bd = μ₀.readId bd :=
  Grown.readId_then_old μ₀ _ (SVal.keeps_copyStToM v hU μ₀.heap) bd hid

/-- **findOnCopy** at a one-member path, **selectOnCopyMemPrim**: a member of
a memory struct copied into storage holds what the object held there. -/
theorem MVal.findOnCopy {H : HTy} (hp : Heap H) {s f : Name} {p : PrimTy}
    (r : HRef H (.struct s)) (hf : lookupBy f (structDef s) = some (.prim p)) :
    (MVal.copyMToSt hp (T := .ref (.struct s)) r).find (.field hf .nil) =
      some (.prim (hp.field r hf)) :=
  MVal.copyMToSt_field hp r hf

end Solkey

end Solidity
