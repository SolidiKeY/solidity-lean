import Solidity.Calculus.StateFacts
import Solidity.Semantics.HeapErase

/-!
# The Theory of memory, typed

solkey's memory theory (`memoryRules.key`, `structMemoryRules.key`) read on
the typed heap: a memory is a heap grown from the global part's
(`Grown H`), an address an identity with a member or an element
(`MAddrT T`), and each law a statement about `Grown.readT`, `writeT` and
the allocations (`Heap.allocDefault`, `SVal.copyStToM`), generic in the
types it is read at, as the storage laws are generic over their
locations (`Theory/Typed/Obs.lean`).

* **readOnWrite**, **readWriteDifferent**: a write reads back where it
  lands, and leaves every address apart from it (`Grown.writeT_facts`,
  `Heap.readAddr_writeAddr_same`, `Heap.readAddr_writeAddr_apart`).
* **readAddDifferent**, **newAddDifferent**: an allocation leaves every
  older object (`Heap.readAddr_allocDefault`, `MAddrT.resolve_wk`); its
  objects are new (`Grown.alloc_id_ge`).
* **readAddEqual**, **initMember**, **defaultValueInt**/**defaultValueBool**:
  a fresh object reads its default (`Grown.readAddM_fresh_field`).
* **readFromCopyToStorage**, **selectOnCopyMem**: a copy between storage
  and memory reads what it copied (`SVal.copyStToM_field`,
  `MVal.copyMToSt_field`).

The laws are proved on the typed heap, through its erasure where the
interpreter's lemmas already answer (`Heap.readAddr_erase`).
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
      simp only [Heap.readAddr, Heap.index, hb.1, if_true, Heap.get_set_same, MObj.elems_setElem,
        List.getElem?_set_self hb.2]
    · simp only [reduceCtorEq] at h

/-- **A write leaves an address apart from it** (`readWriteDifferent`). -/
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
            by_cases hj : 0 ≤ j
            · have hn : i.toNat ≠ j.toNat := by omega
              simp only [hj, if_true, List.getElem?_set_ne hn]
            · simp only [hj, if_false]
        · simp only [Heap.readAddr, Heap.index, Heap.get_set_ne _ r r' e]
    · simp only [reduceCtorEq] at h

end Heap

/-- The object an address is in. -/
def MAddrT.id {T : Ty} : MAddrT T → Nat
  | .field id _ => id
  | .index id _ _ => id


theorem HRef.id_lt {H : HTy} {R : RefTy} (r : HRef H R) : r.id < H.length :=
  (List.getElem?_eq_some_iff.1 r.get?).1


/-- The typed read of an address on the erasure. -/
theorem Heap.readAddr_erase {H : HTy} {σ : Semantics.State} {hp : Heap H}
    (hh : σ.heap = hp.erase) {T : Ty} (a : MAddr H T) :
    Solidity.readAddr σ a.erase = toRes (MVal.erase T) (hp.readAddr a) := by
  cases a with
  | field r h => exact Heap.readField_erase hh r h
  | index r a i => exact Heap.readIndex_erase hh r a i

theorem toRes_inj {α α' β : Type} {f : α → β} {g : α' → β} {x : Option α} {y : Option α'}
    (h : toRes f x = toRes g y) : x.map f = y.map g := by
  cases x <;> cases y <;> simp_all only [toRes, Option.map_none, Option.map_some,
    reduceCtorEq, Except.ok.injEq]

/-- An allocation keeps every object below it: the slot at an address
there reads the same, erased. -/
theorem Heap.readAddr_allocDefault {H : HTy} (hp : Heap H) (R : RefTy)
    (hR : (Ty.ref R).mapFree = true) {T : Ty} (ra : MAddr H T) :
    ((hp.allocDefault R hR).heap.readAddr (ra.wk (hp.allocDefault R hR).ext)).map (MVal.erase T) =
      (hp.readAddr ra).map (MVal.erase T) := by
  let τ₀ : Semantics.State := Heap.into { storage := [] } hp
  have ha := Heap.allocDefault_erase (σ := τ₀) (hp := hp) rfl rfl R hR
  have hx := SemanticsProperties.allocDefault_heapExt ha
  have hid : ra.erase.id < τ₀.nextId := by
    cases ra with
    | field r _ => exact HRef.id_lt r
    | index r _ _ => exact HRef.id_lt r
  have h₀ := Heap.readAddr_erase (σ := τ₀) (hp := hp) rfl ra
  have h₁ := Heap.readAddr_erase (σ := Heap.into τ₀ (hp.allocDefault R hR).heap) rfl
    (ra.wk (hp.allocDefault R hR).ext)
  rw [MAddr.erase_wk, readAddr_heapExt hx hid, h₀] at h₁
  exact (toRes_inj h₁).symm

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


/-- The untyped address. -/
def MAddrT.eraseT {T : Ty} : MAddrT T → Semantics.Addr
  | .field (f := f) id _ => .memoryField id f
  | .index id _ i => .memoryIndex id i

theorem MAddrT.erase_resolve {H : HTy} {T : Ty} {a : MAddrT T} {ra : MAddr H T}
    (h : a.resolve H = some ra) : ra.erase = a.eraseT := by
  cases a with
  | field id hf =>
    simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    simp only [HRef.ofId?] at hr
    split at hr
    · cases hr; rfl
    · cases hr
  | index id a i =>
    simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    simp only [HRef.ofId?] at hr
    split at hr
    · cases hr; rfl
    · cases hr


/-- The erasure the fresh reads are read on: the heap after the allocation. -/
abbrev Grown.allocSt {H : HTy} (μ₀ : Grown H (fun _ => Unit)) (R : RefTy)
    (hR : (Ty.ref R).mapFree = true) : Semantics.State :=
  Heap.into (Heap.into { storage := [] } μ₀.heap) (μ₀.heap.allocDefault R hR).heap

theorem Grown.allocSt_copy {H : HTy} (μ₀ : Grown H (fun _ => Unit)) (R : RefTy)
    (hR : (Ty.ref R).mapFree = true) :
    Semantics.copyStToM (Heap.into { storage := [] } μ₀.heap) (Semantics.defaultForTy (.ref R)) =
      .ok (μ₀.allocSt R hR, .ref (μ₀.heap.allocDefault R hR).val.id) :=
  Close.allocDefault_copy (Heap.allocDefault_erase rfl rfl R hR)


/-- A read one member below a root's path, untyped. -/
theorem Semantics.State.findStorage_snoc (σ : Semantics.State) (root : Name)
    (segs : List Semantics.Seg) (sg : Semantics.Seg) :
    σ.findStorage root (segs ++ [sg]) = σ.findStorage root segs >>= fun w => w.find [sg] := by
  unfold Semantics.State.findStorage
  cases lookupBy root σ.storage with
  | none => rfl
  | some v => exact SemanticsProperties.SVal.find_append v segs [sg]

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

/-- **A member of a storage struct copied into memory** reads what the
struct held there (the untyped `Close.copyStToM_member`, on the erasure). -/
theorem SVal.copyStToM_field {H : HTy} (hp : Heap H) {s f : Name} {p : PrimTy}
    (sv : SVal (.ref (.struct s))) (hT : (Ty.ref (.struct s)).mapFree = true)
    (hf : lookupBy f (structDef s) = some (.prim p)) (hl : ¬ f = "length") :
    (sv.copyStToM hp hT).heap.field (sv.copyStToM hp hT).val hf =
      (((SVal.view sv : SFields _).get hf).view : p.Denote) := by
  let g := sv.copyStToM hp hT
  let τ₀ : Semantics.State := Heap.into { storage := [] } hp
  have hc : Semantics.copyStToM τ₀ sv.erase = .ok (Heap.into τ₀ g.heap, .ref g.val.id) :=
    SVal.copyStToM_erase sv hT hp τ₀ rfl rfl
  have hmem := Close.copyStToM_member hc hl
  have hrd : Close.readVal (Heap.into τ₀ g.heap) (.memoryField g.val.id f) =
      .ok (PrimTy.erase (g.heap.field g.val hf)) := by
    have h₁ := Heap.readAddr_erase (σ := Heap.into τ₀ g.heap) (hp := g.heap) rfl
      (MAddr.field g.val hf)
    simp only [Close.readVal]
    rw [show (Semantics.Addr.memoryField g.val.id f) = (MAddr.field g.val hf).erase from rfl, h₁]
    simp only [Heap.readAddr, toRes, Semantics.Res.ok_bind']
    exact MVal.asValue_erase_prim _
  have hfind : sv.erase.find [.field f] = .ok ((SVal.view sv : SFields _).get hf).erase := by
    have := SVal.find_erase sv (.field hf .nil)
    exact this
  rw [hmem, hfind, Semantics.Res.ok_bind', SVal.asValue_erase_prim] at hrd
  exact (PrimTy.erase_injective (Except.ok.inj hrd)).symm

/-- **A member of a memory struct copied into storage** holds what the
object held there (the untyped `Close.copyMem_member`, on the erasure). -/
theorem MVal.copyMToSt_field {H : HTy} (hp : Heap H) {s f : Name} {p : PrimTy}
    (r : HRef H (.struct s)) (hf : lookupBy f (structDef s) = some (.prim p))
    (hl : ¬ f = "length") :
    (MVal.copyMToSt hp (T := .ref (.struct s)) r).find (.field hf .nil) =
      some (.prim (hp.field r hf)) := by
  let τ : Semantics.State := Heap.into { storage := [] } hp
  have hcm := MVal.copyMem_erase (σ := τ) (hp := hp) rfl (T := .ref (.struct s)) r
  have hmem := Close.copyMem_member hcm hl
  have h₁ := Heap.readAddr_erase (σ := τ) (hp := hp) rfl (MAddr.field r hf)
  rw [show (MAddr.field r hf).erase = Semantics.Addr.memoryField r.id f from rfl] at h₁
  rw [h₁] at hmem
  simp only [Heap.readAddr, toRes, Semantics.Res.ok_bind', MVal.erase, Close.copyLeaf_prim] at hmem
  have hfe := SVal.find_erase (MVal.copyMToSt hp (T := .ref (.struct s)) r) (.field hf .nil)
  rw [show (Path.field hf (Path.nil (T := .prim p))).erase = [Semantics.Seg.field f] from rfl,
    hmem] at hfe
  cases hx : (MVal.copyMToSt hp (T := .ref (.struct s)) r).find (.field hf .nil) with
  | none => rw [hx] at hfe; cases hfe
  | some y =>
    rw [hx] at hfe
    simp only [toRes, Except.ok.injEq] at hfe
    rw [← SVal.erase_prim] at hfe
    rw [SVal.erase_injective hfe.symm]


/-! ## Allocations: older objects, and the fresh root -/

/-- A copy into memory keeps every object below it: the slot at an address
there reads the same, erased. -/
theorem Heap.readAddr_copyStToM {H : HTy} (hp : Heap H) {U : Ty} (v : SVal U)
    (hU : U.mapFree = true) {T : Ty} (ra : MAddr H T) :
    ((v.copyStToM hp hU).heap.readAddr (ra.wk (v.copyStToM hp hU).ext)).map (MVal.erase T) =
      (hp.readAddr ra).map (MVal.erase T) := by
  let τ₀ : Semantics.State := Heap.into { storage := [] } hp
  have hc := SVal.copyStToM_erase v hU hp τ₀ rfl rfl
  have hx := SemanticsProperties.copyStToM_heapExt τ₀ v.erase _ _ hc
  have hid : ra.erase.id < τ₀.nextId := by
    cases ra with
    | field r _ => exact HRef.id_lt r
    | index r _ _ => exact HRef.id_lt r
  have h₀ := Heap.readAddr_erase (σ := τ₀) (hp := hp) rfl ra
  have h₁ := Heap.readAddr_erase (σ := Heap.into τ₀ (v.copyStToM hp hU).heap) rfl
    (ra.wk (v.copyStToM hp hU).ext)
  rw [MAddr.erase_wk, readAddr_heapExt hx hid, h₀] at h₁
  exact (toRes_inj h₁).symm

/-- A read of an address the grown heap `μ₀.then g` resolves as `μ₀` does:
the old object, read there. -/
theorem Grown.read_then_old {H : HTy} (μ₀ : Grown H (fun _ => Unit)) {α : HTy → Type}
    (g : Grown μ₀.H' α)
    (hg : ∀ {T : Ty} (ra : MAddr μ₀.H' T),
      (g.heap.readAddr (ra.wk g.ext)).map (MVal.erase T) = (μ₀.heap.readAddr ra).map (MVal.erase T))
    {T : Ty} (bd : MAddrT T) (hid : bd.id < μ₀.H'.length) :
    ((bd.resolve (μ₀.then g).H').bind fun rb => (μ₀.then g).heap.readAddr rb).map (MVal.erase T) =
      ((bd.resolve μ₀.H').bind fun rb => μ₀.heap.readAddr rb).map (MVal.erase T) := by
  show ((bd.resolve g.H').bind fun rb => g.heap.readAddr rb).map _ = _
  rw [MAddrT.resolve_wk g.ext bd hid]
  cases bd.resolve μ₀.H' with
  | none => rfl
  | some rb =>
    simp only [Option.map_some, Option.bind_some]
    exact hg rb

/-- **readAddDifferent**: below an allocation, an address whose object is
older reads what it read (erased; a word and an identity read so are
equal). -/
theorem Grown.readAddM_old {H : HTy} (μ₀ : Grown H (fun _ => Unit)) (R : RefTy)
    (hR : (Ty.ref R).mapFree = true) {T : Ty} (bd : MAddrT T) (hid : bd.id < μ₀.H'.length) :
    ((bd.resolve (μ₀.then (μ₀.heap.allocDefault R hR)).H').bind fun rb =>
        (μ₀.then (μ₀.heap.allocDefault R hR)).heap.readAddr rb).map (MVal.erase T) =
      ((bd.resolve μ₀.H').bind fun rb => μ₀.heap.readAddr rb).map (MVal.erase T) :=
  Grown.read_then_old μ₀ _ (fun ra => Heap.readAddr_allocDefault μ₀.heap R hR ra) bd hid

/-- **readAddDifferent** for a copy into memory (`copySt`): an older
object reads what it read. -/
theorem Grown.readCopySt_old {H : HTy} (μ₀ : Grown H (fun _ => Unit)) {U : Ty} (v : SVal U)
    (hU : U.mapFree = true) {T : Ty} (bd : MAddrT T) (hid : bd.id < μ₀.H'.length) :
    ((bd.resolve (μ₀.then (v.copyStToM μ₀.heap hU)).H').bind fun rb =>
        (μ₀.then (v.copyStToM μ₀.heap hU)).heap.readAddr rb).map (MVal.erase T) =
      ((bd.resolve μ₀.H').bind fun rb => μ₀.heap.readAddr rb).map (MVal.erase T) :=
  Grown.read_then_old μ₀ _ (fun ra => Heap.readAddr_copyStToM μ₀.heap v hU ra) bd hid

/-- A word read so, erased, is the word. -/
theorem MVal.erase_prim_inj {H H' : HTy} {p : PrimTy} {x : Option (MVal H (.prim p))}
    {y : Option (MVal H' (.prim p))} (h : x.map (MVal.erase (.prim p)) = y.map (MVal.erase (.prim p))) :
    (x : Option p.Denote) = (y : Option p.Denote) := by
  cases x <;> cases y <;> simp only [Option.map_none, Option.map_some, reduceCtorEq,
    Option.some.injEq] at h ⊢
  exact PrimTy.erase_injective (Semantics.MVal.prim.inj h)

/-- An identity read so, erased, is the identity. -/
theorem MVal.erase_ref_inj {H H' : HTy} {R : RefTy} {x : Option (MVal H (.ref R))}
    {y : Option (MVal H' (.ref R))} (h : x.map (MVal.erase (.ref R)) = y.map (MVal.erase (.ref R))) :
    x.bind (fun r => some (r : HRef H R).id) = y.bind (fun r => some (r : HRef H' R).id) := by
  cases x <;> cases y <;> simp only [Option.map_none, Option.map_some, reduceCtorEq,
    Option.some.injEq, Option.bind_some, Option.bind_none] at h ⊢
  exact Semantics.MVal.ref.inj h


/-! ## Lengths: what a read of an element needs -/

section Len

/-- An element reads exactly below the array's length. -/
theorem Heap.readAddr_index_isSome {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H) (r : HRef H R)
    (a : ArrTy R E) (i : Int) :
    (hp.readAddr (.index r a i)).isSome = decide (0 ≤ i ∧ i.toNat < hp.len r a) := by
  simp only [Heap.readAddr, Heap.index, Heap.len]
  by_cases h0 : 0 ≤ i
  · simp only [h0, if_true, true_and]
    by_cases hl : i.toNat < (MObj.elems a (hp.get r)).length <;> simp [hl]
  · simp only [h0, if_false, false_and, Option.isSome_none, decide_false]

/-- A slot writes exactly where it reads. -/
theorem Heap.writeAddr_isSome {H : HTy} {T : Ty} (hp : Heap H) (ad : MAddr H T) (v : MVal H T) :
    (hp.writeAddr ad v).isSome = (hp.readAddr ad).isSome := by
  cases ad with
  | field r h => rfl
  | index r a i =>
    rw [Heap.readAddr_index_isSome]
    simp only [Heap.writeAddr, Heap.setIndex, Heap.len]
    split <;> simp_all

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

/-- Two arrays whose elements read at the same indices have one length. -/
theorem Heap.len_eq_of_index {H H' : HTy} {R R' : RefTy} {E : Ty} (hp : Heap H) (hp' : Heap H')
    (r : HRef H R) (r' : HRef H' R') (a : ArrTy R E) (a' : ArrTy R' E)
    (h : ∀ i : Int, (hp.readAddr (.index r a i)).isSome = (hp'.readAddr (.index r' a' i)).isSome) :
    hp.len r a = hp'.len r' a' := by
  have := h (min (hp.len r a) (hp'.len r' a'))
  simp only [Heap.readAddr_index_isSome, decide_eq_decide] at this
  omega

theorem Objs.get_snoc_last {H : HTy} {R : RefTy} (o : MObj H R) : (Rs : List RefTy) →
    (os : Objs H Rs) → (h : (Rs ++ [R])[Rs.length]? = some R) →
    Objs.get (Rs ++ [R]) (Objs.snoc o Rs os) Rs.length h = o
  | [], _, _ => rfl
  | _ :: Rs, os, _ => Objs.get_snoc_last o Rs os.2 _

/-- The object allocated is the one given. -/
theorem Heap.get_alloc {H : HTy} {R : RefTy} (hp : Heap H) (o : MObj H R) :
    (hp.alloc o).1.get (hp.alloc o).2 = MObj.wk (List.prefix_append H [R]) R o :=
  Objs.get_snoc_last _ H _ _

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

/-- **A grown heap keeps every older array's length**, where it reads the
older objects as they were. -/
theorem Grown.lenU_then_old {H : HTy} (μ₀ : Grown H (fun _ => Unit)) {α : HTy → Type}
    (g : Grown μ₀.H' α)
    (hg : ∀ {T : Ty} (ra : MAddr μ₀.H' T),
      (g.heap.readAddr (ra.wk g.ext)).map (MVal.erase T) = (μ₀.heap.readAddr ra).map (MVal.erase T))
    {E : Ty} (id : Nat) (hid : id < μ₀.H'.length) :
    (HRef.ofId? (μ₀.then g).H' (.array E) id).map (fun r => (μ₀.then g).heap.lenU r) =
      (HRef.ofId? μ₀.H' (.array E) id).map (fun r => μ₀.heap.lenU r) := by
  show (HRef.ofId? g.H' (.array E) id).map (fun r => g.heap.lenU r) = _
  rw [HRef.ofId?_wk g.ext _ hid]
  cases HRef.ofId? μ₀.H' (.array E) id with
  | none => rfl
  | some r =>
    simp only [Option.map_some, Option.some.injEq]
    refine Heap.lenU_eq (Heap.len_eq_of_index _ _ _ _ .dyn .dyn fun i => ?_)
    have := hg (MAddr.index r .dyn i)
    rw [← Option.isSome_map (f := MVal.erase _), ← Option.isSome_map (f := MVal.erase _)
      (x := μ₀.heap.readAddr _), ← this]
    rfl

theorem Grown.lenU_addM_old {H : HTy} (μ₀ : Grown H (fun _ => Unit)) (R : RefTy)
    (hR : (Ty.ref R).mapFree = true) {E : Ty} (id : Nat) (hid : id < μ₀.H'.length) :
    (HRef.ofId? (μ₀.then (μ₀.heap.allocDefault R hR)).H' (.array E) id).map
        (fun r => (μ₀.then (μ₀.heap.allocDefault R hR)).heap.lenU r) =
      (HRef.ofId? μ₀.H' (.array E) id).map (fun r => μ₀.heap.lenU r) :=
  Grown.lenU_then_old μ₀ _ (fun ra => Heap.readAddr_allocDefault μ₀.heap R hR ra) id hid

theorem Grown.lenU_copySt_old {H : HTy} (μ₀ : Grown H (fun _ => Unit)) {U : Ty} (v : SVal U)
    (hU : U.mapFree = true) {E : Ty} (id : Nat) (hid : id < μ₀.H'.length) :
    (HRef.ofId? (μ₀.then (v.copyStToM μ₀.heap hU)).H' (.array E) id).map
        (fun r => (μ₀.then (v.copyStToM μ₀.heap hU)).heap.lenU r) =
      (HRef.ofId? μ₀.H' (.array E) id).map (fun r => μ₀.heap.lenU r) :=
  Grown.lenU_then_old μ₀ _ (fun ra => Heap.readAddr_copyStToM μ₀.heap v hU ra) id hid

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

/-- **An allocation's identity is new** (`newAddDifferent`): past every
identity of the heap it grows. -/
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

/-! ## Copies into storage: what a copy reads (`copyMem`) -/

section CopyMem

theorem SVec.toList_ofLen {α : Type} {E : Ty} (f : α → SVal E) : (n : Nat) → (l : List α) →
    (h : l.length = n) → (SVec.ofLen f n l h).toList = l.map f
  | 0, [], _ => by simp only [SVec.ofLen, SVec.toList_nil, List.map_nil]
  | n + 1, x :: xs, h => by
    simp only [SVec.ofLen, SVec.toList_cons, List.map_cons, SVec.toList_ofLen f n xs]
  | 0, _ :: _, h => by simp only [List.length_cons, Nat.add_one_ne_zero] at h
  | _ + 1, [], h => by simp only [List.length_nil, Nat.zero_ne_add_one] at h

/-- The copy at any fuel past the type's rank is the copy. -/
theorem MVal.copyBelow_eq {H : HTy} (hp : Heap H) (k : Nat) (T : Ty) (h : tyRank T < k)
    (v : MVal H T) : MVal.copyBelow hp k T h v = v.copyMToSt hp := by
  have e₁ := MVal.copyBelow_erase (σ := Heap.into { storage := [] } hp) (hp := hp) rfl k T h v _
    (RemOk.all hp T)
  have e₂ := MVal.copyBelow_erase (σ := Heap.into { storage := [] } hp) (hp := hp) rfl _ T
    (Nat.lt_succ_of_le (tyRank_le_rankBound T)) v _ (RemOk.all hp T)
  exact SVal.erase_injective (Except.ok.inj (e₁.symm.trans e₂))

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
    (i : Int) (p : Path E U) :
    (MVal.copyMToSt hp (T := .ref (.array E)) r).findM (.at i p) =
      if 0 ≤ i then ((MObj.elems .dyn (hp.get r))[i.toNat]?).bind
        (fun v => (MVal.copyMToSt hp v).findM p) else none := by
  simp only [MVal.copyMToSt, MVal.copyBelow, MVal.copyAt, MVal.copyRefAt, SVal.findM,
    SVec.toList_ofList, SList.toList_nil, List.append_nil, List.getElem?_map, MObj.elems_dyn]
  split
  · cases (hp.get r : {l : List (MVal H E) // l.length < 2 ^ 256}).1[i.toNat]? <;> rfl
  · rfl

/-- A fixed array copied to storage, at an element. -/
theorem MVal.copyMToSt_findM_atF {H : HTy} (hp : Heap H) {E U : Ty} {n : Nat}
    (r : HRef H (.fixed E n)) (i : Int) (p : Path E U) :
    (MVal.copyMToSt hp (T := .ref (.fixed E n)) r).findM (.atF i p) =
      if 0 ≤ i then ((MObj.elems .fixed (hp.get r))[i.toNat]?).bind
        (fun v => (MVal.copyMToSt hp v).findM p) else none := by
  simp only [MVal.copyMToSt, MVal.copyBelow, MVal.copyAt, MVal.copyRefAt, SVal.findM,
    SVec.toList_ofLen, List.getElem?_map, MObj.elems_fixed]
  split
  · cases (hp.get r : {l : List (MVal H E) // l.length = n}).1[i.toNat]? with
    | none => rfl
    | some v =>
      simp only [Option.map_some, Option.bind_some]
      exact congrArg (·.findM p) ((MVal.copyBelow_eq hp (rankBound E + 2) E _ v).trans
        (MVal.copyBelow_eq hp (rankBound E + 1) E _ v).symm)
  · rfl

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

end CopyMem

end Solidity
