import Solidity.Calculus.CloseScoped
import Solidity.Calculus.TermLaws

/-!
# `sol_close`'s storage frame, typed

A storage write under the box, named on the spot with what the typed laws
say of the storage it returns (`Calculus/TermLaws.lean`'s frame section):
solkey's `findOnSave` at the path written and below it, and its
`findOnSaveFrame`, `lenOnSaveFrame` where the paths part, the parting read
as the Theory's `diverges` on the references' segments (`SRef.absT`), which
the closer computes, a symbolic key by a hypothesis `k != j` of the formula
or a branch.  An index check (`Storage.checkIndex`) is framed as an array's
length is: it reads the length only (or nothing, for a mapping).

The references are read in one normal form, a root followed by a path
(`SRef.append`), so that a fact about the reads below a write meets a read
written member by member.
-/

namespace Solidity

open Theory.StValue (diverges lengthSeg)
open Semantics (lookupBy structDef)

namespace Storage

variable {C : Contract}

/-- An index check reads the length of an array, and only that: a save
below one of the array's slots leaves it. -/
theorem inBounds_saveM {R : RefTy} {k : PrimTy} {V W : Ty} (it : IndexTy R k V) (i : Int)
    {y y' : SVal (.ref R)} {rr : Path (.ref R) W} {v : SVal W} (h : y.saveM rr v = some y')
    (hne : rr.erase ≠ []) : inBounds it i y' = inBounds it i y := by
  cases it with
  | map => rfl
  | arr a =>
    cases a with
    | fixed => rfl
    | dyn =>
      cases rr with
      | nil => exact absurd rfl hne
      | «at» j rr' =>
        show (if 0 ≤ i ∧ i.toNat < (SVal.view y' : ArrView _).n then some () else none) =
          (if 0 ≤ i ∧ i.toNat < (SVal.view y : ArrView _).n then some () else none)
        rw [SVal.saveM_at_n h]

/-- **A save leaves an index check** where it parts from the array's
length: elsewhere, or below one of its slots (solkey's `lenOnSaveFrame`,
which the check reads). -/
theorem checkIndex_save_frame {k : PrimTy} {V : Ty} {T : Ty} {R' : RefTy}
    {st st' : Storage C} {r : SRef C T} {v : SVal T} {q : SRef C (.ref R')}
    (it : IndexTy R' k V) (i : Int)
    (hd : diverges r.absT (q.absT ++ [lengthSeg]) = true) (h : st.save r v = some st') :
    st'.checkIndex q it i = st.checkIndex q it i := by
  rcases diverges_append_single hd with hd | ⟨rest, hne, he⟩
  · simp only [Storage.checkIndex, find_save_frame hd h]
  · obtain ⟨x', hs, rfl⟩ := save_some h
    rcases r with ⟨n, hr, p⟩
    rcases q with ⟨n', hq, p'⟩
    simp only [SRef.absT, Theory.rootPath, List.cons_append, List.cons.injEq,
      Semantics.Seg.field.injEq] at he
    obtain ⟨rfl, he⟩ := he
    rename_i T₁ T₂
    obtain rfl : T₁ = T₂ := Option.some.inj (hr.symm.trans hq)
    obtain ⟨rr, rfl, hrr⟩ := Path.split_of_erase p' p he
    rw [SVal.save_eq_saveM] at hs
    obtain ⟨y, y', hy, hy', hx'⟩ := SVal.saveM_append _ p' rr v hs
    have hfy' : x'.findM p' = some y' := SVal.findM_saveM _ p' y' hx'
    show (((SFields.set st hr x').get hr).find p').bind _ = ((st.get hr).find p').bind _
    rw [SFields.get_set_same, SVal.find_eq_findM, SVal.find_eq_findM, hfy', hy]
    simp only [Option.bind_some]
    exact inBounds_saveM it i hy' (hrr ▸ hne)

/-- What a write at `r` saves there: the word, or the value laid over what
is there (`Storage.write`). -/
def writeVal {T : Ty} (st : Storage C) (r : SRef C T) (v : SVal T) : Option (SVal T) :=
  if v.isPrim then some v else (st.find r).map fun cur => cur.overlay v

theorem write_eq_bind {T : Ty} (st : Storage C) (r : SRef C T) (v : SVal T) :
    st.write r v = (st.writeVal r v).bind (st.save r) := by
  unfold Storage.write writeVal
  split
  · rfl
  · cases st.find r <;> rfl

end Storage

/-! ## A copy laid over a struct, member by member -/

theorem SFields.get_overlay {f : Name} : {fs : List (Name × Ty)} → {T : Ty} →
    (os ns : SFields fs) → (h : lookupBy f fs = some T) →
    (os.overlay ns).get h = (os.get h).overlay (ns.get h)
  | [], _, .nil, .nil, h => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, T, .cons o os, .cons n ns, h => by
    rw [SFields.overlay_cons, SFields.get_cons, SFields.get_cons, SFields.get_cons]
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      simp only [e, dite_true]
    · simp only [e, dite_false]
      exact SFields.get_overlay os ns _

/-- A word laid over a word is the new one. -/
theorem SVal.overlay_prim' {p : PrimTy} (o n : SVal (.prim p)) : o.overlay n = n := by
  cases n; exact SVal.overlay_prim o _

/-- **A member of a struct copy** (the untyped `Close.find_overlay_fields`):
the new struct's member laid over the old one's. -/
theorem SVal.find_overlay_field {s f : Name} {T U : Ty} (o n : SVal (.ref (.struct s)))
    (h : lookupBy f (structDef s) = some T) (p : Path T U) :
    (o.overlay n).find (.field h p) =
      (n.find (.field h .nil)).bind fun n' => (((SVal.view o : SFields _).get h).overlay n').find p := by
  cases o with
  | struct ofs =>
    cases n with
    | struct nfs =>
      rw [SVal.overlay_struct, SVal.find_field, SFields.get_overlay, SVal.find_field,
        SVal.find_nil, Option.bind_some, SVal.view_struct]

/-! ## A delete, member by member -/

theorem SFields.get_defaultOf {f : Name} : {fs : List (Name × Ty)} → {T : Ty} →
    (xs : SFields fs) → (h : lookupBy f fs = some T) →
    xs.defaultOf.get h = (xs.get h).defaultOf
  | [], _, .nil, h => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, T, .cons x xs, h => by
    rw [SFields.defaultOf_cons, SFields.get_cons, SFields.get_cons]
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      simp only [e, dite_true]
    · simp only [e, dite_false]
      exact SFields.get_defaultOf xs _

/-- A word reset is the type's default, whatever it held. -/
theorem SVal.defaultOf_prim' {p : PrimTy} (x : SVal (.prim p)) :
    x.defaultOf = .prim (PrimTy.dflt p) := by
  cases x; exact SVal.defaultOf_prim _

/-- A member of a struct reset is the member reset. -/
theorem SVal.find_defaultOf_field {s f : Name} {T U : Ty} (x : SVal (.ref (.struct s)))
    (h : lookupBy f (structDef s) = some T) (p : Path T U) :
    x.defaultOf.find (.field h p) = (((SVal.view x : SFields _).get h).defaultOf).find p := by
  cases x with
  | struct fs => rw [SVal.defaultOf_struct, SVal.find_field, SFields.get_defaultOf]; rfl

/-! ## A deployment's storage, and writes that cannot fail

A typed storage has every member of a struct and every key of a mapping:
a path through no array slot (`Path.total`) is always there, so a write or
a read along one returns, under the diamond as under the box, and the
deployment's storage (`Storage.init`, `mtSt`) reads the default there. -/

/-- A path through no array slot. -/
def Path.total : {T U : Ty} → Path T U → Bool
  | _, _, .nil => true
  | _, _, .field _ p => p.total
  | _, _, .key _ p => p.total
  | _, _, .at _ _ => false
  | _, _, .atF _ _ => false

theorem SVal.dflt_prim' (p : PrimTy) : SVal.dflt (.prim p) = .prim (PrimTy.dflt p) := rfl

theorem defaultForFields_map : (l : List (Name × Ty)) →
    Semantics.defaultForFields l = l.map fun (n, T) => (n, Semantics.defaultForTy T)
  | [] => by rw [Semantics.defaultForFields]; rfl
  | (n, T) :: l => by rw [Semantics.defaultForFields, defaultForFields_map l]; rfl

theorem SVal.dflt_struct' (s : Name) :
    SVal.dflt (.ref (.struct s)) = .struct (SFields.dflt (structDef s)) := by
  apply SVal.erase_injective
  rw [SVal.dflt_erase, SVal.erase_struct, SFields.dflt_erase, Semantics.defaultForTy,
    defaultForFields_map]

theorem SVal.dflt_map' (K V : Ty) :
    SVal.dflt (.ref (.mapping K V)) = .map .nil (SVal.dflt V) := by
  apply SVal.erase_injective
  rw [SVal.dflt_erase, SVal.erase_map, SVal.dflt_erase, Semantics.defaultForTy, SMap.erase_nil]

theorem SFields.get_dflt {f : Name} : {fs : List (Name × Ty)} → {T : Ty} →
    (h : lookupBy f fs = some T) → (SFields.dflt fs).get h = SVal.dflt T
  | [], _, h => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, T, h => by
    rw [SFields.dflt, SFields.get_cons]
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      simp only [e, dite_true]
    · simp only [e, dite_false]
      exact SFields.get_dflt _

theorem SVal.findM_dflt_total : {T U : Ty} → (p : Path T U) → p.total = true →
    (SVal.dflt T).findM p = some (SVal.dflt U)
  | _, _, .nil, _ => by cases h : SVal.dflt _ <;> rfl
  | _, _, @Path.field s _ _ _ hf p, hp => by
    rw [SVal.dflt_struct']
    simp only [SVal.findM, SFields.get_dflt]
    exact SVal.findM_dflt_total p hp
  | _, _, @Path.key K V _ k p, hp => by
    rw [SVal.dflt_map']
    simp only [SVal.findM, SMap.toList, SVal.findM]
    exact SVal.findM_dflt_total p hp
  | _, _, .at _ _, hp => by simp only [Path.total, Bool.false_eq_true] at hp
  | _, _, .atF _ _, hp => by simp only [Path.total, Bool.false_eq_true] at hp

theorem Storage.find_init_total {C : Contract} {U : Ty} (r : SRef C U) (h : r.path.total = true) :
    (Storage.init C).find r = some (SVal.dflt U) := by
  simp only [Storage.find, Storage.init, SFields.get_dflt, SVal.find_eq_findM]
  exact SVal.findM_dflt_total _ h

theorem SVal.saveM_total : {T U : Ty} → (x : SVal T) → (p : Path T U) → p.total = true →
    (v : SVal U) → x.saveM p v ≠ none
  | _, _, _, .nil, _, _ => by simp only [SVal.saveM, ne_eq, reduceCtorEq, not_false_eq_true]
  | _, _, .struct fs, .field hf p, hp, v => by
    obtain ⟨x', hx'⟩ := Option.ne_none_iff_exists'.1 (SVal.saveM_total (fs.get hf) p hp v)
    simp only [SVal.saveM, hx', Option.bind_eq_bind, Option.bind_some, ne_eq, reduceCtorEq,
      not_false_eq_true]
  | _, _, .map m d, .key k p, hp, v => by
    simp only [SVal.saveM]
    split
    · rename_i x _
      obtain ⟨x', hx'⟩ := Option.ne_none_iff_exists'.1 (SVal.saveM_total x p hp v)
      simp only [hx', Option.bind_eq_bind, Option.bind_some, ne_eq, reduceCtorEq,
        not_false_eq_true]
    · obtain ⟨x', hx'⟩ := Option.ne_none_iff_exists'.1 (SVal.saveM_total d p hp v)
      simp only [hx', Option.bind_eq_bind, Option.bind_some, ne_eq, reduceCtorEq,
        not_false_eq_true]
  | _, _, _, .at _ _, hp, _ => by simp only [Path.total, Bool.false_eq_true] at hp
  | _, _, _, .atF _ _, hp, _ => by simp only [Path.total, Bool.false_eq_true] at hp

theorem SVal.findM_total : {T U : Ty} → (x : SVal T) → (p : Path T U) → p.total = true →
    x.findM p ≠ none
  | _, _, _, .nil, _ => by simp only [SVal.findM, ne_eq, reduceCtorEq, not_false_eq_true]
  | _, _, .struct fs, .field hf p, hp => by
    simp only [SVal.findM]
    exact SVal.findM_total (fs.get hf) p hp
  | _, _, .map m d, .key k p, hp => by
    simp only [SVal.findM]
    split
    · exact SVal.findM_total _ p hp
    · exact SVal.findM_total d p hp
  | _, _, _, .at _ _, hp => by simp only [Path.total, Bool.false_eq_true] at hp
  | _, _, _, .atF _ _, hp => by simp only [Path.total, Bool.false_eq_true] at hp

theorem Storage.find_ne_none_total {C : Contract} {U : Ty} (st : Storage C) (r : SRef C U)
    (h : r.path.total = true) : st.find r ≠ none := by
  simp only [Storage.find, SVal.find_eq_findM]
  exact SVal.findM_total _ _ h

theorem Storage.save_ne_none_total {C : Contract} {U : Ty} (st : Storage C) (r : SRef C U)
    (h : r.path.total = true) (v : SVal U) : st.save r v ≠ none := by
  obtain ⟨x', hx'⟩ := Option.ne_none_iff_exists'.1
    (SVal.saveM_total (st.get r.hroot) r.path h v)
  simp only [Storage.save, SVal.save_eq_saveM, hx', Option.bind_eq_bind, Option.bind_some, ne_eq,
    reduceCtorEq, not_false_eq_true]

theorem Storage.write_ne_none_total {C : Contract} {U : Ty} (st : Storage C) (r : SRef C U)
    (h : r.path.total = true) (v : SVal U) : st.write r v ≠ none := by
  rw [Storage.write_eq_bind]
  unfold Storage.writeVal
  split
  · simp only [Option.bind_some]
    exact Storage.save_ne_none_total st r h v
  · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 (Storage.find_ne_none_total st r h)
    simp only [hc, Option.map_some, Option.bind_some]
    exact Storage.save_ne_none_total st r h _

theorem Storage.delete_ne_none_total {C : Contract} {U : Ty} (st : Storage C) (r : SRef C U)
    (h : r.path.total = true) : st.delete r ≠ none := by
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 (Storage.find_ne_none_total st r h)
  simp only [Storage.delete, hc, Option.bind_eq_bind, Option.bind_some]
  exact Storage.save_ne_none_total st r h _

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

namespace CloseS

variable {C : Contract}

/-! ## References in one normal form -/

theorem field_append {s f : Name} {T : Ty} (r : SRef C (.ref (.struct s)))
    (h : C.fieldType s f = some T) : r.field h = r.append (.field h .nil) := rfl
theorem index_append {R : RefTy} {k : PrimTy} {V : Ty} (r : SRef C (.ref R))
    (it : IndexTy R k V) (i : Int) : r.index it i = r.append (Path.index it i) := rfl
theorem append_append {T U W : Ty} (r : SRef C T) (p : Path T U) (q : Path U W) :
    (r.append p).append q = r.append (p.append q) := by
  simp only [SRef.append, Path.append_assoc]
theorem root_append {T U : Ty} (r : SRef C T) (p : Path T U) : (r.append p).root = r.root := rfl
theorem absT_ofRoot {T : Ty} (r : Name) (h : C.rootType r = some T) :
    (SRef.ofRoot r h).absT = [.field r] := rfl
theorem absT_append {T U : Ty} (r : SRef C T) (p : Path T U) :
    (r.append p).absT = r.absT ++ p.erase := by
  simp only [SRef.absT, SRef.append, Path.erase_append, Theory.rootPath, List.cons_append]
theorem diverges_nil_left (q : List Semantics.Seg) : diverges [] q = false := rfl
theorem diverges_nil_right (a : Semantics.Seg) (p : List Semantics.Seg) :
    diverges (a :: p) [] = false := rfl
/-- `diverges` as `sol_close` reads it, with the disequation both ways
round (as the untyped `Close.diverge_cons'`): a premise `k != j` then frames
`balances[k]` against `balances[j]` whichever of the two was written
first. -/
theorem diverges_cons (a b : Semantics.Seg) (p q : List Semantics.Seg) :
    diverges (a :: p) (b :: q) = true ↔ (¬ a = b ∨ ¬ b = a) ∨ diverges p q = true := by
  simp only [Theory.StValue.diverges]
  by_cases h : a = b
  · subst h; simp only [if_true, not_true_eq_false, or_self, false_or]
  · simp only [h, if_false, not_false_eq_true, true_or]
theorem key_uint (n : Int) (h : PrimTy.uint.inRange n = true) :
    PrimTy.key (p := .uint) ⟨n, h⟩ = n := rfl
theorem key_int (n : Int) (h : PrimTy.int.inRange n = true) :
    PrimTy.key (p := .int) ⟨n, h⟩ = n := rfl
theorem key_uint' (a : PrimTy.uint.Denote) : PrimTy.key a = a.val := rfl
theorem key_int' (a : PrimTy.int.Denote) : PrimTy.key a = a.val := rfl
theorem netOfT_def (l : List (Int × Int)) (n : PrimTy.uint.Denote) :
    Tm.netOfT l n = PrimTy.int.ofInt? ((Semantics.lookupBy n.1 l).getD 0) := rfl
/-- A mapping's slot at a root is always there. -/
theorem checkIndex_map_root {k : PrimTy} {V : Ty} (st : Storage C) (r : Name)
    (h : C.rootType r = some (Ty.ref (RefTy.mapping (.prim k) V))) (i : Int) :
    st.checkIndex (SRef.ofRoot r h) IndexTy.map i = some () := rfl
theorem dflt_bool : PrimTy.dflt .bool = (false : Bool) := rfl
theorem dflt_uint_val : (PrimTy.dflt .uint).val = 0 := rfl
theorem dflt_int_val : (PrimTy.dflt .int).val = 0 := rfl
theorem writeVal_prim {p : PrimTy} (st : Storage C) (r : SRef C (.prim p))
    (x : p.Denote) : st.writeVal r (.prim x) = some (.prim x) := rfl

theorem writeVal_ref {R : RefTy} (st : Storage C) (r : SRef C (.ref R)) (v : SVal (.ref R)) :
    st.writeVal r v = (st.find r).map fun cur => cur.overlay v := rfl
theorem find_ofRoot {T : Ty} (st : Storage C) (r : Name) (h : C.rootType r = some T) :
    st.find (SRef.ofRoot r h) = some (st.get h) := rfl

/-- A result named bare (`Modality.wp_box`) is the option's: two reads of
one reference then name one value. -/
theorem optRes_eq_ok {α : Type} (x : Option α) (a : α) : Close.optRes x = .ok a ↔ x = some a := by
  cases x <;> simp only [Close.optRes, reduceCtorEq, Except.ok.injEq, Option.some.injEq]

/-- A result that does not read what it binds: in `[ alice = bob; ]
alice.age == 7`, `alice.age` reads `7` wherever `alice` is found. -/
theorem bind_const_eq_some {α β : Type} (x : Option α) (y w : β) :
    (x.bind fun _ => some y) = some w ↔ y = w ∧ ∃ a, x = some a := by
  cases x <;> simp only [Option.bind_none, Option.bind_some, reduceCtorEq, Option.some.injEq,
    exists_false, and_false, exists_eq', and_true]

theorem map_const_eq_some {α β : Type} (x : Option α) (y w : β) :
    (x.map fun _ => y) = some w ↔ y = w ∧ ∃ a, x = some a := by
  cases x <;> simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq,
    exists_false, and_false, exists_eq', and_true]

/-- **A subtree read under the box** (the untyped `Modality.wp_box_findStorage`):
in `[ alice = bob; ] alice.age == bob.age`, the tree read at `bob` reads
below what the storage reads below `bob`.  A word read is named bare: the
fact would be an obligation where the read stands under a negation. -/
theorem wp_box_find {R : RefTy} {st : Storage C} {r : SRef C (.ref R)}
    {P : SVal (.ref R) → Prop} :
    Modality.box.wp (Close.optRes (st.find r)) P ↔
      ∀ w, st.find r = some w →
        (∀ {W : Ty} (p : Path (.ref R) W), w.find p = st.find (r.append p)) → P w := by
  cases h : st.find r with
  | none => simp only [Close.optRes, Modality.wp, Modality.onHalt, reduceCtorEq, false_implies,
      implies_true]
  | some w =>
    simp only [Close.optRes, Modality.wp, Option.some.injEq, forall_eq']
    refine ⟨fun hP _ => hP, fun hP => hP fun p => ?_⟩
    rw [Storage.find_append, h]
    rfl

/-! A word named by an equation read member-wise (`mk_eq_uint`): `∀ a,
⟨n, h⟩ = a → P a` reaches simp as `∀ a, n = a.val → P a`, which is `P` of
`⟨n, h⟩`. -/

theorem forall_val_eq_uint (n : Int) (P : PrimTy.uint.Denote → Prop) :
    (∀ a : PrimTy.uint.Denote, n = a.val → P a) ↔ ∀ h : PrimTy.uint.inRange n = true, P ⟨n, h⟩ :=
  ⟨fun H h => H ⟨n, h⟩ rfl, fun H ⟨_, hm⟩ e => by subst e; exact H hm⟩
theorem forall_val_eq_int (n : Int) (P : PrimTy.int.Denote → Prop) :
    (∀ a : PrimTy.int.Denote, n = a.val → P a) ↔ ∀ h : PrimTy.int.inRange n = true, P ⟨n, h⟩ :=
  ⟨fun H h => H ⟨n, h⟩ rfl, fun H ⟨_, hm⟩ e => by subst e; exact H hm⟩
theorem forall_val_ne_uint (n : Int) :
    (∀ a : PrimTy.uint.Denote, ¬ n = a.val) ↔ ¬ PrimTy.uint.inRange n = true :=
  ⟨fun H h => H ⟨n, h⟩ rfl, fun H ⟨_, hm⟩ e => by subst e; exact H hm⟩
theorem forall_val_ne_int (n : Int) :
    (∀ a : PrimTy.int.Denote, ¬ n = a.val) ↔ ¬ PrimTy.int.inRange n = true :=
  ⟨fun H h => H ⟨n, h⟩ rfl, fun H ⟨_, hm⟩ e => by subst e; exact H hm⟩
theorem exists_val_eq_uint (n : Int) :
    (∃ a : PrimTy.uint.Denote, n = a.val) ↔ PrimTy.uint.inRange n = true :=
  ⟨fun ⟨⟨_, hm⟩, e⟩ => e ▸ hm, fun h => ⟨⟨n, h⟩, rfl⟩⟩
theorem exists_val_eq_int (n : Int) :
    (∃ a : PrimTy.int.Denote, n = a.val) ↔ PrimTy.int.inRange n = true :=
  ⟨fun ⟨⟨_, hm⟩, e⟩ => e ▸ hm, fun h => ⟨⟨n, h⟩, rfl⟩⟩

/-! ## Memory under the box -/

theorem readT_prim {H : HTy} {p : PrimTy} (m : Grown H (fun _ => Unit)) (a : MAddrT (.prim p)) :
    m.readT a = m.readId a := by
  unfold Grown.readId
  cases m.readT a <;> rfl
theorem readT_ident {H : HTy} {R : RefTy} (m : Grown H (fun _ => Unit)) (a : MAddrT (.ref R)) :
    ((m.readT a).bind fun (r : HRef _ R) => some r.id) = m.readId a := by
  unfold Grown.readId
  cases m.readT a <;> rfl
theorem Landed.memT_readId {Δ : Ctx} {g : State C []} {ℓ : LocsV C Δ} (x : Landed g ℓ)
    {T : Ty} (a : MAddrT T) : x.val.glob.memT.readId a = g.memT.readId a := by
  have e := x.glob_eq
  generalize x.val.glob = y at e ⊢
  subst e
  rfl
theorem push_memT_readId {Γ : Ctx} {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) {T : Ty}
    (a : MAddrT T) : (σ.push v).glob.memT.readId a = σ.glob.memT.readId a := rfl
theorem withMem_memT_readId {H : HTy} (g : GlobT C H) (μ : Grown H (fun _ => Unit)) {T : Ty}
    (a : MAddrT T) : (g.withMem μ).1.memT.readId a = μ.readId a := rfl

/-- A member of a struct copied out of storage, read in the memory the
copy leaves: what the struct held there. -/
theorem readId_copySt_field {H : HTy} (m : Grown H (fun _ => Unit)) {s f : Name} {p : PrimTy}
    (w : SVal (.ref (.struct s))) (hT : (Ty.ref (.struct s)).mapFree = true)
    (hf : lookupBy f (structDef s) = some (.prim p)) (hl : ¬ f = "length") :
    (m.then (w.copyStToM m.heap hT)).readId (MAddrT.field (w.copyStToM m.heap hT).val.id hf) =
      (w.find (.field hf .nil)).map fun v => v.view := by
  show (((MAddrT.field (w.copyStToM m.heap hT).val.id hf).resolve
      (w.copyStToM m.heap hT).H').bind (w.copyStToM m.heap hT).heap.readAddr).map _ = _
  simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM, HRef.ofId?_self, Option.map_some,
    Option.bind_some]
  show some ((w.copyStToM m.heap hT).heap.field (w.copyStToM m.heap hT).val hf) = _
  rw [SVal.copyStToM_field m.heap w hT hf hl]
  rfl

/-- A member of a memory struct copied into storage, as the memory reads
it. -/
theorem copyMToSt_find_field {H : HTy} (g : Grown H (fun _ => Unit)) {s f : Name} {p : PrimTy}
    (a : HRef g.H' (.struct s)) (hf : lookupBy f (structDef s) = some (.prim p))
    (hl : ¬ f = "length") :
    (MVal.copyMToSt g.heap (T := .ref (.struct s)) a).find (.field hf .nil) =
      (g.readId (MAddrT.field a.id hf)).map SVal.prim := by
  rw [MVal.copyMToSt_field g.heap a hf hl]
  show _ = Option.map SVal.prim
    ((((MAddrT.field a.id hf).resolve g.H').bind g.heap.readAddr).map (MVal.toMvT g.H' _))
  simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM, HRef.ofId?_self, Option.map_some,
    Option.bind_some]
  rfl

/-- An identity read as an object of its type, under the box: the object
has that identity. -/
theorem wp_box_ofId {H : HTy} {R : RefTy} {id : Nat} {P : HRef H R → Prop} :
    Modality.box.wp (Close.optRes (HRef.ofId? H R id)) P ↔
      ∀ a : HRef H R, HRef.ofId? H R id = some a → a.id = id → P a := by
  cases h : HRef.ofId? H R id with
  | none => simp only [Close.optRes, Modality.wp, Modality.onHalt, reduceCtorEq, false_implies,
      implies_true]
  | some a =>
    simp only [Close.optRes, Modality.wp, Option.some.injEq, forall_eq']
    exact ⟨fun hP _ => hP, fun hP => hP (HRef.id_of_ofId? h)⟩

theorem withStorage_memT_readId {H : HTy} (g : GlobT C H) (st : Storage C) {T : Ty}
    (a : MAddrT T) : (g.withStorage st).1.memT.readId a = g.1.memT.readId a := rfl
theorem withNet_memT_readId {H : HTy} (g : GlobT C H) (nt : List (Int × Int)) {T : Ty}
    (a : MAddrT T) : (g.withNet nt).1.memT.readId a = g.1.memT.readId a := rfl
theorem withBalance_memT_readId {H : HTy} (g : GlobT C H) (b : PrimTy.uint.Denote) {T : Ty}
    (a : MAddrT T) : (g.withBalance b).1.memT.readId a = g.1.memT.readId a := rfl

/-- **A memory write under the box** (the untyped `Modality.wp_box_writeAddr`):
after `m.age = 5;` the memory reads `5` at `m.age`, and as before at every
address apart from it. -/
theorem wp_box_writeT {H : HTy} {T : Ty} {m : Grown H (fun _ => Unit)} {a : MAddrT T} {v : MvT T}
    {P : Grown H (fun _ => Unit) → Prop} :
    Modality.box.wp (Close.optRes (m.writeT a v)) P ↔
      ∀ m', m.writeT a v = some m' → m'.readId a = some v →
        (∀ {U : Ty} (b : MAddrT U), a.Apart b → m'.readId b = m.readId b) → P m' := by
  cases h : m.writeT a v with
  | none => simp only [Close.optRes, Modality.wp, Modality.onHalt, reduceCtorEq, false_implies,
      implies_true]
  | some m' =>
    simp only [Close.optRes, Modality.wp, Option.some.injEq, forall_eq']
    obtain ⟨h₁, h₂⟩ := Grown.writeT_facts h
    exact ⟨fun hP _ _ => hP, fun hP => hP h₁ h₂⟩

/-! ## A deployment's storage, and the diamond over a total path -/

theorem path_ofRoot {T : Ty} (r : Name) (h : C.rootType r = some T) :
    (SRef.ofRoot r h).path = .nil := rfl
theorem path_append {T U : Ty} (r : SRef C T) (p : Path T U) :
    (r.append p).path = r.path.append p := rfl
theorem find_init_ofRoot {T : Ty} (r : Name) (h : C.rootType r = some T) :
    (Storage.init C).find (SRef.ofRoot r h) = some (SVal.dflt T) :=
  Storage.find_init_total _ rfl
theorem find_init_append {T U : Ty} (r : Name) (h : C.rootType r = some T) (p : Path T U)
    (hp : p.total = true) : (Storage.init C).find ((SRef.ofRoot r h).append p) = some (SVal.dflt U) :=
  Storage.find_init_total _ (by simpa only [path_append, path_ofRoot, Path.append_nil] using hp)

theorem wp_diamond_of_ne_none {α : Type} {x : Option α} {P : α → Prop} (h : x ≠ none) :
    Modality.diamond.wp (Close.optRes x) P ↔ Modality.box.wp (Close.optRes x) P := by
  obtain ⟨a, rfl⟩ := Option.ne_none_iff_exists'.1 h
  exact Iff.rfl

/-- A write along a path through no array slot returns: the diamond is the
box there. -/
theorem wp_diamond_write_total {T : Ty} {st : Storage C} {r : SRef C T} {v : SVal T}
    {P : Storage C → Prop} (h : r.path.total = true) :
    Modality.diamond.wp (Close.optRes (st.write r v)) P ↔
      Modality.box.wp (Close.optRes (st.write r v)) P :=
  wp_diamond_of_ne_none (Storage.write_ne_none_total st r h v)
theorem wp_diamond_delete_total {T : Ty} {st : Storage C} {r : SRef C T} {P : Storage C → Prop}
    (h : r.path.total = true) :
    Modality.diamond.wp (Close.optRes (st.delete r)) P ↔
      Modality.box.wp (Close.optRes (st.delete r)) P :=
  wp_diamond_of_ne_none (Storage.delete_ne_none_total st r h)
/-- A read along a path through no array slot returns, under either
modality: it is named by the value it returns (`Option.get`), so two reads
of one reference are one term. -/
theorem wp_find_total {m : Modality} {T : Ty} {st : Storage C} {r : SRef C T}
    {P : SVal T → Prop} (h : r.path.total = true) :
    m.wp (Close.optRes (st.find r)) P ↔
      P ((st.find r).get (Option.isSome_iff_ne_none.mpr (Storage.find_ne_none_total st r h))) := by
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 (Storage.find_ne_none_total st r h)
  simp only [ha, Option.get_some]
  exact Iff.rfl

/-- What a read returns, read below. -/
theorem get_find_find {T U : Ty} (st : Storage C) (r : SRef C T) (h : (st.find r).isSome)
    (p : Path T U) : ((st.find r).get h).find p = st.find (r.append p) := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 h
  simp only [ha, Option.get_some, Storage.find_append, Option.bind_some]

/-! ## A write under the box -/

/-- **A storage write under the box**, named with what is known of the
storage it returns: at the reference written and below it, what was saved
there (`Storage.writeVal`); as before where the reference parts from it, its
length and index checks as before where they part from the array's length. -/
theorem wp_box_write {T : Ty} {st : Storage C} {r : SRef C T} {v : SVal T}
    {P : Storage C → Prop} :
    Modality.box.wp (Close.optRes (st.write r v)) P ↔
      ∀ st', st.write r v = some st' →
        st'.find r = st.writeVal r v →
        (∀ {W : Ty} (p : Path T W), st'.find (r.append p) = (st.writeVal r v).bind (·.find p)) →
        (∀ {W : Ty} (q : SRef C W), diverges r.absT q.absT = true → st'.find q = st.find q) →
        (∀ {E : Ty} (q : SRef C (.ref (.array E))),
          diverges r.absT (q.absT ++ [lengthSeg]) = true → st'.len q = st.len q) →
        (∀ {R : RefTy} {k : PrimTy} {V : Ty} (q : SRef C (.ref R)) (it : IndexTy R k V) (i : Int),
          diverges r.absT (q.absT ++ [lengthSeg]) = true →
            st'.checkIndex q it i = st.checkIndex q it i) →
        P st' := by
  cases h : st.write r v with
  | none => simp only [Close.optRes, Modality.wp, Modality.onHalt, reduceCtorEq, false_implies,
      implies_true]
  | some st' =>
    simp only [Close.optRes, Modality.wp, Option.some.injEq, forall_eq']
    refine ⟨fun hP _ _ _ _ _ => hP, fun hP => ?_⟩
    rw [Storage.write_eq_bind] at h
    obtain ⟨w, hw, hs⟩ := Option.bind_eq_some_iff.1 h
    have hf : st'.find r = some w := Storage.find_save_same hs
    refine hP (hf.trans hw.symm) (fun p => ?_) (fun q hd => Storage.find_save_frame hd hs)
      (fun q hd => Storage.len_save_frame hd hs)
      (fun q it i hd => Storage.checkIndex_save_frame it i hd hs)
    rw [Storage.find_append, hf, hw]

/-- **A storage delete under the box**: at the reference deleted and below
it, the value there reset (`SVal.defaultOf`); the frame as for a write. -/
theorem wp_box_delete {T : Ty} {st : Storage C} {r : SRef C T} {P : Storage C → Prop} :
    Modality.box.wp (Close.optRes (st.delete r)) P ↔
      ∀ st', st.delete r = some st' →
        st'.find r = (st.find r).map (fun x => x.defaultOf) →
        (∀ {W : Ty} (p : Path T W), st'.find (r.append p) =
          (st.find r).bind fun x => x.defaultOf.find p) →
        (∀ {W : Ty} (q : SRef C W), diverges r.absT q.absT = true → st'.find q = st.find q) →
        (∀ {E : Ty} (q : SRef C (.ref (.array E))),
          diverges r.absT (q.absT ++ [lengthSeg]) = true → st'.len q = st.len q) →
        (∀ {R : RefTy} {k : PrimTy} {V : Ty} (q : SRef C (.ref R)) (it : IndexTy R k V) (i : Int),
          diverges r.absT (q.absT ++ [lengthSeg]) = true →
            st'.checkIndex q it i = st.checkIndex q it i) →
        P st' := by
  cases h : st.delete r with
  | none => simp only [Close.optRes, Modality.wp, Modality.onHalt, reduceCtorEq, false_implies,
      implies_true]
  | some st' =>
    simp only [Close.optRes, Modality.wp, Option.some.injEq, forall_eq']
    refine ⟨fun hP _ _ _ _ _ => hP, fun hP => ?_⟩
    obtain ⟨x, hx, hs⟩ := Storage.delete_save h
    have hf : st'.find r = some x.defaultOf := Storage.find_save_same hs
    refine hP (by rw [hf, hx]; rfl) (fun p => ?_) (fun q hd => Storage.find_save_frame hd hs)
      (fun q hd => Storage.len_save_frame hd hs)
      (fun q it i hd => Storage.checkIndex_save_frame it i hd hs)
    rw [Storage.find_append, hf, hx]
    rfl

/-- The same for a word: it reads back at the reference written. -/
theorem wp_box_write_prim {p : PrimTy} {st : Storage C} {r : SRef C (.prim p)} {x : p.Denote}
    {P : Storage C → Prop} :
    Modality.box.wp (Close.optRes (st.write r (.prim x))) P ↔
      ∀ st', st.write r (.prim x) = some st' → st'.find r = some (.prim x) →
        (∀ {W : Ty} (q : SRef C W), diverges r.absT q.absT = true → st'.find q = st.find q) →
        (∀ {E : Ty} (q : SRef C (.ref (.array E))),
          diverges r.absT (q.absT ++ [lengthSeg]) = true → st'.len q = st.len q) →
        (∀ {R : RefTy} {k : PrimTy} {V : Ty} (q : SRef C (.ref R)) (it : IndexTy R k V) (i : Int),
          diverges r.absT (q.absT ++ [lengthSeg]) = true →
            st'.checkIndex q it i = st.checkIndex q it i) →
        P st' := by
  rw [wp_box_write]
  refine ⟨fun hP st' h hf hq hl hc => hP st' h hf (fun _ => ?_) hq hl hc,
    fun hP st' h hf _ hq hl hc => hP st' h hf hq hl hc⟩
  rw [Storage.find_append, hf]
  rfl

end CloseS

attribute [close_rw_s high] CloseS.wp_box_write_prim CloseS.wp_diamond_write_total
  CloseS.wp_diamond_delete_total CloseS.wp_find_total

attribute [close_rw_s]
  CloseS.wp_box_write CloseS.field_append CloseS.index_append CloseS.append_append
  CloseS.root_append CloseS.absT_ofRoot CloseS.absT_append CloseS.diverges_nil_left
  CloseS.diverges_nil_right CloseS.diverges_cons CloseS.key_uint CloseS.key_int
  CloseS.key_uint' CloseS.key_int' CloseS.netOfT_def
  CloseS.checkIndex_map_root CloseS.writeVal_prim CloseS.writeVal_ref
  CloseS.readT_prim CloseS.readT_ident CloseS.Landed.memT_readId CloseS.push_memT_readId
  CloseS.withMem_memT_readId CloseS.wp_box_writeT MAddrT.Apart CloseS.readId_copySt_field
  CloseS.copyMToSt_find_field CloseS.wp_box_ofId CloseS.withStorage_memT_readId
  CloseS.withNet_memT_readId CloseS.withBalance_memT_readId
  CloseS.get_find_find Option.get_some CloseS.path_ofRoot CloseS.path_append CloseS.find_init_ofRoot CloseS.find_init_append
  Path.total SVal.dflt_prim' Semantics.lookupBy Option.getD_some Option.getD_none
  CloseS.wp_box_delete CloseS.map_const_eq_some SVal.defaultOf_prim' SVal.find_defaultOf_field
  Option.map_map CloseS.dflt_bool CloseS.dflt_uint_val CloseS.dflt_int_val
  CloseS.bind_const_eq_some CloseS.optRes_eq_ok CloseS.forall_val_eq_uint CloseS.forall_val_eq_int
  CloseS.forall_val_ne_uint CloseS.forall_val_ne_int CloseS.exists_val_eq_uint
  CloseS.exists_val_eq_int
  CloseS.wp_box_find SVal.find_overlay_field SVal.overlay_prim' SVal.find_nil Function.comp_def
  Path.index_map Path.index_dyn Path.index_fixed Path.append_nil Path.append_field Path.append_at
  Path.append_atF Path.append_key Path.erase Semantics.Seg.field.injEq Semantics.Seg.at.injEq
  List.cons_append List.nil_append

end Solidity
