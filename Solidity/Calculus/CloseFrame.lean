import Solidity.Calculus.CloseScoped
import Solidity.Calculus.TermLaws

/-!
# `sol_close`'s storage frame, typed

A storage write under the box, named on the spot with what the typed laws
say of the storage it returns (`Calculus/TermLaws.lean`'s frame section):
`findOnSave` at the path written and below it, and `findOnSaveFrame`,
`lenOnSaveFrame` where the paths part (solkey's `selectOnSaveCons`, its
`\then` and its `\else`), the parting read
as the Theory's `diverges` on the references' segments (`SRef.segs`), which
the closer computes, a symbolic key by a hypothesis `k != j` of the formula
or a branch.  An index check (`Storage.checkIndex`) is framed as an array's
length is: it reads the length only (or nothing, for a mapping).

The references are read in one normal form, a root followed by a path
(`SRef.append`), so that a fact about the reads below a write meets a read
written member by member.
-/

namespace Solidity

open Theory (diverges lengthSeg)
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
length: elsewhere, or below one of its slots (`lenOnSaveFrame`, which the
check reads). -/
theorem checkIndex_save_frame {k : PrimTy} {V : Ty} {T : Ty} {R' : RefTy}
    {st st' : Storage C} {r : SRef C T} {v : SVal T} {q : SRef C (.ref R')}
    (it : IndexTy R' k V) (i : Int)
    (hd : diverges r.segs (q.segs ++ [lengthSeg]) = true) (h : st.save r v = some st') :
    st'.checkIndex q it i = st.checkIndex q it i := by
  rcases diverges_append_single hd with hd | ⟨rest, hne, he⟩
  · simp only [Storage.checkIndex, find_save_frame hd h]
  · obtain ⟨x', hs, rfl⟩ := save_some h
    rcases r with ⟨n, hr, p⟩
    rcases q with ⟨n', hq, p'⟩
    simp only [SRef.segs, List.cons_append, List.cons.injEq,
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

/-! ## A delete, member by member -/

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

theorem SVal.dflt_struct' (s : Name) :
    SVal.dflt (.ref (.struct s)) = .struct (SFields.dflt (structDef s)) :=
  SVal.dflt_struct_eq s

theorem SVal.dflt_map' (K V : Ty) :
    SVal.dflt (.ref (.mapping K V)) = .map .nil (SVal.dflt V) :=
  SVal.dflt_map_eq K V

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
theorem segs_ofRoot {T : Ty} (r : Name) (h : C.rootType r = some T) :
    (SRef.ofRoot r h).segs = [.field r] := rfl
theorem segs_append {T U : Ty} (r : SRef C T) (p : Path T U) :
    (r.append p).segs = r.segs ++ p.erase := by
  simp only [SRef.segs, SRef.append, Path.erase_append, List.cons_append]
theorem diverges_nil_left (q : List Semantics.Seg) : diverges [] q = false := rfl
theorem diverges_nil_right (a : Semantics.Seg) (p : List Semantics.Seg) :
    diverges (a :: p) [] = false := rfl
/-- `diverges` as `sol_close` reads it, with the disequation both ways
round (as the untyped `Close.diverge_cons'`): a premise `k != j` then frames
`balances[k]` against `balances[j]` whichever of the two was written
first. -/
theorem diverges_cons (a b : Semantics.Seg) (p q : List Semantics.Seg) :
    diverges (a :: p) (b :: q) = true ↔ (¬ a = b ∨ ¬ b = a) ∨ diverges p q = true := by
  simp only [Theory.diverges]
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
    Tm.netOfT l n = some ((Semantics.lookupBy n.1 l).getD 0) := rfl
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

/-- **A subtree read under the box**:
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
    (hf : lookupBy f (structDef s) = some (.prim p)) :
    (m.then (w.copyStToM m.heap hT)).readId (MAddrT.field (w.copyStToM m.heap hT).val.id hf) =
      (w.find (.field hf .nil)).map fun v => v.view := by
  show (((MAddrT.field (w.copyStToM m.heap hT).val.id hf).resolve
      (w.copyStToM m.heap hT).H').bind (w.copyStToM m.heap hT).heap.readAddr).map _ = _
  simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM, HRef.ofId?_self, Option.map_some,
    Option.bind_some]
  show some ((w.copyStToM m.heap hT).heap.field (w.copyStToM m.heap hT).val hf) = _
  rw [SVal.copyStToM_field m.heap w hT hf]
  rfl

/-- A member of a memory struct copied into storage, as the memory reads
it. -/
theorem copyMToSt_find_field {H : HTy} (g : Grown H (fun _ => Unit)) {s f : Name} {p : PrimTy}
    (a : HRef g.H' (.struct s)) (hf : lookupBy f (structDef s) = some (.prim p)) :
    (MVal.copyMToSt g.heap (T := .ref (.struct s)) a).find (.field hf .nil) =
      (g.readId (MAddrT.field a.id hf)).map SVal.prim := by
  rw [MVal.copyMToSt_field g.heap a hf]
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

/-- **A memory write under the box**:
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

theorem total_ofRoot_append {T U : Ty} (r : Name) (h : C.rootType r = some T) (p : Path T U)
    (hp : p.total = true) : ((SRef.ofRoot r h).append p).path.total = true := by
  simpa only [path_append, path_ofRoot, Path.append_nil] using hp

/-! A reference in the closer's normal form is a root, or a root followed by
a path: the lemmas below take the two, so that the side condition is the
path's own `Path.total`, which `simp` decides. -/

/-- A write along a path through no array slot returns: the diamond is the
box there. -/
theorem wp_diamond_write_root {T : Ty} {st : Storage C} {r : Name} {h : C.rootType r = some T}
    {v : SVal T} {P : Storage C → Prop} :
    Modality.diamond.wp (Close.optRes (st.write (SRef.ofRoot r h) v)) P ↔
      Modality.box.wp (Close.optRes (st.write (SRef.ofRoot r h) v)) P :=
  wp_diamond_of_ne_none (Storage.write_ne_none_total st _ rfl v)
theorem wp_diamond_write_total {T U : Ty} {st : Storage C} {r : Name} {h : C.rootType r = some T}
    {p : Path T U} {v : SVal U} {P : Storage C → Prop} (hp : p.total = true) :
    Modality.diamond.wp (Close.optRes (st.write ((SRef.ofRoot r h).append p) v)) P ↔
      Modality.box.wp (Close.optRes (st.write ((SRef.ofRoot r h).append p) v)) P :=
  wp_diamond_of_ne_none (Storage.write_ne_none_total st _ (total_ofRoot_append r h p hp) v)
theorem wp_diamond_delete_root {T : Ty} {st : Storage C} {r : Name} {h : C.rootType r = some T}
    {P : Storage C → Prop} :
    Modality.diamond.wp (Close.optRes (st.delete (SRef.ofRoot r h))) P ↔
      Modality.box.wp (Close.optRes (st.delete (SRef.ofRoot r h))) P :=
  wp_diamond_of_ne_none (Storage.delete_ne_none_total st _ rfl)
theorem wp_diamond_delete_total {T U : Ty} {st : Storage C} {r : Name} {h : C.rootType r = some T}
    {p : Path T U} {P : Storage C → Prop} (hp : p.total = true) :
    Modality.diamond.wp (Close.optRes (st.delete ((SRef.ofRoot r h).append p))) P ↔
      Modality.box.wp (Close.optRes (st.delete ((SRef.ofRoot r h).append p))) P :=
  wp_diamond_of_ne_none (Storage.delete_ne_none_total st _ (total_ofRoot_append r h p hp))

/-- A read along a path through no array slot returns, under either
modality: it is named by the value it returns (`Option.getD`, at the type's
default, which it never takes), so two reads of one reference are one term,
and a fact about the reference rewrites it. -/
theorem wp_find_of_total {m : Modality} {T : Ty} {st : Storage C} {r : SRef C T}
    {P : SVal T → Prop} (h : r.path.total = true) :
    m.wp (Close.optRes (st.find r)) P ↔ P ((st.find r).getD (SVal.dflt T)) := by
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 (Storage.find_ne_none_total st r h)
  simp only [ha, Option.getD_some]
  exact Iff.rfl
theorem wp_find_root {m : Modality} {T : Ty} {st : Storage C} {r : Name}
    {h : C.rootType r = some T} {P : SVal T → Prop} :
    m.wp (Close.optRes (st.find (SRef.ofRoot r h))) P ↔
      P ((st.find (SRef.ofRoot r h)).getD (SVal.dflt T)) :=
  wp_find_of_total rfl
theorem wp_find_total {m : Modality} {T U : Ty} {st : Storage C} {r : Name}
    {h : C.rootType r = some T} {p : Path T U} {P : SVal U → Prop} (hp : p.total = true) :
    m.wp (Close.optRes (st.find ((SRef.ofRoot r h).append p))) P ↔
      P ((st.find ((SRef.ofRoot r h).append p)).getD (SVal.dflt U)) :=
  wp_find_of_total (total_ofRoot_append r h p hp)

/-- A result that does not read what a total read returns: the read returns. -/
theorem find_root_bind_const {α : Type} {T : Ty} (st : Storage C) (r : Name)
    (h : C.rootType r = some T) (y : Option α) :
    (st.find (SRef.ofRoot r h)).bind (fun _ => y) = y := by
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 (Storage.find_ne_none_total st (SRef.ofRoot r h) rfl)
  rw [ha, Option.bind_some]
theorem find_total_bind_const {α : Type} {T U : Ty} (st : Storage C) (r : Name)
    (h : C.rootType r = some T) (p : Path T U) (hp : p.total = true) (y : Option α) :
    (st.find ((SRef.ofRoot r h).append p)).bind (fun _ => y) = y := by
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1
    (Storage.find_ne_none_total st _ (total_ofRoot_append r h p hp))
  rw [ha, Option.bind_some]

theorem find_root_map_const {α : Type} {T : Ty} (st : Storage C) (r : Name)
    (h : C.rootType r = some T) (y : α) :
    (st.find (SRef.ofRoot r h)).map (fun _ => y) = some y := by
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 (Storage.find_ne_none_total st (SRef.ofRoot r h) rfl)
  rw [ha, Option.map_some]
theorem find_total_map_const {α : Type} {T U : Ty} (st : Storage C) (r : Name)
    (h : C.rootType r = some T) (p : Path T U) (hp : p.total = true) (y : α) :
    (st.find ((SRef.ofRoot r h).append p)).map (fun _ => y) = some y := by
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1
    (Storage.find_ne_none_total st _ (total_ofRoot_append r h p hp))
  rw [ha, Option.map_some]
/-- A mapping's key along a total path is always a slot. -/
theorem checkIndex_map_total {k : PrimTy} {V T : Ty} (st : Storage C) (r : Name)
    (h : C.rootType r = some T) (p : Path T (.ref (.mapping (.prim k) V))) (hp : p.total = true)
    (i : Int) : st.checkIndex ((SRef.ofRoot r h).append p) IndexTy.map i = some () := by
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1
    (Storage.find_ne_none_total st _ (total_ofRoot_append r h p hp))
  simp only [Storage.checkIndex, ha, Option.bind_eq_bind, Option.bind_some]
  rfl

/-- What a read along a total path returns, read below. -/
theorem getD_find_find {T U : Ty} (st : Storage C) (r : SRef C T) (h : r.path.total = true)
    (p : Path T U) : ((st.find r).getD (SVal.dflt T)).find p = st.find (r.append p) := by
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 (Storage.find_ne_none_total st r h)
  simp only [ha, Option.getD_some, Storage.find_append, Option.bind_some]
theorem getD_find_root {T U : Ty} (st : Storage C) (r : Name) (h : C.rootType r = some T)
    (p : Path T U) : ((st.find (SRef.ofRoot r h)).getD (SVal.dflt T)).find p =
      st.find ((SRef.ofRoot r h).append p) :=
  getD_find_find st _ rfl p
theorem getD_find_append {T U W : Ty} (st : Storage C) (r : Name) (h : C.rootType r = some T)
    (q : Path T U) (hq : q.total = true) (p : Path U W) :
    ((st.find ((SRef.ofRoot r h).append q)).getD (SVal.dflt U)).find p =
      st.find (((SRef.ofRoot r h).append q).append p) :=
  getD_find_find st _ (total_ofRoot_append r h q hq) p

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
        (∀ {W : Ty} (q : SRef C W), diverges r.segs q.segs = true → st'.find q = st.find q) →
        (∀ {E : Ty} (q : SRef C (.ref (.array E))),
          diverges r.segs (q.segs ++ [lengthSeg]) = true → st'.len q = st.len q) →
        (∀ {R : RefTy} {k : PrimTy} {V : Ty} (q : SRef C (.ref R)) (it : IndexTy R k V) (i : Int),
          diverges r.segs (q.segs ++ [lengthSeg]) = true →
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
        (∀ {W : Ty} (q : SRef C W), diverges r.segs q.segs = true → st'.find q = st.find q) →
        (∀ {E : Ty} (q : SRef C (.ref (.array E))),
          diverges r.segs (q.segs ++ [lengthSeg]) = true → st'.len q = st.len q) →
        (∀ {R : RefTy} {k : PrimTy} {V : Ty} (q : SRef C (.ref R)) (it : IndexTy R k V) (i : Int),
          diverges r.segs (q.segs ++ [lengthSeg]) = true →
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
        (∀ {W : Ty} (q : SRef C W), diverges r.segs q.segs = true → st'.find q = st.find q) →
        (∀ {E : Ty} (q : SRef C (.ref (.array E))),
          diverges r.segs (q.segs ++ [lengthSeg]) = true → st'.len q = st.len q) →
        (∀ {R : RefTy} {k : PrimTy} {V : Ty} (q : SRef C (.ref R)) (it : IndexTy R k V) (i : Int),
          diverges r.segs (q.segs ++ [lengthSeg]) = true →
            st'.checkIndex q it i = st.checkIndex q it i) →
        P st' := by
  rw [wp_box_write]
  refine ⟨fun hP st' h hf hq hl hc => hP st' h hf (fun _ => ?_) hq hl hc,
    fun hP st' h hf _ hq hl hc => hP st' h hf hq hl hc⟩
  rw [Storage.find_append, hf]
  rfl

end CloseS

attribute [close_rw_s high] CloseS.wp_box_write_prim CloseS.wp_diamond_write_total
  CloseS.wp_diamond_write_root CloseS.wp_diamond_delete_total CloseS.wp_diamond_delete_root
  CloseS.wp_find_total CloseS.wp_find_root

attribute [close_rw_s]
  CloseS.wp_box_write CloseS.field_append CloseS.index_append CloseS.append_append
  CloseS.root_append CloseS.segs_ofRoot CloseS.segs_append CloseS.diverges_nil_left
  CloseS.diverges_nil_right CloseS.diverges_cons CloseS.key_uint CloseS.key_int
  CloseS.key_uint' CloseS.key_int' CloseS.netOfT_def
  CloseS.checkIndex_map_root CloseS.writeVal_prim CloseS.writeVal_ref
  CloseS.readT_prim CloseS.readT_ident CloseS.Landed.memT_readId CloseS.push_memT_readId
  CloseS.withMem_memT_readId CloseS.wp_box_writeT MAddrT.Apart CloseS.readId_copySt_field
  CloseS.copyMToSt_find_field CloseS.wp_box_ofId CloseS.withStorage_memT_readId
  CloseS.withNet_memT_readId CloseS.withBalance_memT_readId
  CloseS.getD_find_root CloseS.getD_find_append CloseS.find_root_bind_const
  CloseS.find_total_bind_const CloseS.find_root_map_const CloseS.find_total_map_const
  CloseS.checkIndex_map_total CloseS.path_ofRoot CloseS.path_append CloseS.find_init_ofRoot CloseS.find_init_append
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
