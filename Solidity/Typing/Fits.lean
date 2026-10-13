import Solidity.Typing.Constructibility
import Solidity.Semantics.RunFrame
import Solidity.Semantics.TypedErase

/-!
# Reachable storage fits (decision 77, its conditional form)

`Typing/Constructibility.lean` characterises the reachable storages among
those that fit (`FitsStorage`: every word, mapping key and array slot in
range, what a literal can write), and `huge_reachable_not_fits` shows that a
contract whose fixed-size array is past `2^256` elements reaches a storage
that does not fit.  This module proves the converse under solc's own bound:
for a contract whose fixed sizes are all at most `2^256` (`FixedFits`, what
solc's "type too large for storage" implies), **every reachable storage
fits** (`reachable_fits`), so `reachable_iff_fits` drops the premise.

Three of the four facts `fits` asks are the typed state's by construction: a
word is a `PrimTy.Denote`, in range; a fixed-size array has exactly its
type's length; a dynamic array fewer than `2^256` live elements
(`SVal.array`'s bound).  The fourth is not, and is a third run invariant
beside `canonInv` and `tightInv` (`fitsInv`, of the typed state's erasure,
as `Typing/TypedRunInv.lean` reads them): every mapping key is in its key
type's range (`SMap`'s keys are `Int`s; a key is written through
`PrimTy.key` of a typed index, or along an alias's path, which the locals
part of the invariant keeps, `LTy.KeysFit`), and every dynamic array's live
and recycled slots together are fewer than `2^256` (`SVal.bnd`): `push`
takes a recycled slot or checks the bound (`Storage.full`), `pop` and
`delete` move slots, never add one, and a copy keeps the larger of the old
slot count and the new length.

The leaves read the typed step (`TRun.*`), through the storage erasure
lemmas (`Semantics/StorageErase.lean`) where storage changes: the typed
reference carries the keys' range and the path's type, the typed `push` its
bound.
-/

namespace Solidity

open Semantics
open SemanticsProperties (lookupBy_eq_some_mem lookupBy_setBy_self lookupBy_setBy_ne)

variable {C : Contract}

/-! ## Bounded values -/

/-- A mapping key that fits its key type: a word key in its range (a `bool`
key `0` or `1`); a reference key is never indexed (`KeysOK`). -/
def Ty.keyOk : Ty → Int → Prop
  | .prim p, k => p.keyFits k = true
  | .ref _, _ => True

/-- What every reachable value satisfies beyond its type: a dynamic array's
live and recycled slots together fewer than `2^256`, and every mapping key
in its key type's range.  A value of another shape than its type is not
bounded, so the predicate carries the shape `find` and `save` need. -/
def Semantics.SVal.bnd : Semantics.SVal → Ty → Prop
  | .prim _, .prim _ => True
  | .struct fields, .ref (.struct s) => bndFields s fields
  | .array elems shadow _, .ref (.array E) =>
      elems.length + shadow.length < 2 ^ 256 ∧ bndElems E elems ∧ bndElems E shadow
  | .array elems shadow _, .ref (.fixed E _) => bndElems E elems ∧ bndElems E shadow
  | .map entries dflt, .ref (.mapping K V) => bndEntries K V entries ∧ dflt.bnd V
  | _, _ => False
where
  bndFields (s : Name) : List (Name × Semantics.SVal) → Prop
    | [] => True
    | (n, v) :: rest =>
        (match lookupBy n (structDef s) with
         | some T => v.bnd T
         | none => True) ∧ bndFields s rest
  bndElems (E : Ty) : List Semantics.SVal → Prop
    | [] => True
    | v :: rest => v.bnd E ∧ bndElems E rest
  bndEntries (K V : Ty) : List (Int × Semantics.SVal) → Prop
    | [] => True
    | (k, v) :: rest => K.keyOk k ∧ v.bnd V ∧ bndEntries K V rest

open Semantics.SVal.bnd (bndFields bndElems bndEntries)

/-- Every root bounded at its declared type. -/
def BndStorage (C : Contract) (st : List (Name × Semantics.SVal)) : Prop :=
  ∀ r T v, lookupBy r C.vars = some T → lookupBy r st = some v → v.bnd T

/-- One segment's key in range: an index into a mapping keyed by a word. -/
def SegFits : Ty → Seg → Prop
  | .ref (.mapping K _), .at k => K.keyOk k
  | _, _ => True

/-- Every key along a path from a value of type `T` in range. -/
def KeysFit : Ty → List Seg → Prop
  | _, [] => True
  | T, seg :: rest => SegFits T seg ∧
      (match segTy T seg with
       | some T' => KeysFit T' rest
       | none => True)

/-- Every fixed-size array type a path reaches from `T` has at most `2^256`
elements. -/
def FixedFitsAt (T : Ty) : Prop :=
  ∀ segs E n, tyAtSegs T segs = some (.ref (.fixed E n)) → n ≤ 2 ^ 256

/-- **The contract's fixed sizes fit**: every fixed-size array type in its
storage layout has at most `2^256` elements, which solc's "type too large
for storage" check implies (`Huge` is refused). -/
def FixedFits (C : Contract) : Prop :=
  ∀ r T, lookupBy r C.vars = some T → FixedFitsAt T

/-! ### Lists -/

theorem bndElems_iff {E : Ty} : ∀ {l : List Semantics.SVal}, bndElems E l ↔ ∀ v ∈ l, v.bnd E
  | [] => by simp only [bndElems, List.not_mem_nil, false_implies, implies_true]
  | v :: rest => by simp only [bndElems, bndElems_iff (l := rest), List.mem_cons,
                        forall_eq_or_imp]

theorem bndEntries_iff {K V : Ty} :
    ∀ {l : List (Int × Semantics.SVal)}, bndEntries K V l ↔ ∀ kv ∈ l, K.keyOk kv.1 ∧ kv.2.bnd V
  | [] => by simp only [bndEntries, List.not_mem_nil, false_implies, implies_true]
  | (k, v) :: rest => by simp only [bndEntries, bndEntries_iff (l := rest), Prod.forall,
                             List.mem_cons, forall_eq_or_imp, and_assoc]

theorem bndElems_append {E : Ty} {l l' : List Semantics.SVal} (h : bndElems E l)
    (h' : bndElems E l') : bndElems E (l ++ l') :=
  bndElems_iff.mpr fun v hv => (List.mem_append.mp hv).elim (bndElems_iff.mp h v)
    (bndElems_iff.mp h' v)

theorem bndElems_drop {E : Ty} {l : List Semantics.SVal} (n : Nat) (h : bndElems E l) :
    bndElems E (l.drop n) :=
  bndElems_iff.mpr fun v hv => bndElems_iff.mp h v (List.mem_of_mem_drop hv)

theorem bndFields_lookup {s : Name} {fields : List (Name × Semantics.SVal)} {n : Name}
    {v : Semantics.SVal} {T : Ty} (h : bndFields s fields) (hl : lookupBy n fields = some v)
    (hT : lookupBy n (structDef s) = some T) : v.bnd T := by
  induction fields with
  | nil => simp only [lookupBy, reduceCtorEq] at hl
  | cons p rest ih =>
    obtain ⟨n', v'⟩ := p
    simp only [bndFields] at h
    by_cases hn : n = n'
    · subst hn
      simp only [lookupBy, ↓reduceIte, Option.some.injEq] at hl; subst hl
      simpa only [hT] using h.1
    · simp only [lookupBy, hn, ↓reduceIte] at hl
      exact ih h.2 hl

theorem bndFields_setBy {s : Name} {fields : List (Name × Semantics.SVal)} {n : Name}
    {w : Semantics.SVal} {T : Ty} (h : bndFields s fields) (hd : lookupBy n (structDef s) = some T)
    (hw : w.bnd T) : bndFields s (setBy n w fields) := by
  induction fields with
  | nil => simp only [setBy, bndFields, hd, hw, and_self]
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    simp only [bndFields] at h
    by_cases hn : n = k
    · subst hn; simp only [setBy, ↓reduceIte, bndFields, hd, hw, h.2, and_self]
    · simp only [setBy, if_neg hn, bndFields]; exact ⟨h.1, ih h.2⟩

theorem bndEntries_setBy {K V : Ty} {entries : List (Int × Semantics.SVal)} {i : Int}
    {w : Semantics.SVal} (h : bndEntries K V entries) (hi : K.keyOk i) (hw : w.bnd V) :
    bndEntries K V (setBy i w entries) := by
  induction entries with
  | nil => simp only [setBy, bndEntries, hi, hw, and_self]
  | cons p rest ih =>
    obtain ⟨j, v⟩ := p
    by_cases hij : i = j
    · subst hij; simp only [setBy, ↓reduceIte, bndEntries, hi, hw, h.2.2, and_self]
    · simp only [setBy, if_neg hij, bndEntries]; exact ⟨h.1, h.2.1, ih h.2.2⟩

theorem bndEntries_lookup {K V : Ty} {entries : List (Int × Semantics.SVal)} {i : Int}
    {v : Semantics.SVal} (h : bndEntries K V entries) (hl : lookupBy i entries = some v) :
    v.bnd V :=
  (bndEntries_iff.mp h (i, v) (lookupBy_eq_some_mem hl)).2

/-! ### Defaults, reads, writes -/

/-- A fresh default is bounded: its arrays are empty or of their fixed
length, its mappings empty. -/
theorem defaultForTy_bnd : ∀ (T : Ty), (defaultForTy T).bnd T := by
  intro T
  induction T using defaultForTy.induct
    (motive2 := fun l => ∀ (s : Name), (∀ nt ∈ l, lookupBy nt.1 (structDef s) = some nt.2) →
      bndFields s (defaultForFields l)) with
  | case1 => simp only [defaultForTy, Semantics.SVal.bnd]
  | case2 => simp only [defaultForTy, Semantics.SVal.bnd]
  | case3 => simp only [defaultForTy, Semantics.SVal.bnd]
  | case4 name ih =>
    rw [defaultForTy]
    exact ih name fun nt hm => lookupBy_eq_of_nodup (structDef_nodup name) hm
  | case5 elem =>
    rw [defaultForTy]
    exact ⟨by decide, trivial, trivial⟩
  | case6 elem n ih =>
    rw [defaultForTy]
    exact ⟨bndElems_iff.mpr fun v hv => by rw [List.eq_of_mem_replicate hv]; exact ih, trivial⟩
  | case7 key value ih =>
    rw [defaultForTy]
    exact ⟨trivial, ih⟩
  | case8 => simp only [defaultForFields, bndFields]
  | case9 n t rest iht ihrest =>
    rename_i s h
    simp only [defaultForFields, bndFields, h (n, t) (List.mem_cons_self ..)]
    exact ⟨iht, ihrest s fun nt hm => h nt (List.mem_cons_of_mem _ hm)⟩

/-- What `find` reaches in a bounded value is bounded. -/
theorem find_bnd : ∀ {segs : List Seg} {v : Semantics.SVal} {T T' : Ty} {w : Semantics.SVal},
    v.bnd T → tyAtSegs T segs = some T' → v.find segs = .ok w → w.bnd T'
  | [], v, T, T', w, hb, hs, hf => by
    simp only [tyAtSegs, Option.some.injEq] at hs
    subst hs
    rw [SemanticsProperties.SVal.find_nil] at hf; cases hf; exact hb
  | seg :: rest, v, T, T', w, hb, hs, hf => by
    simp only [tyAtSegs] at hs
    cases hseg : segTy T seg with
    | none => rw [hseg] at hs; exact nomatch hs
    | some U =>
      rw [hseg] at hs
      cases seg with
      | field n =>
        cases T with
        | prim _ => simp only [segTy, reduceCtorEq] at hseg
        | ref r =>
          cases r with
          | struct s =>
            simp only [segTy] at hseg
            cases v with
            | struct fields =>
              simp only [Semantics.SVal.find] at hf
              split at hf
              · rename_i v' hl
                exact find_bnd (bndFields_lookup hb hl hseg) hs hf
              · exact nomatch hf
            | prim _ | array _ _ _ | map _ _ => exact hb.elim
          | array _ | fixed _ _ | mapping _ _ => simp only [segTy, reduceCtorEq] at hseg
      | «at» i =>
        cases T with
        | prim _ => simp only [segTy, reduceCtorEq] at hseg
        | ref r =>
          cases r with
          | struct _ => simp only [segTy, reduceCtorEq] at hseg
          | array E =>
            simp only [segTy, Option.some.injEq] at hseg
            subst hseg
            cases v with
            | array elems sh fx =>
              simp only [Semantics.SVal.find] at hf
              split at hf
              · have hm := List.get_mem (elems ++ sh) ⟨i.toNat, by omega⟩
                exact find_bnd (bndElems_iff.mp (bndElems_append hb.2.1 hb.2.2) _ hm) hs hf
              · exact nomatch hf
            | prim _ | struct _ | map _ _ => exact hb.elim
          | fixed E _ =>
            simp only [segTy, Option.some.injEq] at hseg
            subst hseg
            cases v with
            | array elems sh fx =>
              simp only [Semantics.SVal.find] at hf
              split at hf
              · have hm := List.get_mem (elems ++ sh) ⟨i.toNat, by omega⟩
                exact find_bnd (bndElems_iff.mp (bndElems_append hb.1 hb.2) _ hm) hs hf
              · exact nomatch hf
            | prim _ | struct _ | map _ _ => exact hb.elim
          | mapping K V =>
            simp only [segTy, Option.some.injEq] at hseg
            subst hseg
            cases v with
            | map es d =>
              simp only [Semantics.SVal.find] at hf
              split at hf
              · rename_i v' hl
                exact find_bnd (bndEntries_lookup hb.1 hl) hs hf
              · exact find_bnd hb.2 hs hf
            | prim _ | struct _ | array _ _ _ => exact hb.elim

/-- Saving a bounded value at a path whose keys fit keeps the tree bounded:
an array's slots are rewritten in place, a missing entry is created at a
key in range. -/
theorem save_bnd : ∀ {segs : List Seg} {v : Semantics.SVal} {T T' : Ty} {new w : Semantics.SVal},
    v.bnd T → tyAtSegs T segs = some T' → KeysFit T segs → new.bnd T' →
      v.save segs new = .ok w → w.bnd T
  | [], v, T, T', new, w, _, hs, _, hn, hf => by
    simp only [tyAtSegs, Option.some.injEq] at hs
    subst hs
    rw [SemanticsProperties.SVal.save_nil] at hf; cases hf; exact hn
  | seg :: rest, v, T, T', new, w, hb, hs, hk, hn, hf => by
    simp only [tyAtSegs] at hs
    obtain ⟨hk₁, hk₂⟩ := hk
    cases hseg : segTy T seg with
    | none => rw [hseg] at hs; exact nomatch hs
    | some U =>
      rw [hseg] at hs
      simp only [hseg] at hk₂
      cases seg with
      | field n =>
        cases T with
        | prim _ => simp only [segTy, reduceCtorEq] at hseg
        | ref r =>
          cases r with
          | struct s =>
            simp only [segTy] at hseg
            cases v with
            | struct fields =>
              simp only [Semantics.SVal.save] at hf
              split at hf
              · rename_i old hl
                obtain ⟨up, hup, hf⟩ := bind_ok_inv hf
                cases hf
                exact bndFields_setBy hb hseg
                  (save_bnd (bndFields_lookup hb hl hseg) hs hk₂ hn hup)
              · exact nomatch hf
            | prim _ | array _ _ _ | map _ _ => exact hb.elim
          | array _ | fixed _ _ | mapping _ _ => simp only [segTy, reduceCtorEq] at hseg
      | «at» i =>
        cases T with
        | prim _ => simp only [segTy, reduceCtorEq] at hseg
        | ref r =>
          cases r with
          | struct _ => simp only [segTy, reduceCtorEq] at hseg
          | array E =>
            simp only [segTy, Option.some.injEq] at hseg
            subst hseg
            cases v with
            | array elems sh fx =>
              simp only [Semantics.SVal.save] at hf
              split at hf
              · rename_i hbd
                obtain ⟨up, hup, hf⟩ := bind_ok_inv hf
                cases hf
                have hall := bndElems_append hb.2.1 hb.2.2
                have hm := List.get_mem (elems ++ sh) ⟨i.toNat, hbd.2⟩
                have hupb := save_bnd (bndElems_iff.mp hall _ hm) hs hk₂ hn hup
                have hset : ∀ x ∈ (elems ++ sh).set i.toNat up, x.bnd E := by
                  intro x hx
                  rcases List.mem_or_eq_of_mem_set hx with hx | rfl
                  · exact bndElems_iff.mp hall x hx
                  · exact hupb
                refine ⟨?_, bndElems_iff.mpr fun x hx => hset x (List.mem_of_mem_take hx),
                  bndElems_iff.mpr fun x hx => hset x (List.mem_of_mem_drop hx)⟩
                have h1 := hb.1
                simp only [List.length_take, List.length_drop, List.length_set,
                  List.length_append] at h1 ⊢
                omega
              · exact nomatch hf
            | prim _ | struct _ | map _ _ => exact hb.elim
          | fixed E n =>
            simp only [segTy, Option.some.injEq] at hseg
            subst hseg
            cases v with
            | array elems sh fx =>
              simp only [Semantics.SVal.save] at hf
              split at hf
              · rename_i hbd
                obtain ⟨up, hup, hf⟩ := bind_ok_inv hf
                cases hf
                have hall := bndElems_append hb.1 hb.2
                have hm := List.get_mem (elems ++ sh) ⟨i.toNat, hbd.2⟩
                have hupb := save_bnd (bndElems_iff.mp hall _ hm) hs hk₂ hn hup
                have hset : ∀ x ∈ (elems ++ sh).set i.toNat up, x.bnd E := by
                  intro x hx
                  rcases List.mem_or_eq_of_mem_set hx with hx | rfl
                  · exact bndElems_iff.mp hall x hx
                  · exact hupb
                exact ⟨bndElems_iff.mpr fun x hx => hset x (List.mem_of_mem_take hx),
                  bndElems_iff.mpr fun x hx => hset x (List.mem_of_mem_drop hx)⟩
              · exact nomatch hf
            | prim _ | struct _ | map _ _ => exact hb.elim
          | mapping K V =>
            simp only [segTy, Option.some.injEq] at hseg
            subst hseg
            have hkey : K.keyOk i := hk₁
            cases v with
            | map es d =>
              simp only [Semantics.SVal.save] at hf
              split at hf
              · rename_i old hl
                obtain ⟨up, hup, hf⟩ := bind_ok_inv hf
                cases hf
                exact ⟨bndEntries_setBy hb.1 hkey
                  (save_bnd (bndEntries_lookup hb.1 hl) hs hk₂ hn hup), hb.2⟩
              · obtain ⟨up, hup, hf⟩ := bind_ok_inv hf
                cases hf
                exact ⟨bndEntries_setBy hb.1 hkey (save_bnd hb.2 hs hk₂ hn hup), hb.2⟩
            | prim _ | struct _ | array _ _ _ => exact hb.elim

/-! ### `delete`, copies, pushes, pops -/

mutual

/-- `delete` keeps a value bounded: an array's live elements move, cleared,
into its recycled slots, so their number stays. -/
theorem Semantics.SVal.defaultOf_bnd : ∀ {v : Semantics.SVal} {T : Ty}, v.bnd T →
    v.defaultOf.bnd T
  | .prim (.int _), .prim _, _ | .prim (.bool _), .prim _, _ => trivial
  | .struct fields, .ref (.struct _), hb => Semantics.SVal.defaultOfFields_bnd hb
  | .array elems sh false, .ref (.array _), hb => by
    refine ⟨?_, trivial, bndElems_append (Semantics.SVal.defaultOfElems_bnd hb.2.1) hb.2.2⟩
    have h1 := hb.1
    simp only [List.length_nil, List.length_append, Semantics.SVal.defaultOfElems_length]
    omega
  | .array elems sh true, .ref (.array _), hb =>
    ⟨by simpa only [Semantics.SVal.defaultOfElems_length] using hb.1,
      Semantics.SVal.defaultOfElems_bnd hb.2.1, hb.2.2⟩
  | .array elems sh false, .ref (.fixed _ _), hb =>
    ⟨trivial, bndElems_append (Semantics.SVal.defaultOfElems_bnd hb.1) hb.2⟩
  | .array elems sh true, .ref (.fixed _ _), hb => ⟨Semantics.SVal.defaultOfElems_bnd hb.1, hb.2⟩
  | .map _ _, .ref (.mapping _ _), hb => hb
  | .prim _, .ref _, hb | .struct _, .prim _, hb | .array _ _ _, .prim _, hb
  | .map _ _, .prim _, hb => hb.elim
  | .struct _, .ref (.array _), hb | .struct _, .ref (.mapping _ _), hb
  | .struct _, .ref (.fixed _ _), hb => hb.elim
  | .array _ _ _, .ref (.struct _), hb | .array _ _ _, .ref (.mapping _ _), hb => hb.elim
  | .map _ _, .ref (.struct _), hb | .map _ _, .ref (.array _), hb
  | .map _ _, .ref (.fixed _ _), hb => hb.elim

theorem Semantics.SVal.defaultOfFields_bnd {s : Name} :
    ∀ {fields : List (Name × Semantics.SVal)}, bndFields s fields →
      bndFields s (Semantics.SVal.defaultOf.defaultOfFields fields)
  | [], _ => trivial
  | (n, v) :: rest, hb => by
    refine ⟨?_, Semantics.SVal.defaultOfFields_bnd hb.2⟩
    have h1 := hb.1
    revert h1
    cases lookupBy n (structDef s) with
    | none => intro _; trivial
    | some T => exact fun h => Semantics.SVal.defaultOf_bnd h

theorem Semantics.SVal.defaultOfElems_bnd {E : Ty} :
    ∀ {elems : List Semantics.SVal}, bndElems E elems →
      bndElems E (Semantics.SVal.defaultOf.defaultOfElems elems)
  | [], _ => trivial
  | _ :: _, hb => ⟨Semantics.SVal.defaultOf_bnd hb.1, Semantics.SVal.defaultOfElems_bnd hb.2⟩

end

mutual

/-- A value laid on fresh slots is bounded: its arrays lose their recycled
slots. -/
theorem Semantics.SVal.strip_bnd : ∀ {v : Semantics.SVal} {T : Ty}, v.bnd T → v.strip.bnd T
  | .prim _, .prim _, _ => trivial
  | .struct fields, .ref (.struct _), hb => Semantics.SVal.stripFields_bnd hb
  | .array elems _ _, .ref (.array _), hb => by
    refine ⟨?_, Semantics.SVal.stripElems_bnd hb.2.1, trivial⟩
    have h1 := hb.1
    simp only [List.length_nil, Nat.add_zero, Semantics.SVal.stripElems_length']
    omega
  | .array _ _ _, .ref (.fixed _ _), hb => ⟨Semantics.SVal.stripElems_bnd hb.1, trivial⟩
  | .map _ _, .ref (.mapping _ _), hb => hb
  | .prim _, .ref _, hb | .struct _, .prim _, hb | .array _ _ _, .prim _, hb
  | .map _ _, .prim _, hb => hb.elim
  | .struct _, .ref (.array _), hb | .struct _, .ref (.mapping _ _), hb
  | .struct _, .ref (.fixed _ _), hb => hb.elim
  | .array _ _ _, .ref (.struct _), hb | .array _ _ _, .ref (.mapping _ _), hb => hb.elim
  | .map _ _, .ref (.struct _), hb | .map _ _, .ref (.array _), hb
  | .map _ _, .ref (.fixed _ _), hb => hb.elim

theorem Semantics.SVal.stripFields_bnd {s : Name} :
    ∀ {fields : List (Name × Semantics.SVal)}, bndFields s fields →
      bndFields s (Semantics.SVal.strip.stripFields fields)
  | [], _ => trivial
  | (n, v) :: rest, hb => by
    refine ⟨?_, Semantics.SVal.stripFields_bnd hb.2⟩
    have h1 := hb.1
    revert h1
    cases lookupBy n (structDef s) with
    | none => intro _; trivial
    | some T => exact fun h => Semantics.SVal.strip_bnd h

theorem Semantics.SVal.stripElems_bnd {E : Ty} :
    ∀ {elems : List Semantics.SVal}, bndElems E elems →
      bndElems E (Semantics.SVal.strip.stripElems elems)
  | [], _ => trivial
  | _ :: _, hb => ⟨Semantics.SVal.strip_bnd hb.1, Semantics.SVal.stripElems_bnd hb.2⟩

end

mutual

/-- **A copy keeps storage bounded**: an array takes the new length, and
keeps the old slots past it, so it has the larger of the two counts. -/
theorem Semantics.SVal.overlay_bnd {old new : Semantics.SVal} {T : Ty} (hob : old.bnd T)
    (hnb : new.bnd T) : (old.overlay new).bnd T := by
  match new with
  | .prim p => cases old <;> simpa only [Semantics.SVal.overlay, Semantics.SVal.strip] using hnb
  | .struct nfs =>
      cases old with
      | struct ofs =>
          cases T with
          | prim _ => exact hnb.elim
          | ref r =>
              cases r with
              | struct s => exact Semantics.SVal.overlayFields_bnd hob hnb
              | array _ | fixed _ _ | mapping _ _ => exact hnb.elim
      | prim _ => simp only [Semantics.SVal.overlay]; exact Semantics.SVal.strip_bnd hnb
      | array _ _ _ => simp only [Semantics.SVal.overlay]; exact Semantics.SVal.strip_bnd hnb
      | map _ _ => simp only [Semantics.SVal.overlay]; exact Semantics.SVal.strip_bnd hnb
  | .array nel nsh nfx =>
      cases old with
      | array oel osh ofx =>
          cases T with
          | prim _ => exact hnb.elim
          | ref r =>
              cases r with
              | array E =>
                  simp only [Semantics.SVal.overlay]
                  refine ⟨?_, Semantics.SVal.overlayElems_bnd
                      (bndElems_append hob.2.1 hob.2.2) hnb.2.1,
                    bndElems_append (Semantics.SVal.defaultOfElems_bnd (bndElems_drop _ hob.2.1))
                      (bndElems_drop _ hob.2.2)⟩
                  have h1 := hob.1
                  have h2 := hnb.1
                  simp only [List.length_append, Semantics.SVal.overlayElems_length,
                    Semantics.SVal.defaultOfElems_length, List.length_drop]
                  omega
              | fixed E n =>
                  simp only [Semantics.SVal.overlay]
                  exact ⟨Semantics.SVal.overlayElems_bnd (bndElems_append hob.1 hob.2) hnb.1,
                    bndElems_append (Semantics.SVal.defaultOfElems_bnd (bndElems_drop _ hob.1))
                      (bndElems_drop _ hob.2)⟩
              | struct _ | mapping _ _ => exact hnb.elim
      | prim _ => simp only [Semantics.SVal.overlay]; exact Semantics.SVal.strip_bnd hnb
      | struct _ => simp only [Semantics.SVal.overlay]; exact Semantics.SVal.strip_bnd hnb
      | map _ _ => simp only [Semantics.SVal.overlay]; exact Semantics.SVal.strip_bnd hnb
  | .map ne nd =>
      cases old with
      | map oe od => simpa only [Semantics.SVal.overlay] using hob
      | prim _ => simp only [Semantics.SVal.overlay]; exact Semantics.SVal.strip_bnd hnb
      | struct _ => simp only [Semantics.SVal.overlay]; exact Semantics.SVal.strip_bnd hnb
      | array _ _ _ => simp only [Semantics.SVal.overlay]; exact Semantics.SVal.strip_bnd hnb

theorem Semantics.SVal.overlayFields_bnd {s : Name} {ofs nfs : List (Name × Semantics.SVal)}
    (hob : bndFields s ofs) (hnb : bndFields s nfs) :
    bndFields s (Semantics.SVal.overlay.overlayFields ofs nfs) := by
  match nfs with
  | [] => trivial
  | (n, v) :: rest =>
      refine ⟨?_, Semantics.SVal.overlayFields_bnd hob hnb.2⟩
      have h1 := hnb.1
      revert h1
      cases hdef : lookupBy n (structDef s) with
      | none => intro _; trivial
      | some T =>
          intro h1
          cases hl : lookupBy n ofs with
          | none => exact Semantics.SVal.strip_bnd h1
          | some o => exact Semantics.SVal.overlay_bnd (bndFields_lookup hob hl hdef) h1

theorem Semantics.SVal.overlayElems_bnd {E : Ty} {olds news : List Semantics.SVal}
    (hob : bndElems E olds) (hnb : bndElems E news) :
    bndElems E (Semantics.SVal.overlay.overlayElems olds news) := by
  match olds, news with
  | o :: os, v :: rest =>
    exact ⟨Semantics.SVal.overlay_bnd hob.1 hnb.1, Semantics.SVal.overlayElems_bnd hob.2 hnb.2⟩
  | [], rest => simpa only [Semantics.SVal.overlay.overlayElems] using
      Semantics.SVal.stripElems_bnd hnb
  | _ :: _, [] => trivial

end

/-- The slot a push lands on is bounded, and the recycled slots it leaves
are the old ones but the first. -/
theorem pushSlot_bnd {E : Ty} {shadow : List Semantics.SVal} (hsh : bndElems E shadow) :
    (Semantics.pushSlot E shadow).1.bnd E ∧ bndElems E (Semantics.pushSlot E shadow).2 ∧
      (shadow ≠ [] → (Semantics.pushSlot E shadow).2.length + 1 = shadow.length) ∧
      (shadow = [] → (Semantics.pushSlot E shadow).2 = []) := by
  cases shadow with
  | nil => exact ⟨defaultForTy_bnd E, trivial, fun h => absurd rfl h, fun _ => rfl⟩
  | cons c rest =>
    refine ⟨?_, hsh.2, fun _ => rfl, fun h => nomatch h⟩
    simp only [Semantics.pushSlot]
    split
    · exact defaultForTy_bnd E
    · exact hsh.1

/-- An array one element longer, bounded when it took a recycled slot or
stayed below the bound. -/
theorem pushed_bnd {E : Ty} {elems shadow : List Semantics.SVal} {fx fx' : Bool}
    {x : Semantics.SVal} (hb : (Semantics.SVal.array elems shadow fx).bnd (.ref (.array E)))
    (hx : x.bnd E) (hlen : elems.length + 1 < 2 ^ 256) :
    (Semantics.SVal.array (elems ++ [x]) (Semantics.pushSlot E shadow).2 fx').bnd
      (.ref (.array E)) := by
  obtain ⟨-, hsb, hlen', hnil⟩ := pushSlot_bnd hb.2.2
  refine ⟨?_, bndElems_append hb.2.1 ⟨hx, trivial⟩, hsb⟩
  have h1 := hb.1
  simp only [List.length_append, List.length_cons, List.length_nil]
  by_cases hs : shadow = []
  · rw [hnil hs]; simp only [List.length_nil]; omega
  · have := hlen' hs; omega

/-- An array one element shorter, its last element moved into the recycled
slots. -/
theorem popped_bnd {E : Ty} {elems shadow restRev : List Semantics.SVal} {last y : Semantics.SVal}
    {fx fx' : Bool} (hb : (Semantics.SVal.array elems shadow fx).bnd (.ref (.array E)))
    (hrev : elems.reverse = last :: restRev) (hy : last.bnd E → y.bnd E) :
    (Semantics.SVal.array restRev.reverse (y :: shadow) fx').bnd (.ref (.array E)) := by
  have hmem : ∀ v, v ∈ last :: restRev → v ∈ elems := by
    intro v hv; rw [← hrev] at hv; exact List.mem_reverse.mp hv
  refine ⟨?_, bndElems_iff.mpr fun v hv => bndElems_iff.mp hb.2.1 v
      (hmem v (List.mem_cons_of_mem _ (List.mem_reverse.mp hv))),
    hy (bndElems_iff.mp hb.2.1 last (hmem last List.mem_cons_self)), hb.2.2⟩
  have h1 := hb.1
  have hl : elems.length = restRev.length + 1 := by
    rw [← List.length_reverse (as := elems), hrev, List.length_cons]
  simp only [List.length_reverse, List.length_cons]
  omega

/-! ### The state -/

theorem BndStorage.setBy {st : List (Name × Semantics.SVal)} (hb : BndStorage C st) {r : Name}
    {T : Ty} {v : Semantics.SVal} (hr : lookupBy r C.vars = some T) (hv : v.bnd T) :
    BndStorage C (setBy r v st) := by
  intro r' T' v' hr' hv'
  by_cases he : r' = r
  · subst he
    rw [lookupBy_setBy_self] at hv'
    cases hv'
    rw [hr] at hr'
    cases hr'
    exact hv
  · rw [lookupBy_setBy_ne he] at hv'
    exact hb r' T' v' hr' hv'

section State

variable {σ σ' : Semantics.State}

theorem bnd_findStorage (hb : BndStorage C σ.storage) {r : Name} {segs : List Seg} {T' : Ty}
    (hT : C.layout.tyAt r segs = some T') {w : Semantics.SVal} (hf : σ.findStorage r segs = .ok w) :
    w.bnd T' := by
  obtain ⟨T, hr, hs⟩ := Layout.tyAt_split hT
  simp only [Semantics.State.findStorage] at hf
  split at hf
  · rename_i V hV
    exact find_bnd (hb r T V hr hV) hs hf
  · exact nomatch hf

theorem bnd_saveStorage (hb : BndStorage C σ.storage) {r : Name} {segs : List Seg} {T' : Ty}
    (hT : C.layout.tyAt r segs = some T') (hk : ∀ T, lookupBy r C.vars = some T → KeysFit T segs)
    {new : Semantics.SVal} (hn : new.bnd T') (h : σ.saveStorage r segs new = .ok σ') :
    BndStorage C σ'.storage := by
  obtain ⟨T, hr, hs⟩ := Layout.tyAt_split hT
  obtain ⟨V, up, hV, hup, rfl⟩ := SemanticsProperties.State.saveStorage_ok_inv h
  exact BndStorage.setBy hb hr (save_bnd (hb r T V hr hV) hs (hk T hr) hn hup)

/-- A push at a resolved array, below the bound. -/
theorem bnd_pushAt (hb : BndStorage C σ.storage) {E : Ty} {r : Name} {segs : List Seg}
    (hT : C.layout.tyAt r segs = some (.ref (.array E)))
    (hk : ∀ T, lookupBy r C.vars = some T → KeysFit T segs)
    (hlen : ∀ elems sh fx, σ.findStorage r segs = .ok (.array elems sh fx) →
      elems.length + 1 < 2 ^ 256)
    {val : Semantics.SVal → Res Semantics.SVal} (hval : ∀ slot v, slot.bnd E → val slot = .ok v → v.bnd E)
    (h : pushAt σ E r segs val = .ok σ') : BndStorage C σ'.storage := by
  obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
  have hsb := bnd_findStorage hb hT hsv
  cases sv with
  | array elems shadow fx =>
    obtain ⟨newElem, hnew, h⟩ := bind_ok_inv h
    exact bnd_saveStorage hb hT hk (pushed_bnd hsb
      (hval _ _ (pushSlot_bnd hsb.2.2).1 hnew) (hlen _ _ _ hsv)) h
  | prim _ | struct _ | map _ _ => exact nomatch h

/-- `b.push()` as a place, below the bound. -/
theorem bnd_pushPlaceAt (hb : BndStorage C σ.storage) {E : Ty} {r : Name} {segs : List Seg}
    (hT : C.layout.tyAt r segs = some (.ref (.array E)))
    (hk : ∀ T, lookupBy r C.vars = some T → KeysFit T segs)
    (hlen : ∀ elems sh fx, σ.findStorage r segs = .ok (.array elems sh fx) →
      elems.length + 1 < 2 ^ 256)
    {n : Int} (h : pushPlaceAt σ E r segs = .ok (σ', n)) : BndStorage C σ'.storage := by
  obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
  have hsb := bnd_findStorage hb hT hsv
  cases sv with
  | array elems shadow fx =>
    obtain ⟨σ₁, hσ₁, h⟩ := bind_ok_inv h
    cases h
    exact bnd_saveStorage hb hT hk (pushed_bnd hsb (pushSlot_bnd hsb.2.2).1
      (hlen _ _ _ hsv)) hσ₁
  | prim _ | struct _ | map _ _ => exact nomatch h

/-- A pop at a resolved array. -/
theorem bnd_popAt (hb : BndStorage C σ.storage) {E : Ty} {r : Name} {segs : List Seg}
    (hT : C.layout.tyAt r segs = some (.ref (.array E)))
    (hk : ∀ T, lookupBy r C.vars = some T → KeysFit T segs) {keep : Bool}
    (h : popAt σ keep r segs = .ok σ') : BndStorage C σ'.storage := by
  obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
  have hsb := bnd_findStorage hb hT hsv
  cases sv with
  | array elems shadow fx =>
    simp only at h
    split at h
    · exact nomatch h
    · rename_i last restRev hrev
      refine bnd_saveStorage hb hT hk (popped_bnd hsb hrev fun hl => ?_) h
      split
      · exact hl
      · exact Semantics.SVal.defaultOf_bnd hl
  | prim _ | struct _ | map _ _ => exact nomatch h

end State

/-! ## Typed values

What the typed state gives by construction: a copy out of memory, with no
mapping and nothing past its arrays' ends, is bounded; and a bounded value
fits, its words in range by their types and its fixed sizes by
`FixedFitsAt`. -/

theorem FixedFitsAt.seg {T U : Ty} {seg : Seg} (h : FixedFitsAt T) (hs : segTy T seg = some U) :
    FixedFitsAt U :=
  fun segs E n hu => h (seg :: segs) E n (by simp only [tyAtSegs, hs]; exact hu)

open Semantics.SVal.plain (plainFields plainElems)
open Semantics.SVal.fits (fitsFields fitsElems fitsEntries)

mutual

theorem SVal.erase_plain_bnd : {T : Ty} → (v : SVal T) → v.erase.plain → v.erase.bnd T
  | _, .prim _, _ => by rw [SVal.erase_prim]; trivial
  | _, .struct (s := s) fs, hp => by
    rw [SVal.erase_struct] at hp ⊢
    exact SFields.erase_plain_bnd s fs (fun _ hm => lookupBy_eq_of_nodup (structDef_nodup s) hm) hp
  | _, .array (n := n) e sh hn, hp => by
    rw [SVal.erase_array] at hp ⊢
    obtain ⟨hsh, hpe⟩ := hp
    refine ⟨?_, SVec.erase_plain_bnd e hpe, ?_⟩
    · rw [hsh, SVec.length_erase]; simpa only [List.length_nil, Nat.add_zero] using hn
    · rw [hsh]; trivial
  | _, .fixed e, hp => by
    rw [SVal.erase_fixed] at hp ⊢
    exact ⟨SVec.erase_plain_bnd e hp.2, trivial⟩
  | _, .map _ _, hp => by rw [SVal.erase_map] at hp; exact hp.elim

theorem SFields.erase_plain_bnd (s : Name) : {fs : List (Name × Ty)} → (x : SFields fs) →
    (∀ fT ∈ fs, lookupBy fT.1 (structDef s) = some fT.2) → plainFields x.erase →
      bndFields s x.erase
  | _, .nil, _, _ => by rw [SFields.erase_nil]; trivial
  | _, .cons (f := f) (T := T) v rest, hl, hp => by
    rw [SFields.erase_cons] at hp ⊢
    refine ⟨?_, SFields.erase_plain_bnd s rest (fun fT hm => hl fT (List.mem_cons_of_mem _ hm))
      hp.2⟩
    simp only [hl (f, T) List.mem_cons_self]
    exact SVal.erase_plain_bnd v hp.1

theorem SVec.erase_plain_bnd : {E : Ty} → {n : Nat} → (l : SVec E n) → plainElems l.erase →
    bndElems E l.erase
  | _, _, .nil, _ => by rw [SVec.erase_nil]; trivial
  | _, _, .cons v rest, hp => by
    rw [SVec.erase_cons] at hp ⊢
    exact ⟨SVal.erase_plain_bnd v hp.1, SVec.erase_plain_bnd rest hp.2⟩

end

mutual

/-- **A bounded typed value fits**: its words are in range by their types,
its fixed sizes by `FixedFitsAt`, and the rest is what `bnd` says. -/
theorem SVal.erase_fits : {T : Ty} → (v : SVal T) → FixedFitsAt T → v.erase.bnd T →
    v.erase.fits T
  | _, .prim (p := p) x, _, _ => by
    rw [SVal.erase_prim]
    cases p with
    | bool => trivial
    | uint => exact x.2
    | int => exact x.2
  | _, .struct (s := s) fs, hf, hb => by
    rw [SVal.erase_struct] at hb ⊢
    exact SFields.erase_fits s fs (fun _ hm => lookupBy_eq_of_nodup (structDef_nodup s) hm)
      (fun hl => hf.seg (seg := .field _) hl) hb
  | _, .array e sh _, hf, hb => by
    rw [SVal.erase_array] at hb ⊢
    exact ⟨hb.1, SVec.erase_fits e (hf.seg (seg := .at 0) rfl) hb.2.1,
      SList.erase_fits sh (hf.seg (seg := .at 0) rfl) hb.2.2⟩
  | _, .fixed (n := n) e, hf, hb => by
    rw [SVal.erase_fixed] at hb ⊢
    refine ⟨?_, SVec.erase_fits e (hf.seg (seg := .at 0) rfl) hb.1⟩
    rw [SVec.length_erase]
    exact hf [] _ n rfl
  | _, .map m _, hf, hb => by
    rw [SVal.erase_map] at hb ⊢
    exact SMap.erase_fits m (hf.seg (seg := .at 0) rfl) hb.1

theorem SFields.erase_fits (s : Name) : {fs : List (Name × Ty)} → (x : SFields fs) →
    (∀ fT ∈ fs, lookupBy fT.1 (structDef s) = some fT.2) →
    (∀ {f T}, lookupBy f (structDef s) = some T → FixedFitsAt T) → bndFields s x.erase →
      fitsFields s x.erase
  | _, .nil, _, _, _ => by rw [SFields.erase_nil]; trivial
  | _, .cons (f := f) (T := T) v rest, hl, hf, hb => by
    rw [SFields.erase_cons] at hb ⊢
    have hlf := hl (f, T) List.mem_cons_self
    refine ⟨?_, SFields.erase_fits s rest (fun fT hm => hl fT (List.mem_cons_of_mem _ hm)) hf
      hb.2⟩
    have hb1 := hb.1
    simp only [hlf] at hb1 ⊢
    exact SVal.erase_fits v (hf hlf) hb1

theorem SVec.erase_fits : {E : Ty} → {n : Nat} → (l : SVec E n) → FixedFitsAt E →
    bndElems E l.erase → fitsElems E l.erase
  | _, _, .nil, _, _ => by rw [SVec.erase_nil]; trivial
  | _, _, .cons v rest, hf, hb => by
    rw [SVec.erase_cons] at hb ⊢
    exact ⟨SVal.erase_fits v hf hb.1, SVec.erase_fits rest hf hb.2⟩

theorem SList.erase_fits : {E : Ty} → (l : SList E) → FixedFitsAt E →
    bndElems E l.erase → fitsElems E l.erase
  | _, .nil, _, _ => by rw [SList.erase_nil]; trivial
  | _, .cons v rest, hf, hb => by
    rw [SList.erase_cons] at hb ⊢
    exact ⟨SVal.erase_fits v hf hb.1, SList.erase_fits rest hf hb.2⟩

theorem SMap.erase_fits {K : Ty} : {V : Ty} → (m : SMap V) → FixedFitsAt V →
    bndEntries K V m.erase → fitsEntries K V m.erase
  | _, .nil, _, _ => by rw [SMap.erase_nil]; trivial
  | _, .cons _ v rest, hf, hb => by
    rw [SMap.erase_cons] at hb ⊢
    refine ⟨?_, SVal.erase_fits v hf hb.2.1, SMap.erase_fits rest hf hb.2.2⟩
    have hk := hb.1
    cases K with
    | prim _ => exact hk
    | ref _ => trivial

end

/-! ## Typed storage

Each typed write, read through its erasure (`Semantics/StorageErase.lean`):
the typed reference gives the path's type (`tyAtSegs_erase`) and, with the
invariant on aliases, its keys' range (`SRef.KeysFit`). -/

/-- Every key along a typed reference's path in range. -/
def SRef.KeysFit {U : Ty} (r : SRef C U) : Prop := Solidity.KeysFit r.ty r.path.erase

namespace Storage

variable {st st' : Storage C}

theorem root_bnd (hb : BndStorage C st.erase) {U : Ty} (r : SRef C U) :
    (st.get r.hroot).erase.bnd r.ty :=
  hb r.root r.ty _ r.hroot (SFields.lookupBy_erase st r.hroot)

theorem find_bnd (hb : BndStorage C st.erase) {U : Ty} (r : SRef C U) {v : SVal U}
    (h : st.find r = some v) : v.erase.bnd U := by
  have hf := SVal.find_erase (st.get r.hroot) r.path
  have h' : (st.get r.hroot).find r.path = some v := h
  rw [h'] at hf
  exact Solidity.find_bnd (root_bnd hb r) (tyAtSegs_erase r.path) hf

theorem save_bnd (hb : BndStorage C st.erase) {U : Ty} (r : SRef C U) {new : SVal U}
    (hk : r.KeysFit) (hn : new.erase.bnd U) (h : st.save r new = some st') :
    BndStorage C st'.erase := by
  unfold Storage.save at h
  obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  have he := SVal.save_erase (st.get r.hroot) r.path new
  rw [hv] at he
  show BndStorage C (SFields.erase (st.set r.hroot v))
  rw [← SFields.setBy_erase st r.hroot v]
  exact BndStorage.setBy hb r.hroot
    (Solidity.save_bnd (root_bnd hb r) (tyAtSegs_erase r.path) hk hn he)

theorem write_bnd (hb : BndStorage C st.erase) {U : Ty} (r : SRef C U) {new : SVal U}
    (hk : r.KeysFit) (hn : new.erase.bnd U) (h : st.write r new = some st') :
    BndStorage C st'.erase := by
  unfold Storage.write at h
  split at h
  · exact save_bnd hb r hk hn h
  · obtain ⟨cur, hcur, h⟩ := Option.bind_eq_some_iff.mp h
    refine save_bnd hb r hk ?_ h
    rw [SVal.overlay_erase]
    exact Semantics.SVal.overlay_bnd (find_bnd hb r hcur) hn

theorem delete_bnd (hb : BndStorage C st.erase) {U : Ty} (r : SRef C U) (hk : r.KeysFit)
    (h : st.delete r = some st') : BndStorage C st'.erase := by
  unfold Storage.delete at h
  obtain ⟨cur, hcur, h⟩ := Option.bind_eq_some_iff.mp h
  refine save_bnd hb r hk ?_ h
  rw [SVal.defaultOf_erase]
  exact Semantics.SVal.defaultOf_bnd (find_bnd hb r hcur)

/-- Below the bound in the typed storage, below it in the erasure. -/
theorem len_of_full {E : Ty} {σ : Semantics.State} (hs : σ.storage = st.erase)
    (r : SRef C (.ref (.array E))) (hfull : st.full r = false) :
    ∀ elems sh fx, σ.findStorage r.root r.path.erase = .ok (.array elems sh fx) →
      elems.length + 1 < 2 ^ 256 := by
  intro elems sh fx hf
  rw [findStorage_erase hs r] at hf
  cases hv : st.find r with
  | none => rw [hv] at hf; exact nomatch hf
  | some v =>
    rw [hv] at hf
    have hn := full_false hfull v hv
    cases v with
    | array e sh' h =>
      simp only [toRes, SVal.erase_array, Except.ok.injEq, Semantics.SVal.array.injEq] at hf
      rw [← hf.1, SVec.length_erase]
      simpa only [SVal.view_array] using hn

end Storage

/-! ### Keys -/

theorem KeysFit_append : ∀ {segs : List Seg} {T T₁ : Ty} (seg : Seg),
    KeysFit T segs → tyAtSegs T segs = some T₁ → SegFits T₁ seg → KeysFit T (segs ++ [seg])
  | [], T, T₁, seg, _, hs, hk => by
    simp only [tyAtSegs, Option.some.injEq] at hs; subst hs
    refine ⟨hk, ?_⟩
    split <;> trivial
  | s :: rest, T, T₁, seg, hk₀, hs, hk => by
    simp only [tyAtSegs] at hs
    obtain ⟨hk₁, hk₂⟩ := hk₀
    refine ⟨hk₁, ?_⟩
    split at hs
    · rename_i U hm
      simp only [hm] at hk₂ ⊢
      exact KeysFit_append seg hk₂ hs hk
    · exact nomatch hs

theorem PrimTy.keyFits_key : {p : PrimTy} → (v : p.Denote) → p.keyFits (PrimTy.key v) = true
  | .bool, b => by cases b <;> rfl
  | .uint, n => n.2
  | .int, n => n.2

/-- An alias is bound, if at all, along a path whose keys are in range; every
other local is unconstrained. -/
def LTy.KeysFit (C : Contract) : (t : LTy) → t.Denote C → Prop
  | .alias _, o => ∀ r segs, o = some (r, segs) → ∃ T, lookupBy r C.vars = some T ∧
      Solidity.KeysFit T segs
  | .val _, _ => True
  | .mem _, _ => True
  | .old, _ => True
  | .oldNet, _ => True
  | .kint, _ => True

theorem SRef.keysFit_local {R : RefTy} {r : SRef C (.ref R)} (h : r.KeysFit) :
    LTy.KeysFit C (.alias R) (some r.erase) := by
  intro root segs he
  cases he
  exact ⟨r.ty, r.hroot, h⟩

section Paths

variable {Γ : Ctx} (σ : State C Γ)

mutual

/-- A typed path resolves along keys in range, its aliases' included. -/
theorem SPath.resolveT_keysFit (he : TEnv.All (LTy.KeysFit C) σ.env) :
    {T : Ty} → (b : SPath C Γ T) → ∀ {r : SRef C T}, b.resolveT σ = .ok r → r.KeysFit
  | _, .alias i, r, h => by
    have hk := he.get i
    change (match (TEnv.get i σ.env : Option (SRef C _)) with
      | some r => .ok r
      | none => .error .revert : TRes _) = .ok r at h
    split at h
    · rename_i r' hr'
      cases h
      rw [hr'] at hk
      obtain ⟨T, hT, hks⟩ := hk r.root r.path.erase rfl
      have hroot : lookupBy r.root C.vars = some r.ty := r.hroot
      rw [hroot] at hT
      cases hT
      exact hks
    · exact nomatch h
  | _, .loc l, r, h => Loc.resolveT_keysFit he l h

theorem Loc.resolveT_keysFit (he : TEnv.All (LTy.KeysFit C) σ.env) :
    {T : Ty} → (l : Loc C Γ T) → ∀ {r : SRef C T}, l.resolveT σ = .ok r → r.KeysFit
  | _, .root _ _, r, h => by
    cases h
    trivial
  | _, .field b f hf, r, h => by
    obtain ⟨r0, h0, h⟩ := tbind_ok_inv h
    cases h
    have hp := congrArg Prod.snd (SRef.field_erase r0 hf)
    show Solidity.KeysFit r0.ty (r0.field hf).path.erase
    rw [show (r0.field hf).path.erase = r0.path.erase ++ [.field f] from hp]
    exact KeysFit_append _ (SPath.resolveT_keysFit he b h0) (tyAtSegs_erase r0.path) trivial
  | _, .index it b i, r, h => by
    obtain ⟨r0, h0, h⟩ := tbind_ok_inv h
    obtain ⟨k, _, h⟩ := tbind_ok_inv h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    have hp := congrArg Prod.snd (SRef.index_erase r0 it (PrimTy.key k))
    show Solidity.KeysFit r0.ty (r0.index it (PrimTy.key k)).path.erase
    rw [show (r0.index it (PrimTy.key k)).path.erase = r0.path.erase ++ [.at (PrimTy.key k)]
      from hp]
    refine KeysFit_append _ (SPath.resolveT_keysFit he b h0) (tyAtSegs_erase r0.path) ?_
    cases it with
    | map => exact PrimTy.keyFits_key k
    | arr a => cases a <;> trivial

end

end Paths

/-! ## The run keeps the storage bounded -/

/-- The third run invariant: the storage bounded, every alias bound along
keys in range. -/
def fitsInv (C : Contract) : RunInv C where
  glob _ τ := BndStorage C τ.storage
  loc _ t v := LTy.KeysFit C t v
  loc_mono _ h := h

/-- The storage bounded, every alias along keys in range. -/
abbrev RunFits (C : Contract) {Γ : Ctx} (H : HeapTy) (σ : State C Γ) : Prop :=
  (fitsInv C).HoldsT H σ

theorem fitsInv.valMemOk : (fitsInv C).ValMemOk :=
  ⟨fun _ _ _ => trivial, fun _ _ _ => trivial, fun _ _ _ _ hs h => by
    show BndStorage C _; rw [hs]; exact h⟩

namespace RunFits

variable {Γ : Ctx} {H : HeapTy}

/-- A typed state's heap grown, its storage and locals as they were. -/
theorem adopt {α : HTy → Type} {σ : State C Γ} (g : Grown σ.H α) (h : RunFits C H σ) :
    RunFits C H (σ.adopt g).1 :=
  ⟨h.1, TEnv.All.wk _ h.2⟩

end RunFits

section Leaves

variable {Γ : Ctx} {H : HeapTy}

theorem Src.valueT_bnd (σ : State C Γ) (hb : BndStorage C σ.storage.erase) {T : Ty} :
    (r : Src C Γ T) → {sv : SVal T} → r.valueT σ = .ok sv → sv.erase.bnd T
  | .val _, sv, h => by
    obtain ⟨x, _, h⟩ := tbind_ok_inv h
    cases h
    rw [SVal.erase_prim]
    trivial
  | .copy _ _, sv, h => by
    obtain ⟨ref, _, h⟩ := tbind_ok_inv h
    exact Storage.find_bnd hb ref (TRes.ofOpt_ok h)

theorem SRef.keysFit_root {U : Ty} {r : SRef C U} (h : r.KeysFit) :
    ∀ T, lookupBy r.root C.vars = some T → Solidity.KeysFit T r.path.erase := by
  intro T hT
  have hr : lookupBy r.root C.vars = some r.ty := r.hroot
  rw [hr] at hT
  cases hT
  exact h

/-- `p = alice;`, `p = persons.push();`: the storage bounded (a push below
the bound), the path along keys in range. -/
theorem ARhs.evalT_fits (σ : State C Γ) (hσ : RunFits C H σ) {R : RefTy} :
    (r : ARhs C Γ R) → {st : Storage C} → {ref : SRef C (.ref R)} →
      r.evalT σ = .ok (st, ref) → BndStorage C st.erase ∧ ref.KeysFit
  | .path p, st, ref, h => by
    obtain ⟨ref', href, h⟩ := tbind_ok_inv h
    cases h
    exact ⟨hσ.1, SPath.resolveT_keysFit σ hσ.2 p href⟩
  | .push b _, st, ref, h => by
    obtain ⟨ref0, href, h⟩ := tbind_ok_inv h
    have hk := SPath.resolveT_keysFit σ hσ.2 b href
    split at h
    · exact nomatch h
    · rename_i hfull
      have hfull' : σ.storage.full ref0 = false := by simpa only [Bool.not_eq_true] using hfull
      obtain ⟨⟨st', n⟩, hp, h⟩ := tbind_ok_inv h
      cases h
      have he := Storage.pushPlaceAt_erase (σ := σ.globE) rfl ref0 hfull'
      rw [TRes.ofOpt_ok hp] at he
      refine ⟨bnd_pushPlaceAt hσ.1 (SRef.tyAt_erase ref0) (SRef.keysFit_root hk)
        (Storage.len_of_full rfl ref0 hfull') he, ?_⟩
      have hpe := congrArg Prod.snd (SRef.index_erase ref0 (IndexTy.arr ArrTy.dyn) (n : Int))
      show Solidity.KeysFit ref0.ty (ref0.index (IndexTy.arr ArrTy.dyn) (n : Int)).path.erase
      rw [show (ref0.index (IndexTy.arr ArrTy.dyn) (n : Int)).path.erase =
        ref0.path.erase ++ [.at (n : Int)] from hpe]
      exact KeysFit_append _ hk (tyAtSegs_erase ref0.path) trivial

/-- `m = n;`, `m = alice;`: the heap grown, storage and locals as they
were. -/
theorem MRhs.evalT_fits (σ : State C Γ) (hσ : RunFits C H σ) {R : RefTy} :
    (r : MRhs C Γ R) → {g : Grew C Γ σ.H (HRef · R)} → r.evalT σ = .ok g → RunFits C H g.st
  | .alias _, g, h => by
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact hσ
  | .copy _ _, g, h => by
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact RunFits.adopt _ hσ
  | .newArr _ _, g, h => by
    cases h
    exact RunFits.adopt _ hσ

theorem opStoreT_fits (σ : State C Γ) (hσ : RunFits C H σ) (op : BinOp)
    {p : PrimTy} (r : SRef C (.prim p)) (hk : r.KeysFit) (v : p.Denote) {o : Out C σ.H Γ}
    (h : opStoreT σ op r v = .ok o) : RunFits C H o.st := by
  unfold opStoreT at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨new, _, h⟩ := tbind_ok_inv h
  obtain ⟨st, hst, h⟩ := tbind_ok_inv h
  cases h
  exact ⟨Storage.save_bnd hσ.1 r hk (by rw [SVal.erase_prim]; trivial) (TRes.ofOpt_ok hst), hσ.2⟩

theorem opMemT_fits (σ : State C Γ) (hσ : RunFits C H σ) (op : BinOp)
    {p : PrimTy} (a : MAddr σ.H (.prim p)) (v : p.Denote) {o : Out C σ.H Γ}
    (h : opMemT σ op a v = .ok o) : RunFits C H o.st := by
  unfold opMemT at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  cases h
  exact ⟨hσ.1, hσ.2⟩

theorem OpLoc.storeT_fits (σ : State C Γ) (hσ : RunFits C H σ) (op : BinOp) :
    {p : PrimTy} → (l : OpLoc C Γ p) → (v : p.Denote) → {o : Out C σ.H Γ} →
      l.storeT σ op v = .ok o → RunFits C H o.st
  | _, .local i, _, o, h => by
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact hσ.setLocal i trivial
  | _, .root r hr, v, o, h =>
    opStoreT_fits σ hσ op (SRef.ofRoot r hr) (show Solidity.KeysFit _ [] from trivial) v h
  | _, .field b f hf, v, o, h => by
    obtain ⟨ref, href, h⟩ := tbind_ok_inv h
    exact opStoreT_fits σ hσ op ref (Loc.resolveT_keysFit σ hσ.2 _ href) v h
  | _, .index it b i, v, o, h => by
    obtain ⟨ref, href, h⟩ := tbind_ok_inv h
    exact opStoreT_fits σ hσ op ref (Loc.resolveT_keysFit σ hσ.2 _ href) v h
  | _, .mfield .., v, o, h => by
    obtain ⟨a, _, h⟩ := tbind_ok_inv h
    exact opMemT_fits σ hσ op a v h
  | _, .mindex .., v, o, h => by
    obtain ⟨a, _, h⟩ := tbind_ok_inv h
    exact opMemT_fits σ hσ op a v h

theorem bumpStoreT_fits (σ : State C Γ) (hσ : RunFits C H σ) (op : IncDec)
    {p : PrimTy} (r : SRef C (.prim p)) (hk : r.KeysFit) {o : Out C σ.H Γ} {w : p.Denote}
    (h : bumpStoreT σ op r = .ok (o, w)) : RunFits C H o.st := by
  unfold bumpStoreT at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨new, _, h⟩ := tbind_ok_inv h
  obtain ⟨st, hst, h⟩ := tbind_ok_inv h
  cases h
  exact ⟨Storage.save_bnd hσ.1 r hk (by rw [SVal.erase_prim]; trivial) (TRes.ofOpt_ok hst), hσ.2⟩

theorem bumpMemT_fits (σ : State C Γ) (hσ : RunFits C H σ) (op : IncDec)
    {p : PrimTy} (a : MAddr σ.H (.prim p)) {o : Out C σ.H Γ} {w : p.Denote}
    (h : bumpMemT σ op a = .ok (o, w)) : RunFits C H o.st := by
  unfold bumpMemT at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  cases h
  exact ⟨hσ.1, hσ.2⟩

theorem OpLoc.bumpT_fits (σ : State C Γ) (hσ : RunFits C H σ) (op : IncDec) :
    {p : PrimTy} → (l : OpLoc C Γ p) → {o : Out C σ.H Γ} → {w : p.Denote} →
      l.bumpT σ op = .ok (o, w) → RunFits C H o.st
  | _, .local i, o, w, h => by
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact hσ.setLocal i trivial
  | _, .root r hr, o, w, h =>
    bumpStoreT_fits σ hσ op (SRef.ofRoot r hr) (show Solidity.KeysFit _ [] from trivial) h
  | _, .field b f hf, o, w, h => by
    obtain ⟨ref, href, h⟩ := tbind_ok_inv h
    exact bumpStoreT_fits σ hσ op ref (Loc.resolveT_keysFit σ hσ.2 _ href) h
  | _, .index it b i, o, w, h => by
    obtain ⟨ref, href, h⟩ := tbind_ok_inv h
    exact bumpStoreT_fits σ hσ op ref (Loc.resolveT_keysFit σ hσ.2 _ href) h
  | _, .mfield .., o, w, h => by
    obtain ⟨a, _, h⟩ := tbind_ok_inv h
    exact bumpMemT_fits σ hσ op a h
  | _, .mindex .., o, w, h => by
    obtain ⟨a, _, h⟩ := tbind_ok_inv h
    exact bumpMemT_fits σ hσ op a h

theorem fits_assign {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) :
    (fitsInv C).TKeeps (TRun.assign l r) := by
  intro σ o hσ h
  unfold TRun.assign at h
  obtain ⟨sv, hsv, h⟩ := tbind_ok_inv h
  obtain ⟨ref, href, h⟩ := tbind_ok_inv h
  obtain ⟨st, hst, h⟩ := tbind_ok_inv h
  cases h
  exact ⟨Storage.write_bnd hσ.1 ref (Loc.resolveT_keysFit σ hσ.2 l href)
    (Src.valueT_bnd σ hσ.1 r hsv) (TRes.ofOpt_ok hst), hσ.2⟩

theorem fits_rebind {R : RefTy} (i : Idx Γ (.alias R)) (r : ARhs C Γ R) :
    (fitsInv C).TKeeps (TRun.rebind i r) := by
  intro σ o hσ h
  unfold TRun.rebind at h
  obtain ⟨⟨st, ref⟩, he, h⟩ := tbind_ok_inv h
  cases h
  obtain ⟨hst, hk⟩ := ARhs.evalT_fits σ hσ r he
  exact RunInv.HoldsT.setLocal (σ := σ.withStorage st) ⟨hst, hσ.2⟩ i
    (SRef.keysFit_local hk)

theorem fits_assignLocal {p : PrimTy} (i : Idx Γ (.val p)) (r : Val C Γ p) :
    (fitsInv C).TKeeps (TRun.assignLocal i r) := by
  intro σ o hσ h
  unfold TRun.assignLocal at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  cases h
  exact hσ.setLocal i trivial

theorem fits_declLocal (p : PrimTy) (init : Option (Val C Γ p)) :
    (fitsInv C).TKeeps (TRun.declLocal p init) := by
  intro σ o hσ h
  unfold TRun.declLocal at h
  cases init with
  | none =>
    cases h
    exact hσ.push (t := .val p) trivial
  | some e =>
    dsimp only at h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact hσ.push (t := .val p) trivial

theorem fits_declStorage (R : RefTy) (init : Option (ARhs C Γ R)) :
    (fitsInv C).TKeeps (TRun.declStorage R init) := by
  intro σ o hσ h
  unfold TRun.declStorage at h
  cases init with
  | none =>
    cases h
    exact hσ.push (t := .alias R) (fun _ _ h => nomatch h)
  | some r =>
    obtain ⟨⟨st, ref⟩, he, h⟩ := tbind_ok_inv h
    cases h
    obtain ⟨hst, hk⟩ := ARhs.evalT_fits σ hσ r he
    exact RunInv.HoldsT.push (σ := σ.withStorage st) (t := .alias R) (v := some ref)
      ⟨hst, hσ.2⟩ (SRef.keysFit_local hk)

theorem fits_opAssign {p : PrimTy} (op : BinOp) (l : OpLoc C Γ p) (r : Val C Γ p) :
    (fitsInv C).TKeeps (TRun.opAssign op l r) := by
  intro σ o hσ h
  unfold TRun.opAssign at h
  obtain ⟨v, _, h⟩ := tbind_ok_inv h
  exact OpLoc.storeT_fits σ hσ op l v h

theorem fits_incDec {p : PrimTy} (op : IncDec) (l : OpLoc C Γ p) :
    (fitsInv C).TKeeps (TRun.incDec op l) := by
  intro σ o hσ h
  unfold TRun.incDec at h
  obtain ⟨⟨o', w⟩, hb, h⟩ := tbind_ok_inv h
  cases h
  exact OpLoc.bumpT_fits σ hσ op l hb

theorem fits_assignIncDec {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec) (l : OpLoc C Γ p) :
    (fitsInv C).TKeeps (TRun.assignIncDec i op l) := by
  intro σ o hσ h
  unfold TRun.assignIncDec at h
  obtain ⟨⟨o', w⟩, hb, h⟩ := tbind_ok_inv h
  cases h
  exact (OpLoc.bumpT_fits σ hσ op l hb).setLocal i trivial

theorem fits_push {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E)) :
    (fitsInv C).TKeeps (TRun.push b v) := by
  intro σ o hσ h
  unfold TRun.push at h
  obtain ⟨ref, href, h⟩ := tbind_ok_inv h
  have hk := SPath.resolveT_keysFit σ hσ.2 b href
  obtain ⟨x, hxb, h⟩ : ∃ x : Option (SVal E), (∀ x0, x = some x0 → x0.erase.bnd E) ∧
      (if σ.storage.full ref = true then Except.error THalt.exhausted
       else do
        let st ← TRes.ofOpt (σ.storage.push ref fun slot => some (x.getD slot))
        pure ({ st := σ.withStorage st, ext := List.prefix_refl _ } : Out C σ.H Γ)) = .ok o := by
    cases v with
    | none => exact ⟨none, (fun _ h => nomatch h), h⟩
    | some r =>
      dsimp only at h
      obtain ⟨sv, hsv, h⟩ := tbind_ok_inv h
      refine ⟨some sv.strip, (fun x0 hx0 => ?_), h⟩
      cases hx0
      rw [SVal.strip_erase]
      exact Semantics.SVal.strip_bnd (Src.valueT_bnd σ hσ.1 r hsv)
  split at h
  · exact nomatch h
  · rename_i hfull
    have hfull' : σ.storage.full ref = false := by simpa only [Bool.not_eq_true] using hfull
    obtain ⟨st, hst, h⟩ := tbind_ok_inv h
    cases h
    have he := Storage.pushAt_erase (σ := σ.globE) rfl ref
      (fun s => .ok ((x.map SVal.erase).getD s)) (fun slot => some (x.getD slot))
      (fun y => by cases x <;> rfl) (Or.inl hfull')
    rw [TRes.ofOpt_ok hst] at he
    refine ⟨bnd_pushAt hσ.1 (SRef.tyAt_erase ref) (SRef.keysFit_root hk)
      (Storage.len_of_full rfl ref hfull') (fun slot w hs hw => ?_) he, hσ.2⟩
    cases x with
    | none => cases hw; exact hs
    | some x0 => cases hw; exact hxb x0 rfl

theorem fits_pop {E : Ty} (b : SPath C Γ (.array E)) : (fitsInv C).TKeeps (TRun.pop b) := by
  intro σ o hσ h
  unfold TRun.pop at h
  obtain ⟨ref, href, h⟩ := tbind_ok_inv h
  obtain ⟨st, hst, h⟩ := tbind_ok_inv h
  cases h
  have he := Storage.popAt_erase (σ := σ.globE) rfl E.isMapping ref
  rw [TRes.ofOpt_ok hst] at he
  exact ⟨bnd_popAt hσ.1 (SRef.tyAt_erase ref)
    (SRef.keysFit_root (SPath.resolveT_keysFit σ hσ.2 b href)) he, hσ.2⟩

theorem fits_transfer (r a : Val C Γ .uint) : (fitsInv C).TKeeps (TRun.transfer r a) := by
  intro σ o hσ h
  unfold TRun.transfer at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  cases h
  exact ⟨hσ.1, hσ.2⟩

theorem fits_send (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) :
    (fitsInv C).TKeeps (TRun.send pv r a) := by
  intro σ o hσ h
  unfold TRun.send at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  cases h
  unfold sendT
  split
  · exact RunInv.HoldsT.setLocal (σ := σ.pay _ _) ⟨hσ.1, hσ.2⟩ pv trivial
  · exact RunInv.HoldsT.setLocal (σ := σ.pay _ _) ⟨hσ.1, hσ.2⟩ pv trivial
  · exact hσ.setLocal pv trivial

theorem fits_declMem (R : RefTy) (init : Option (MRhs C Γ R)) (hm : (Ty.ref R).mapFree = true) :
    (fitsInv C).TKeeps (TRun.declMem R init hm) := by
  intro σ o hσ h
  unfold TRun.declMem at h
  cases init with
  | none =>
    cases h
    exact (RunFits.adopt _ hσ).push (t := .mem R) trivial
  | some r =>
    obtain ⟨g, hg, h⟩ := tbind_ok_inv h
    cases h
    exact (MRhs.evalT_fits σ hσ r hg).push (t := .mem R) trivial

theorem fits_rebindMem {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) :
    (fitsInv C).TKeeps (TRun.rebindMem i r) := by
  intro σ o hσ h
  unfold TRun.rebindMem at h
  obtain ⟨g, hg, h⟩ := tbind_ok_inv h
  cases h
  exact (MRhs.evalT_fits σ hσ r hg).setLocal i trivial

theorem fits_assignFromMem {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) :
    (fitsInv C).TKeeps (TRun.assignFromMem l p) := by
  intro σ o hσ h
  unfold TRun.assignFromMem at h
  obtain ⟨m, _, h⟩ := tbind_ok_inv h
  obtain ⟨ref, href, h⟩ := tbind_ok_inv h
  obtain ⟨st, hst, h⟩ := tbind_ok_inv h
  cases h
  have hc := State.copyMem_erase σ m
  exact ⟨Storage.write_bnd hσ.1 ref (Loc.resolveT_keysFit σ hσ.2 l href)
    (SVal.erase_plain_bnd _ (copyMToSt_plain hc)) (TRes.ofOpt_ok hst), hσ.2⟩

theorem fits_assignMem {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) :
    (fitsInv C).TKeeps (TRun.assignMem l r) := by
  intro σ o hσ h
  unfold TRun.assignMem at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  cases h
  exact ⟨hσ.1, hσ.2⟩

theorem fits_delete {T : Ty} (l : Loc C Γ T) : (fitsInv C).TKeeps (TRun.delete l) := by
  intro σ o hσ h
  unfold TRun.delete at h
  obtain ⟨ref, href, h⟩ := tbind_ok_inv h
  obtain ⟨st, hst, h⟩ := tbind_ok_inv h
  cases h
  exact ⟨Storage.delete_bnd hσ.1 ref (Loc.resolveT_keysFit σ hσ.2 l href) (TRes.ofOpt_ok hst),
    hσ.2⟩

theorem fits_clearT (σ : State C Γ) (hσ : RunFits C H σ) :
    {T : Ty} → (a : MAddr σ.H T) → (hm : T.mapFree = true) → {o : Out C σ.H Γ} →
      TRun.clearT σ a hm = .ok o → RunFits C H o.st
  | .prim _, _, _, o, h => by
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact ⟨hσ.1, hσ.2⟩
  | .ref R, a, hm, o, h => by
    simp only [TRun.clearT] at h
    split at h
    · cases h
      exact RunFits.adopt _ hσ
    · exact nomatch h

theorem fits_deleteMem {T : Ty} (p : MPath C Γ T) : (fitsInv C).TKeeps (TRun.deleteMem p) := by
  intro σ o hσ h
  unfold TRun.deleteMem at h
  cases p with
  | var i _ =>
    cases h
    exact (RunFits.adopt _ hσ).setLocal i trivial
  | loc l =>
    obtain ⟨a, _, h⟩ := tbind_ok_inv h
    exact fits_clearT σ hσ a l.mapFree h

theorem fits_assignNew {R : RefTy} (l : NewLhs C Γ R) (n : Simple C Γ .uint)
    (hn : R.newArrOk = true) : (fitsInv C).TKeeps (TRun.assignNew l n hn) := by
  intro σ o hσ h
  unfold TRun.assignNew at h
  have hg : RunFits C (HTy.toHeapTy 0 σ.H)
      (σ.copyStToMG (newArrT R (n.evalT σ) hn) (RefTy.mapFree_of_newArrOk hn)).st :=
    RunFits.adopt _ hσ
  cases l with
  | store l =>
    obtain ⟨ref, href, h⟩ := tbind_ok_inv h
    obtain ⟨st, hst, h⟩ := tbind_ok_inv h
    cases h
    have hc := State.copyMem_erase
      (σ.copyStToMG (newArrT R (n.evalT σ) hn) (RefTy.mapFree_of_newArrOk hn)).st
      (σ.copyStToMG (newArrT R (n.evalT σ) hn) (RefTy.mapFree_of_newArrOk hn)).val
    exact ⟨Storage.write_bnd hg.1 ref (Loc.resolveT_keysFit _ hg.2 l href)
      (SVal.erase_plain_bnd _ (copyMToSt_plain hc)) (TRes.ofOpt_ok hst), hg.2⟩
  | mem l =>
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact ⟨hg.1, hg.2⟩

end Leaves

/-! ### Scopes and calls -/

mutual

/-- **Bounds, statement level**: a statement run from a bounded state, its
aliases along keys in range, ends in one. -/
theorem Stmt.keeps_fits : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → (fitsInv C).TKeeps (Stmt.runR s)
  | _, _, .assign l r => fits_assign l r
  | _, _, .rebind i r => fits_rebind i r
  | _, _, .assignLocal i r => fits_assignLocal i r
  | _, _, .declLocal p _ init => fits_declLocal p init
  | _, _, .declStorage R _ init => fits_declStorage R init
  | _, _, .opAssign op _ _ l r => fits_opAssign op l r
  | _, _, .incDec op _ l => fits_incDec op l
  | _, _, .assignIncDec i op _ l _ => fits_assignIncDec i op l
  | _, _, .push b v _ => fits_push b v
  | _, _, .pop b => fits_pop b
  | _, _, .transfer r a => fits_transfer r a
  | _, _, .send pv r a => fits_send pv r a
  | _, _, .declMem R _ init _ hm => fits_declMem R init hm
  | _, _, .rebindMem i r => fits_rebindMem i r
  | _, _, .assignFromMem l p => fits_assignFromMem l p
  | _, _, .assignMem l r => fits_assignMem l r
  | _, _, .delete l => fits_delete l
  | _, _, .deleteMem p _ => fits_deleteMem p
  | _, _, .assignNew l n hn => fits_assignNew l n hn
  | _, _, .ite c thn els =>
    RunInv.tkeeps_ite c thn.ext els.ext (Prog.keeps_fits thn) (Prog.keeps_fits els)
  | _, _, .require c => RunInv.tkeeps_require c
  | _, _, .assert c => RunInv.tkeeps_assert c
  | _, _, .revert => RunInv.tkeeps_revert
  | _, _, .call _ args ret body =>
    RunInv.tkeeps_call fitsInv.valMemOk args ret body.ext (Prog.keeps_fits body)
  | _, _, .tryCall call rets ok err code pnc other =>
    RunInv.tkeeps_tryCall fitsInv.valMemOk call rets ok.ext err.ext code pnc.ext other.ext
      (Prog.keeps_fits ok) (Prog.keeps_fits err) (Prog.keeps_fits pnc) (Prog.keeps_fits other)
  | _, _, .loop _ c body => RunInv.tkeeps_loop c body.ext (Prog.keeps_fits body)
  | _, _, .block body => RunInv.tkeeps_block body.ext (Prog.keeps_fits body)

/-- **Bounds, block level.** -/
theorem Prog.keeps_fits : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → (fitsInv C).TKeeps (Prog.runR P)
  | _, _, .nil => RunInv.tkeeps_nil
  | _, _, .cons s P => RunInv.tkeeps_seq (Stmt.keeps_fits s) (Prog.keeps_fits P)

end

/-! ## Reachable storage fits -/

/-- A contract starts bounded: each root at its type's default. -/
theorem BndStorage.init : BndStorage C C.initStorage := by
  intro r T v hr hv
  simp only [Contract.initStorage, lookupBy_map_snd, hr, Option.map_some,
    Option.some.injEq] at hv
  subst hv
  exact defaultForTy_bnd T

/-- **Reachable ⇒ bounded**: every storage a program reaches from the
contract's initial state has its keys in range and its arrays' slots below
`2^256`. -/
theorem reachable_bnd {st : List (Name × Semantics.SVal)} (h : Reachable C st) :
    BndStorage C st := by
  obtain ⟨Γ', P, o, hrun, rfl⟩ := h
  have hi : RunFits C (HTy.toHeapTy 0 (State.init C).H) (State.init C) := by
    refine ⟨?_, trivial⟩
    show BndStorage C (State.init C).storage.erase
    rw [State.init_storage_erase]
    exact BndStorage.init
  exact (Prog.keeps_fits P (State.init C) o hi hrun).1

/-- A bounded typed storage fits, its fixed sizes within `2^256`. -/
theorem Storage.erase_fits (hf : FixedFits C) (st : Storage C) (hb : BndStorage C st.erase) :
    FitsStorage C st.erase := by
  intro r T v hr hv
  have h2 : lookupBy r st.erase = some (st.get hr).erase := SFields.lookupBy_erase st hr
  rw [h2] at hv
  cases hv
  exact SVal.erase_fits _ (hf r T hr) (hb r T _ hr h2)

/-- **Reachable ⇒ fits** (decision 77, its conditional form): for a contract
whose fixed sizes are at most `2^256` (solc's "type too large for storage"),
every reachable storage has its words, keys and slots in range. -/
theorem reachable_fits (hf : FixedFits C) {st : List (Name × Semantics.SVal)}
    (h : Reachable C st) : FitsStorage C st := by
  have hb := reachable_bnd h
  obtain ⟨Γ', P, o, hrun, rfl⟩ := h
  exact Storage.erase_fits hf o.st.storage hb

/-- **The reachable storages, exactly, with no premise on the storage**: for
a contract whose types have well-formed defaults all the way down and whose
fixed sizes fit, a storage is reachable iff it is canonical, tight and fits. -/
theorem reachable_iff_fits (hnd : nodupKeysB C.vars = true)
    (hdeep : C.vars.all (·.2.okDeep) = true) (hf : FixedFits C)
    {st : List (Name × Semantics.SVal)} :
    Reachable C st ↔ CanonStorage C st ∧ TightStorage C st ∧ FitsStorage C st :=
  ⟨fun h => ⟨(reachable_shape hnd hdeep h).1, (reachable_shape hnd hdeep h).2, reachable_fits hf h⟩,
    fun ⟨hc, ht, hfs⟩ => (reachable_iff hnd hdeep hfs).2 ⟨hc, ht⟩⟩

/-- `Huge`'s one root is past solc's bound, so it is no counterexample to
`reachable_fits`. -/
theorem huge_not_fixedFits : ¬ FixedFits Huge := by
  intro hf
  have h := hf "big" _ rfl [] .uint (2 ^ 256 + 1) rfl
  omega

end Solidity
