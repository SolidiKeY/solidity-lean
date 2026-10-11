import Solidity.Typing.TypedRunInv
import Solidity.Semantics.Ends

/-!
# What every reachable state satisfies beyond its types

A typed state's erasure is well-typed by construction (`RunWT`,
`TypedWT.lean`).  This module asks what else the typed run keeps, which `SVal.hasTy` forgets — the
facts that let one refute that a well-typed storage is reachable at all.
`SVal.canon` adds exactly those:

- a struct carries **exactly** its declared members, in declared order
  (`hasTy` checks only the members present): `defaultForTy` creates them
  all, and a write replaces a member in place (`setBy` on a present key);
- a mapping's keys are **unique** (they only grow by `setBy`), and its
  default is **the** type's default (`save` and `delete` never touch it);
- the slots a `pop` recycled are canonical too: `pop` clears the element
  (`defaultOf`) and `push` hands it back (`pushSlot`).

A memory object is copied back into storage by `assignFromMem`, so the heap
has to keep the first fact as well: an object the store typing claims at a
struct has exactly its members (`CanonHeap`).  Then no memory object of a
struct with a mapping member can exist (the member would need a claim at a
mapping type, which no object satisfies), and a copy back never produces a
struct missing its mapping.

The heap's fact holds by construction: a typed heap's struct object is
its members, all of them (`State.erase_canonHeap`).  `Prog.run_canon` is the
preservation theorem for the storage's (the typed run keeps `canonInv`,
canonical storage on the erasure, each step through what it erases to from a
state well-typed and with a canonical heap by construction,
`TypedRunInv.lean`), `reachable_canon` its
corollary from a contract's initial state (`Reachable`: a scoped program
`Prog C [] Γ'` runs there by the typed interpreter), and the two
refutations the removed untyped layer left as `sorry` follow: a storage whose
mapping default is not the default (`map_default_not_reachable`) and one
whose struct misses a member (`struct_missing_field_not_reachable`) are
well-typed and not `Reachable`.

The converse is `Constructibility.lean`: canonical is not enough, and
canonical and tight (`SVal.tight`) is exactly reachable for a storage that
fits (`reachable_iff`), with no premise on the storage under `FixedFits`
(`reachable_iff_fits`, `Typing/Fits.lean`).
-/

namespace Solidity

open Semantics
open SemanticsProperties (lookupBy_setBy_self lookupBy_setBy_ne HeapWellFormed
  lookupBy_eq_some_mem)

variable {C : Contract}

/-! ## The canonical values -/

/-- `v` is a canonical value of type `T`: well-typed, with every struct
carrying exactly its declared members, every mapping unique keys and the
default default, recursively (recycled array slots included). -/
def Semantics.SVal.canon : Semantics.SVal → Ty → Prop
  | SVal.int _, Ty.int => True
  | SVal.int _, Ty.uint => True
  | SVal.bool _, Ty.bool => True
  | Semantics.SVal.struct fields, Ty.ref (RefTy.struct s) =>
      fields.map (·.1) = (structDef s).map (·.1) ∧ canonFields s fields
  | Semantics.SVal.array elems shadow fx, Ty.ref (RefTy.array E) =>
      fx = false ∧ canonElems E elems ∧ canonElems E shadow
  | Semantics.SVal.array elems shadow fx, Ty.ref (RefTy.fixed E n) =>
      fx = true ∧ elems.length = n ∧ canonElems E elems ∧ canonElems E shadow
  | Semantics.SVal.map entries dflt, Ty.ref (RefTy.mapping _ V) =>
      nodupKeysB entries = true ∧ canonEntries V entries ∧ dflt = defaultForTy V ∧ dflt.canon V
  | _, _ => False
where
  canonFields (s : Name) : List (Name × Semantics.SVal) → Prop
    | [] => True
    | (n, v) :: rest =>
        (match lookupBy n (structDef s) with
         | some T => v.canon T
         | none => False) ∧ canonFields s rest
  canonElems (E : Ty) : List Semantics.SVal → Prop
    | [] => True
    | v :: rest => v.canon E ∧ canonElems E rest
  canonEntries (V : Ty) : List (Int × Semantics.SVal) → Prop
    | [] => True
    | (_, v) :: rest => v.canon V ∧ canonEntries V rest

open Semantics.SVal.canon (canonFields canonElems canonEntries)

/-! ## List lemmas -/

section Lists

/-- `alice.age = 3` keeps `alice`'s members, in order. -/
theorem map_fst_setBy_of_present [DecidableEq κ] {k : κ} {v : α} :
    ∀ {l : List (κ × α)}, (lookupBy k l).isSome = true →
      (setBy k v l).map (·.1) = l.map (·.1)
  | [], h => by simp [lookupBy] at h
  | (k', v') :: rest, h => by
    by_cases hk : k = k'
    · subst hk; simp [setBy]
    · simp only [lookupBy, if_neg hk] at h
      simp [setBy, hk, map_fst_setBy_of_present h]

/-- A declared member is present in a struct that has exactly its members. -/
theorem lookupBy_isSome_of_map_fst {κ α β : Type} [DecidableEq κ] {k : κ} :
    ∀ {l : List (κ × α)} {l' : List (κ × β)}, l.map (·.1) = l'.map (·.1) →
      (lookupBy k l').isSome = true → (lookupBy k l).isSome = true
  | [], [], _, h => by simp [lookupBy] at h
  | [], _ :: _, he, _ => by simp at he
  | _ :: _, [], he, _ => by simp at he
  | (a, _) :: rest, (b, _) :: rest', he, h => by
    simp only [List.map_cons, List.cons.injEq] at he
    obtain ⟨rfl, he⟩ := he
    by_cases hk : k = a
    · simp [lookupBy, hk]
    · simp only [lookupBy, if_neg hk] at h ⊢
      exact lookupBy_isSome_of_map_fst he h

/-- A member of a canonical `Person` is canonical at its declared type: `alice.age`. -/
theorem canonFields_lookup {s : Name} {fields : List (Name × Semantics.SVal)} {n : Name} {v : Semantics.SVal}
    (h : canonFields s fields) (hl : lookupBy n fields = some v) :
    ∃ T, lookupBy n (structDef s) = some T ∧ v.canon T := by
  induction fields with
  | nil => simp [lookupBy] at hl
  | cons p rest ih =>
    obtain ⟨n', v'⟩ := p
    simp only [canonFields] at h
    by_cases hn : n = n'
    · subst hn
      simp [lookupBy] at hl
      subst hl
      revert h
      cases hd : lookupBy n (structDef s) with
      | none => intro h; exact h.1.elim
      | some T => intro h; exact ⟨T, rfl, h.1⟩
    · simp [lookupBy, hn] at hl
      exact ih h.2 hl

/-- `alice.age = 3` keeps `alice`'s members canonical. -/
theorem canonFields_setBy {s : Name} {fields : List (Name × Semantics.SVal)} {n : Name} {w : Semantics.SVal}
    {T : Ty}
    (h : canonFields s fields) (hd : lookupBy n (structDef s) = some T) (hw : w.canon T) :
    canonFields s (setBy n w fields) := by
  induction fields with
  | nil => simp [setBy, canonFields, hd, hw]
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    simp only [canonFields] at h
    by_cases hn : n = k
    · subst hn; simp [setBy, canonFields, hd, hw, h.2]
    · simp only [setBy, if_neg hn, canonFields]; exact ⟨h.1, ih h.2⟩

/-- An element of a canonical `uint[]` is canonical. -/
theorem canonElems_mem {E : Ty} {elems : List Semantics.SVal} {v : Semantics.SVal} (h : canonElems E elems)
    (hm : v ∈ elems) : v.canon E := by
  induction elems with
  | nil => cases hm
  | cons w rest ih =>
    cases hm with
    | head => exact h.1
    | tail _ hm => exact ih h.2 hm

/-- Elements canonical one by one make a canonical `uint[]`. -/
theorem canonElems_of_forall {E : Ty} {elems : List Semantics.SVal} (h : ∀ v ∈ elems, v.canon E) :
    canonElems E elems := by
  induction elems with
  | nil => trivial
  | cons v rest ih =>
    exact ⟨h v List.mem_cons_self, ih fun w hw => h w (List.mem_cons_of_mem _ hw)⟩

/-- An entry of a canonical mapping is canonical: `balances[7]`. -/
theorem canonEntries_lookup {V : Ty} {entries : List (Int × Semantics.SVal)} {i : Int} {v : Semantics.SVal}
    (h : canonEntries V entries) (hl : lookupBy i entries = some v) : v.canon V := by
  induction entries with
  | nil => simp [lookupBy] at hl
  | cons p rest ih =>
    obtain ⟨j, w⟩ := p
    by_cases hi : i = j
    · subst hi; simp [lookupBy] at hl; subst hl; exact h.1
    · simp [lookupBy, hi] at hl; exact ih h.2 hl

/-- `balances[7] = 1` keeps the entries canonical. -/
theorem canonEntries_setBy {V : Ty} {entries : List (Int × Semantics.SVal)} {i : Int} {w : Semantics.SVal}
    (h : canonEntries V entries) (hw : w.canon V) : canonEntries V (setBy i w entries) := by
  induction entries with
  | nil => simp [setBy, canonEntries, hw]
  | cons p rest ih =>
    obtain ⟨j, v⟩ := p
    by_cases hi : i = j
    · subst hi; simp [setBy, canonEntries, hw, h.2]
    · simp only [setBy, if_neg hi, canonEntries]; exact ⟨h.1, ih h.2⟩

/-- `values[i] = 3` keeps the elements canonical. -/
theorem canonElems_set {E : Ty} {elems : List Semantics.SVal} {i : Nat} {w : Semantics.SVal}
    (h : canonElems E elems) (hw : w.canon E) : canonElems E (elems.set i w) := by
  induction elems generalizing i with
  | nil => exact h
  | cons v rest ih =>
    cases i with
    | zero => exact ⟨hw, h.2⟩
    | succ n => exact ⟨h.1, ih h.2⟩

/-- `values.push(3)` appends a canonical element. -/
theorem canonElems_append {E : Ty} {xs ys : List Semantics.SVal} (hx : canonElems E xs)
    (hy : canonElems E ys) : canonElems E (xs ++ ys) := by
  induction xs with
  | nil => exact hy
  | cons v rest ih => exact ⟨hx.1, ih hx.2⟩

/-- The live elements of a canonical slot list are canonical. -/
theorem canonElems_take {E : Ty} {xs : List Semantics.SVal} (n : Nat) (h : canonElems E xs) :
    canonElems E (xs.take n) :=
  canonElems_of_forall fun _ hv => canonElems_mem h (List.mem_of_mem_take hv)

/-- The slots past the end of a canonical slot list are canonical. -/
theorem canonElems_drop {E : Ty} {xs : List Semantics.SVal} (n : Nat) (h : canonElems E xs) :
    canonElems E (xs.drop n) :=
  canonElems_of_forall fun _ hv => canonElems_mem h (List.mem_of_mem_drop hv)

end Lists

/-! ## Shapes -/

section Shapes

/-- A canonical `Person` is a struct with `Person`'s members. -/
theorem canon_struct {v : Semantics.SVal} {s : Name} (h : v.canon (.ref (.struct s))) :
    ∃ fields, v = .struct fields ∧ fields.map (·.1) = (structDef s).map (·.1) ∧
      canonFields s fields := by
  cases v with
  | prim p => cases p <;> exact h.elim
  | struct fields => exact ⟨fields, rfl, h⟩
  | array _ _ _ => exact h.elim
  | map _ _ => exact h.elim

/-- A canonical `uint[]` is an array of canonical numbers, recycled slots
included. -/
theorem canon_array {v : Semantics.SVal} {E : Ty} (h : v.canon (.ref (.array E))) :
    ∃ elems shadow, v = .array elems shadow false ∧ canonElems E elems ∧ canonElems E shadow := by
  cases v with
  | prim p => cases p <;> exact h.elim
  | struct _ => exact h.elim
  | array elems shadow fx => obtain ⟨rfl, h⟩ := h; exact ⟨elems, shadow, rfl, h⟩
  | map _ _ => exact h.elim

/-- A canonical `uint[3]` is a marked array of three canonical numbers. -/
theorem canon_fixed {v : Semantics.SVal} {E : Ty} {n : Nat} (h : v.canon (.ref (.fixed E n))) :
    ∃ elems shadow, v = .array elems shadow true ∧ elems.length = n ∧ canonElems E elems ∧
      canonElems E shadow := by
  cases v with
  | prim p => cases p <;> exact h.elim
  | struct _ => exact h.elim
  | array elems shadow fx => obtain ⟨rfl, h⟩ := h; exact ⟨elems, shadow, rfl, h⟩
  | map _ _ => exact h.elim

/-- A canonical `mapping(uint => uint)` has unique keys and the default
default. -/
theorem canon_map {v : Semantics.SVal} {K V : Ty} (h : v.canon (.ref (.mapping K V))) :
    ∃ entries dflt, v = .map entries dflt ∧ nodupKeysB entries = true ∧
      canonEntries V entries ∧ dflt = defaultForTy V ∧ dflt.canon V := by
  cases v with
  | prim p => cases p <;> exact h.elim
  | struct _ => exact h.elim
  | array _ _ _ => exact h.elim
  | map entries dflt => exact ⟨entries, dflt, rfl, h⟩

/-- On a primitive type canonical is well-typed: `3` at `uint`. -/
theorem canon_prim_iff {v : Semantics.SVal} {p : PrimTy} :
    v.canon (.prim p) ↔ v.hasTy (.prim p) = true := by
  cases v with
  | prim pv => cases p <;> cases pv <;> simp [SVal.canon, SVal.hasTy]
  | struct _ => cases p <;> simp [SVal.canon, SVal.hasTy]
  | array _ _ _ => cases p <;> simp [SVal.canon, SVal.hasTy]
  | map _ _ => cases p <;> simp [SVal.canon, SVal.hasTy]

end Shapes

/-! ## Reads, writes, defaults -/

/-- What `find` reaches in a canonical value is canonical: `alice.account`
of a canonical `alice` has both `Account` members. -/
theorem find_canon : ∀ {segs : List Seg} {v : Semantics.SVal} {T T' : Ty} {w : Semantics.SVal},
    v.canon T → tyAtSegs T segs = some T' → v.find segs = .ok w → w.canon T'
  | [], v, T, T', w, h, hs, hf => by
    simp only [tyAtSegs, Option.some.injEq] at hs
    subst hs
    simp only [Semantics.SVal.find, Except.ok.injEq] at hf
    subst hf; exact h
  | seg :: rest, v, T, T', w, h, hs, hf => by
    simp only [tyAtSegs] at hs
    cases hseg : segTy T seg with
    | none => rw [hseg] at hs; exact nomatch hs
    | some Surface.Tm =>
      rw [hseg] at hs
      cases seg with
      | field n =>
        cases T with
        | prim _ => simp [segTy] at hseg
        | ref r =>
          cases r with
          | struct s =>
            obtain ⟨fields, rfl, -, hfs⟩ := canon_struct h
            simp only [segTy] at hseg
            simp only [Semantics.SVal.find] at hf
            split at hf
            · rename_i v' hl
              obtain ⟨Tf, hd, hv⟩ := canonFields_lookup hfs hl
              rw [hseg] at hd; cases hd
              exact find_canon hv hs hf
            · exact nomatch hf
          | array _ => simp [segTy] at hseg
          | fixed _ _ => simp [segTy] at hseg
          | mapping _ _ => simp [segTy] at hseg
      | «at» i =>
        cases T with
        | prim _ => simp [segTy] at hseg
        | ref r =>
          cases r with
          | struct _ => simp [segTy] at hseg
          | array E =>
            obtain ⟨elems, sh, rfl, he, hsh⟩ := canon_array h
            simp only [segTy, Option.some.injEq] at hseg
            subst hseg
            simp only [Semantics.SVal.find] at hf
            split at hf
            · exact find_canon (canonElems_mem (canonElems_append he hsh) (List.get_mem _ _)) hs hf
            · exact nomatch hf
          | fixed E _ =>
            obtain ⟨elems, sh, rfl, -, he, hsh⟩ := canon_fixed h
            simp only [segTy, Option.some.injEq] at hseg
            subst hseg
            simp only [Semantics.SVal.find] at hf
            split at hf
            · exact find_canon (canonElems_mem (canonElems_append he hsh) (List.get_mem _ _)) hs hf
            · exact nomatch hf
          | mapping K V =>
            obtain ⟨es, d, rfl, -, hes, -, hd⟩ := canon_map h
            simp only [segTy, Option.some.injEq] at hseg
            subst hseg
            simp only [Semantics.SVal.find] at hf
            split at hf
            · rename_i v' hl
              exact find_canon (canonEntries_lookup hes hl) hs hf
            · exact find_canon hd hs hf

/-- Saving a canonical value at a typed path keeps the tree canonical:
`alice.age = 3` leaves `alice` with both members, `balances[7] = 1` adds
key `7` once. -/
theorem save_canon : ∀ {segs : List Seg} {v : Semantics.SVal} {T T' : Ty} {new w : Semantics.SVal},
    v.canon T → tyAtSegs T segs = some T' → new.canon T' → v.save segs new = .ok w →
      w.canon T
  | [], v, T, T', new, w, _, hs, hn, hf => by
    simp only [tyAtSegs, Option.some.injEq] at hs
    subst hs
    simp only [Semantics.SVal.save, Except.ok.injEq] at hf
    subst hf; exact hn
  | seg :: rest, v, T, T', new, w, h, hs, hn, hf => by
    simp only [tyAtSegs] at hs
    cases hseg : segTy T seg with
    | none => rw [hseg] at hs; exact nomatch hs
    | some Surface.Tm =>
      rw [hseg] at hs
      cases seg with
      | field n =>
        cases T with
        | prim _ => simp [segTy] at hseg
        | ref r =>
          cases r with
          | struct s =>
            obtain ⟨fields, rfl, hnames, hfs⟩ := canon_struct h
            simp only [segTy] at hseg
            simp only [Semantics.SVal.save] at hf
            split at hf
            · rename_i old hl
              obtain ⟨up, hup, hf⟩ := bind_ok_inv hf
              cases hf
              obtain ⟨Tf, hd, hv⟩ := canonFields_lookup hfs hl
              rw [hseg] at hd; cases hd
              refine ⟨?_, canonFields_setBy hfs hseg (save_canon hv hs hn hup)⟩
              rw [map_fst_setBy_of_present (by simp [hl])]
              exact hnames
            · exact nomatch hf
          | array _ => simp [segTy] at hseg
          | fixed _ _ => simp [segTy] at hseg
          | mapping _ _ => simp [segTy] at hseg
      | «at» i =>
        cases T with
        | prim _ => simp [segTy] at hseg
        | ref r =>
          cases r with
          | struct _ => simp [segTy] at hseg
          | array E =>
            obtain ⟨elems, sh, rfl, he, hsh⟩ := canon_array h
            simp only [segTy, Option.some.injEq] at hseg
            subst hseg
            simp only [Semantics.SVal.save] at hf
            split at hf
            · obtain ⟨up, hup, hf⟩ := bind_ok_inv hf
              cases hf
              have hall := canonElems_append he hsh
              have hset := canonElems_set (i := i.toNat) hall
                (save_canon (canonElems_mem hall (List.get_mem _ _)) hs hn hup)
              exact ⟨rfl, canonElems_take _ hset, canonElems_drop _ hset⟩
            · exact nomatch hf
          | fixed E n =>
            obtain ⟨elems, sh, rfl, hlen, he, hsh⟩ := canon_fixed h
            simp only [segTy, Option.some.injEq] at hseg
            subst hseg
            simp only [Semantics.SVal.save] at hf
            split at hf
            · obtain ⟨up, hup, hf⟩ := bind_ok_inv hf
              cases hf
              have hall := canonElems_append he hsh
              have hset := canonElems_set (i := i.toNat) hall
                (save_canon (canonElems_mem hall (List.get_mem _ _)) hs hn hup)
              exact ⟨rfl, by simp [hlen], canonElems_take _ hset, canonElems_drop _ hset⟩
            · exact nomatch hf
          | mapping K V =>
            obtain ⟨es, d, rfl, hnd, hes, hdd, hd⟩ := canon_map h
            simp only [segTy, Option.some.injEq] at hseg
            subst hseg
            simp only [Semantics.SVal.save] at hf
            split at hf
            · rename_i old hl
              obtain ⟨up, hup, hf⟩ := bind_ok_inv hf
              cases hf
              exact ⟨nodupKeysB_setBy hnd,
                canonEntries_setBy hes (save_canon (canonEntries_lookup hes hl) hs hn hup),
                hdd, hd⟩
            · obtain ⟨up, hup, hf⟩ := bind_ok_inv hf
              cases hf
              exact ⟨nodupKeysB_setBy hnd, canonEntries_setBy hes (save_canon hd hs hn hup),
                hdd, hd⟩

mutual

/-- `delete` keeps a value canonical: members reset in place, arrays
emptied, mappings untouched. -/
theorem Semantics.SVal.defaultOf_canon : ∀ {v : Semantics.SVal} {T : Ty}, v.canon T → v.defaultOf.canon T
  | .prim (.int _), .prim .int, _ | .prim (.int _), .prim .uint, _
  | .prim (.bool _), .prim .bool, _ => trivial
  | .struct fields, .ref (.struct s), h => by
    obtain ⟨hn, hf⟩ := h
    refine ⟨?_, Semantics.SVal.defaultOfFields_canon hf⟩
    rw [← hn]; exact defaultOfFields_names fields
  | .array _ _ false, .ref (.array _), h =>
    ⟨rfl, trivial, canonElems_append (Semantics.SVal.defaultOfElems_canon h.2.1) h.2.2⟩
  | .array elems _ true, .ref (.fixed _ _), h =>
    ⟨rfl, (SVal.defaultOfElems_length elems).trans h.2.1, Semantics.SVal.defaultOfElems_canon h.2.2.1,
      h.2.2.2⟩
  | .array _ _ true, .ref (.array _), h => nomatch h.1
  | .array _ _ false, .ref (.fixed _ _), h => nomatch h.1
  | .map _ _, .ref (.mapping _ _), h => h
  | .prim (.int _), .prim .bool, h | .prim (.bool _), .prim .int, h
  | .prim (.bool _), .prim .uint, h => h.elim
  | .prim (.int _), .ref _, h | .prim (.bool _), .ref _, h => h.elim
  | .struct _, .prim _, h | .array _ _ _, .prim _, h | .map _ _, .prim _, h => h.elim
  | .struct _, .ref (.array _), h | .struct _, .ref (.mapping _ _), h
  | .struct _, .ref (.fixed _ _), h => h.elim
  | .array _ _ _, .ref (.struct _), h | .array _ _ _, .ref (.mapping _ _), h => h.elim
  | .map _ _, .ref (.struct _), h | .map _ _, .ref (.array _), h
  | .map _ _, .ref (.fixed _ _), h => h.elim

/-- `delete alice` resets each member in place. -/
theorem Semantics.SVal.defaultOfFields_canon {s : Name} :
    ∀ {fields : List (Name × Semantics.SVal)}, canonFields s fields →
      canonFields s (SVal.defaultOf.defaultOfFields fields)
  | [], _ => trivial
  | (n, v) :: rest, h => by
    refine ⟨?_, Semantics.SVal.defaultOfFields_canon h.2⟩
    have h1 := h.1
    revert h1
    cases lookupBy n (structDef s) with
    | none => exact fun h => h.elim
    | some T => exact fun h => Semantics.SVal.defaultOf_canon h

/-- `delete values` clears each element in place. -/
theorem Semantics.SVal.defaultOfElems_canon {E : Ty} :
    ∀ {elems : List Semantics.SVal}, canonElems E elems →
      canonElems E (SVal.defaultOf.defaultOfElems elems)
  | [], _ => trivial
  | _ :: _, h => ⟨Semantics.SVal.defaultOf_canon h.1, Semantics.SVal.defaultOfElems_canon h.2⟩

/-- `delete` keeps the member names. -/
theorem defaultOfFields_names : ∀ (fields : List (Name × Semantics.SVal)),
    (SVal.defaultOf.defaultOfFields fields).map (·.1) = fields.map (·.1)
  | [] => rfl
  | (n, _) :: rest => by
    simp only [SVal.defaultOf.defaultOfFields, List.map_cons, defaultOfFields_names rest]

end

/-- A fresh default keeps its declared member names. -/
theorem defaultForFields_names : ∀ l : List (Name × Ty),
    (defaultForFields l).map (·.1) = l.map (·.1)
  | [] => by simp [defaultForFields]
  | (n, t) :: rest => by simp [defaultForFields, defaultForFields_names rest]

/-- A fresh default is canonical, under `defaultOk`. -/
theorem defaultForTy_canon_of : ∀ {T : Ty}, defaultOk T = true → (defaultForTy T).canon T := by
  intro T
  induction T using defaultForTy.induct
    (motive2 := fun l => ∀ (s : Name), defaultOkFields s l = true →
      canonFields s (defaultForFields l)) with
  | case1 => intro _; simp [defaultForTy, SVal.canon]
  | case2 => intro _; simp [defaultForTy, SVal.canon]
  | case3 => intro _; simp [defaultForTy, SVal.canon]
  | case4 name ih =>
    intro h
    simp only [defaultOk] at h
    simp only [defaultForTy]
    exact ⟨defaultForFields_names _, ih name h⟩
  | case5 elem => intro _; simp [defaultForTy, SVal.canon, canonElems]
  | case6 elem n ih =>
    intro h
    simp only [defaultOk] at h
    simp only [defaultForTy, SVal.canon, List.length_replicate]
    refine ⟨trivial, trivial, ?_, trivial⟩
    induction n with
    | zero => trivial
    | succ k ihk => exact ⟨ih h, ihk⟩
  | case7 key value ih =>
    intro h
    simp only [defaultOk] at h
    simp only [defaultForTy]
    exact ⟨rfl, trivial, rfl, ih h⟩
  | case8 => simp [defaultForFields, canonFields]
  | case9 n t rest iht ihrest =>
    rename_i s h
    simp only [defaultOkFields, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hok, hlook⟩, hrest⟩ := h
    simp only [defaultForFields, canonFields, hlook]
    exact ⟨iht hok, ihrest s hrest⟩

/-- **A fresh default is canonical**: `Person memory m;` and
`values.push();` start from one, and so does every root. -/
theorem defaultForTy_canon {T : Ty} : (defaultForTy T).canon T :=
  defaultForTy_canon_of (defaultOk_true T)

/-- The slot `persons.push();` lands on is canonical, and so are the
recycled slots left. -/
theorem pushSlot_canon {E : Ty} {shadow : List Semantics.SVal} (hsh : canonElems E shadow) :
    (Semantics.pushSlot E shadow).1.canon E ∧ canonElems E (Semantics.pushSlot E shadow).2 := by
  cases shadow with
  | nil => exact ⟨defaultForTy_canon, trivial⟩
  | cons c rest =>
    refine ⟨?_, hsh.2⟩
    simp only [Semantics.pushSlot]
    split
    · exact defaultForTy_canon
    · exact hsh.1

/-! ## Copies

A copy lays the source over what is there (`SVal.overlay`); onto fresh slots
it lands stripped of what is past its arrays' ends (`SVal.strip`). -/

/-- Stripping keeps the member names. -/
theorem stripFields_names : ∀ (fields : List (Name × Semantics.SVal)),
    (SVal.strip.stripFields fields).map (·.1) = fields.map (·.1)
  | [] => rfl
  | (n, _) :: rest => by
    simp only [SVal.strip.stripFields, List.map_cons, stripFields_names rest]

/-- A copy takes the source's member names. -/
theorem overlayFields_names (ofs : List (Name × Semantics.SVal)) : ∀ (nfs : List (Name × Semantics.SVal)),
    (SVal.overlay.overlayFields ofs nfs).map (·.1) = nfs.map (·.1)
  | [] => rfl
  | (n, _) :: rest => by
    simp only [SVal.overlay.overlayFields, List.map_cons, overlayFields_names ofs rest]

mutual

/-- A value laid on fresh slots stays canonical. -/
theorem Semantics.SVal.strip_canon : ∀ {v : Semantics.SVal} {T : Ty}, v.canon T → v.strip.canon T
  | .prim _, _, h => by simpa only [Semantics.SVal.strip] using h
  | .struct fields, .ref (.struct _), h =>
    ⟨(stripFields_names fields).trans h.1, Semantics.SVal.stripFields_canon h.2⟩
  | .array _ _ _, .ref (.array _), h => ⟨h.1, Semantics.SVal.stripElems_canon h.2.1, trivial⟩
  | .array elems _ _, .ref (.fixed _ _), h =>
    ⟨h.1, (SVal.stripElems_length' elems).trans h.2.1, Semantics.SVal.stripElems_canon h.2.2.1, trivial⟩
  | .map _ _, .ref (.mapping _ _), h => h
  | .struct _, .prim p, h | .array _ _ _, .prim p, h | .map _ _, .prim p, h => by
    cases p <;> exact h.elim
  | .struct _, .ref (.array _), h | .struct _, .ref (.mapping _ _), h
  | .struct _, .ref (.fixed _ _), h => h.elim
  | .array _ _ _, .ref (.struct _), h | .array _ _ _, .ref (.mapping _ _), h => h.elim
  | .map _ _, .ref (.struct _), h | .map _ _, .ref (.array _), h
  | .map _ _, .ref (.fixed _ _), h => h.elim

theorem Semantics.SVal.stripFields_canon {s : Name} :
    ∀ {fields : List (Name × Semantics.SVal)}, canonFields s fields →
      canonFields s (SVal.strip.stripFields fields)
  | [], _ => trivial
  | (n, v) :: rest, h => by
    refine ⟨?_, Semantics.SVal.stripFields_canon h.2⟩
    have h1 := h.1
    revert h1
    cases lookupBy n (structDef s) with
    | none => exact fun h => h.elim
    | some T => exact fun h => Semantics.SVal.strip_canon h

theorem Semantics.SVal.stripElems_canon {E : Ty} :
    ∀ {elems : List Semantics.SVal}, canonElems E elems → canonElems E (SVal.strip.stripElems elems)
  | [], _ => trivial
  | _ :: _, h => ⟨Semantics.SVal.strip_canon h.1, Semantics.SVal.stripElems_canon h.2⟩

end

mutual

/-- **A copy keeps storage canonical**: `bob = alice;` over a `Person`
leaves a `Person`, each member laid over the old one. -/
theorem Semantics.SVal.overlay_canon {old new : Semantics.SVal} {T : Ty} (ho : old.canon T) (hn : new.canon T) :
    (old.overlay new).canon T := by
  match new with
  | .prim p => cases old <;> simpa [Semantics.SVal.overlay, Semantics.SVal.strip] using hn
  | .struct nfs =>
      cases old with
      | struct ofs =>
          cases T with
          | prim p => cases p <;> exact hn.elim
          | ref r =>
              cases r with
              | struct s =>
                  exact ⟨(overlayFields_names ofs nfs).trans hn.1,
                    Semantics.SVal.overlayFields_canon ho.2 hn.2⟩
              | array _ => exact hn.elim
              | fixed _ _ => exact hn.elim
              | mapping _ _ => exact hn.elim
      | prim _ => simp only [Semantics.SVal.overlay]; exact SVal.strip_canon hn
      | array _ _ _ => simp only [Semantics.SVal.overlay]; exact SVal.strip_canon hn
      | map _ _ => simp only [Semantics.SVal.overlay]; exact SVal.strip_canon hn
  | .array nel nsh nfx =>
      cases old with
      | array oel osh ofx =>
          cases T with
          | prim p => cases p <;> exact hn.elim
          | ref r =>
              cases r with
              | array E =>
                  exact ⟨hn.1, Semantics.SVal.overlayElems_canon (canonElems_append ho.2.1 ho.2.2) hn.2.1,
                    canonElems_append (SVal.defaultOfElems_canon (canonElems_drop _ ho.2.1))
                      (canonElems_drop _ ho.2.2)⟩
              | fixed E n =>
                  exact ⟨hn.1, (SVal.overlayElems_length _ nel).trans hn.2.1,
                    Semantics.SVal.overlayElems_canon (canonElems_append ho.2.2.1 ho.2.2.2) hn.2.2.1,
                    canonElems_append (SVal.defaultOfElems_canon (canonElems_drop _ ho.2.2.1))
                      (canonElems_drop _ ho.2.2.2)⟩
              | struct _ => exact hn.elim
              | mapping _ _ => exact hn.elim
      | prim _ => simp only [Semantics.SVal.overlay]; exact SVal.strip_canon hn
      | struct _ => simp only [Semantics.SVal.overlay]; exact SVal.strip_canon hn
      | map _ _ => simp only [Semantics.SVal.overlay]; exact SVal.strip_canon hn
  | .map ne nd =>
      cases old with
      | map oe od => simpa only [Semantics.SVal.overlay] using ho
      | prim _ => simp only [Semantics.SVal.overlay]; exact SVal.strip_canon hn
      | struct _ => simp only [Semantics.SVal.overlay]; exact SVal.strip_canon hn
      | array _ _ _ => simp only [Semantics.SVal.overlay]; exact SVal.strip_canon hn

theorem Semantics.SVal.overlayFields_canon {s : Name} {ofs nfs : List (Name × Semantics.SVal)}
    (ho : canonFields s ofs) (hn : canonFields s nfs) :
    canonFields s (SVal.overlay.overlayFields ofs nfs) := by
  match nfs with
  | [] => trivial
  | (n, v) :: rest =>
      refine ⟨?_, Semantics.SVal.overlayFields_canon ho hn.2⟩
      have h1 := hn.1
      revert h1
      cases hdef : lookupBy n (structDef s) with
      | none => exact fun h => h.elim
      | some T =>
          intro h1
          cases hl : lookupBy n ofs with
          | none => exact SVal.strip_canon h1
          | some o =>
              obtain ⟨T', hd', hoc⟩ := canonFields_lookup ho hl
              rw [hdef] at hd'
              cases hd'
              exact Semantics.SVal.overlay_canon hoc h1

theorem Semantics.SVal.overlayElems_canon {E : Ty} {olds news : List Semantics.SVal}
    (ho : canonElems E olds) (hn : canonElems E news) :
    canonElems E (SVal.overlay.overlayElems olds news) := by
  match olds, news with
  | o :: os, v :: rest => exact ⟨Semantics.SVal.overlay_canon ho.1 hn.1, Semantics.SVal.overlayElems_canon ho.2 hn.2⟩
  | [], rest => simpa only [SVal.overlay.overlayElems] using SVal.stripElems_canon hn
  | _ :: _, [] => trivial

end

/-! ## The heap keeps struct members -/

/-- Every memory object the store typing claims at a struct carries exactly
the struct's members: `Person memory m;` allocates both. -/
def CanonHeap (H : HeapTy) (heap : List (Nat × Semantics.MObj)) : Prop :=
  ∀ id s, lookupBy id H = some (.ref (.struct s)) →
    ∃ fields, lookupBy id heap = some (.struct fields) ∧
      fields.map (·.1) = (structDef s).map (·.1)

/-- A storage→memory copy that also keeps the heap canonical and leaves the
objects that were there alone. -/
structure CopyOutC (H : HeapTy) (s : Semantics.State) (H' : HeapTy) (s' : Semantics.State) : Prop where
  out : CopyOut H s H' s'
  canon : CanonHeap H' s'.heap
  frame : ∀ id obj, lookupBy id s.heap = some obj → lookupBy id s'.heap = some obj

/-- Two copies in a row: `alice`'s members, then `alice` herself. -/
theorem CopyOutC.trans {H₁ H₂ H₃ : HeapTy} {s₁ s₂ s₃ : Semantics.State} (h₁ : CopyOutC H₁ s₁ H₂ s₂)
    (h₂ : CopyOutC H₂ s₂ H₃ s₃) : CopyOutC H₁ s₁ H₃ s₃ :=
  ⟨h₁.out.trans h₂.out, h₂.canon, fun id obj h => h₂.frame id obj (h₁.frame id obj h)⟩

/-- Copying `alice` into memory: the copies of its members first. -/
theorem copyStFields_names {s s' : Semantics.State} :
    ∀ {fields : List (Name × Semantics.SVal)} {mfields : List (Name × Semantics.MVal)},
      copyStFields s fields = .ok (s', mfields) → mfields.map (·.1) = fields.map (·.1)
  | [], mfields, h => by
    simp only [copyStFields, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; rfl
  | (n, v) :: rest, mfields, h => by
    obtain ⟨⟨s₁, mv⟩, _, h⟩ := bind_ok_inv h
    obtain ⟨⟨s₂, mrest⟩, hrest, h⟩ := bind_ok_inv h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [copyStFields_names hrest]

/-- Allocating a new object keeps the heap canonical when the object is. -/
theorem CopyOutC.alloc {H H₁ : HeapTy} {s s₁ : Semantics.State} {r : RefTy} {obj : Semantics.MObj}
    (hout : CopyOutC H s H₁ s₁) (hobj : MObj.hasTyH H₁ obj (Ty.ref r) = true)
    (hnames : ∀ str, r = .struct str → ∃ fields, obj = .struct fields ∧
      fields.map (·.1) = (structDef str).map (·.1)) :
    CopyOutC H s (setBy s₁.nextId (Ty.ref r) H₁) (s₁.alloc obj).1 ∧
      MVal.hasTyH (setBy s₁.nextId (Ty.ref r) H₁) (MVal.ref s₁.nextId) (Ty.ref r) = true := by
  obtain ⟨hout', hty⟩ := CopyOut.alloc hout.out hobj
  have hfresh : lookupBy s₁.nextId s₁.heap = none := hout.out.heapWf.nextId_fresh
  refine ⟨⟨hout', ?_, fun id o h => ?_⟩, hty⟩
  · intro id str hid
    show ∃ fields, lookupBy id (setBy s₁.nextId obj s₁.heap) = some (.struct fields) ∧ _
    by_cases he : id = s₁.nextId
    · subst he
      rw [lookupBy_setBy_self] at hid ⊢
      cases hid
      obtain ⟨fields, rfl, hn⟩ := hnames str rfl
      exact ⟨fields, rfl, hn⟩
    · rw [lookupBy_setBy_ne he] at hid ⊢
      exact hout.canon id str hid
  · have h₁ := hout.frame id o h
    show lookupBy id (setBy s₁.nextId obj s₁.heap) = some o
    have he : id ≠ s₁.nextId := by
      intro he; subst he; rw [hfresh] at h₁; exact nomatch h₁
    rw [lookupBy_setBy_ne he]; exact h₁

mutual

/-- Copying a canonical storage value into memory keeps the heap canonical:
`Person memory m = alice;` allocates a `Person` with both members. -/
theorem copyStToM_canon {H : HeapTy} {s s' : Semantics.State} {v : Semantics.SVal} {ty : Ty} {mv : Semantics.MVal}
    (hnd : nodupKeysB H = true) (hheap : heapTypedB H s.heap = true)
    (hwf : HeapWellFormed s) (hc : CanonHeap H s.heap) (hty : v.hasTy ty = true)
    (hcn : v.canon ty) (hcopy : copyStToM s v = .ok (s', mv)) :
    ∃ H', CopyOutC H s H' s' ∧ MVal.hasTyH H' mv ty = true := by
  cases v with
  | prim p =>
    cases p <;> simp only [copyStToM, Except.ok.injEq, Prod.mk.injEq] at hcopy <;>
      obtain ⟨rfl, rfl⟩ := hcopy <;>
      refine ⟨H, ⟨CopyOut.refl hnd hheap hwf, hc, fun _ _ h => h⟩, ?_⟩ <;>
      cases ty with
      | prim pt => cases pt <;> simp_all [SVal.hasTy, MVal.hasTyH]
      | ref r => simp [SVal.hasTy] at hty
  | struct fields =>
    cases ty with
    | prim pt => simp [SVal.hasTy] at hty
    | ref r =>
      cases r with
      | struct str =>
        simp only [SVal.hasTy] at hty
        obtain ⟨hn, hfs⟩ := hcn
        obtain ⟨⟨s₁, mfields⟩, hf, h⟩ := bind_ok_inv hcopy
        obtain ⟨H₁, hout, hflds⟩ := copyStFields_canon hnd hheap hwf hc hty hfs hf
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have h := CopyOutC.alloc (r := .struct str) (obj := .struct mfields) hout
          (by simpa [MObj.hasTyH] using hflds)
          (fun str' he => by
            cases he
            exact ⟨mfields, rfl, (copyStFields_names hf).trans hn⟩)
        exact ⟨_, h.1, h.2⟩
      | array _ => simp [SVal.hasTy] at hty
      | fixed _ _ => simp [SVal.hasTy] at hty
      | mapping _ _ => simp [SVal.hasTy] at hty
  | array elems shadow fx =>
    cases ty with
    | prim pt => simp [SVal.hasTy] at hty
    | ref r =>
      cases r with
      | struct _ => simp [SVal.hasTy] at hty
      | array elem =>
        simp only [SVal.hasTy, Bool.and_eq_true] at hty
        obtain ⟨⟨s₁, melems⟩, he, h⟩ := bind_ok_inv hcopy
        obtain ⟨H₁, hout, hels⟩ := copyStElems_canon hnd hheap hwf hc hty.1.2 hcn.2.1 he
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have h := CopyOutC.alloc (r := .array elem) (obj := .array melems fx) hout
          (by simp only [MObj.hasTyH, Bool.and_eq_true]; exact ⟨hty.1.1, hels⟩)
          (fun _ he => nomatch he)
        exact ⟨_, h.1, h.2⟩
      | fixed elem n =>
        simp only [SVal.hasTy, Bool.and_eq_true, beq_iff_eq] at hty
        obtain ⟨⟨s₁, melems⟩, he, h⟩ := bind_ok_inv hcopy
        obtain ⟨H₁, hout, hels⟩ := copyStElems_canon hnd hheap hwf hc hty.1.2 hcn.2.2.1 he
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have h := CopyOutC.alloc (r := .fixed elem n) (obj := .array melems fx) hout
          (by
            simp only [MObj.hasTyH, Bool.and_eq_true, beq_iff_eq, copyStElems_length he]
            exact ⟨hty.1.1, hels⟩)
          (fun _ he => nomatch he)
        exact ⟨_, h.1, h.2⟩
      | mapping _ _ => simp [SVal.hasTy] at hty
  | map _ _ => exact nomatch hcopy

/-- Copying `alice`'s members into memory keeps the heap canonical. -/
theorem copyStFields_canon {H : HeapTy} {s s₁ : Semantics.State} {str : Name}
    {fields : List (Name × Semantics.SVal)} {mfields : List (Name × Semantics.MVal)}
    (hnd : nodupKeysB H = true) (hheap : heapTypedB H s.heap = true)
    (hwf : HeapWellFormed s) (hc : CanonHeap H s.heap)
    (hty : SVal.hasTy.hasTyFields str fields = true) (hcn : canonFields str fields)
    (hcopy : copyStFields s fields = .ok (s₁, mfields)) :
    ∃ H₁, CopyOutC H s H₁ s₁ ∧ MObj.hasTyH.hasTyHFields H₁ str mfields = true := by
  match fields, hty, hcn, hcopy with
  | [], _, _, hcopy =>
    simp only [copyStFields, Except.ok.injEq, Prod.mk.injEq] at hcopy
    obtain ⟨rfl, rfl⟩ := hcopy
    exact ⟨H, ⟨CopyOut.refl hnd hheap hwf, hc, fun _ _ h => h⟩, rfl⟩
  | (n, v) :: rest, hty, hcn, hcopy =>
    simp only [SVal.hasTy.hasTyFields, Bool.and_eq_true] at hty
    obtain ⟨⟨s₂, mv⟩, hv, h⟩ := bind_ok_inv hcopy
    obtain ⟨⟨s₃, mrest⟩, hrest, h⟩ := bind_ok_inv h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases hdef : lookupBy n (structDef str) with
    | none => rw [hdef] at hty; exact Bool.noConfusion hty.1
    | some tyf =>
      rw [hdef] at hty
      have hcn1 : v.canon tyf := by have := hcn.1; rw [hdef] at this; exact this
      obtain ⟨H₂, hout₂, hmv⟩ := copyStToM_canon hnd hheap hwf hc hty.1 hcn1 hv
      obtain ⟨H₃, hout₃, hmrest⟩ := copyStFields_canon hout₂.out.nodup hout₂.out.heap
        hout₂.out.heapWf hout₂.canon hty.2 hcn.2 hrest
      refine ⟨H₃, hout₂.trans hout₃, ?_⟩
      simp only [MObj.hasTyH.hasTyHFields, hdef, Bool.and_eq_true]
      exact ⟨MVal.hasTyH_mono hout₃.out.ext hmv, hmrest⟩

/-- Copying `persons`' elements into memory keeps the heap canonical. -/
theorem copyStElems_canon {H : HeapTy} {s s₁ : Semantics.State} {elem : Ty}
    {elems : List Semantics.SVal} {melems : List Semantics.MVal}
    (hnd : nodupKeysB H = true) (hheap : heapTypedB H s.heap = true)
    (hwf : HeapWellFormed s) (hc : CanonHeap H s.heap)
    (hty : SVal.hasTy.hasTyElems elem elems = true) (hcn : canonElems elem elems)
    (hcopy : copyStElems s elems = .ok (s₁, melems)) :
    ∃ H₁, CopyOutC H s H₁ s₁ ∧ MObj.hasTyH.hasTyHElems H₁ elem melems = true := by
  match elems, hty, hcn, hcopy with
  | [], _, _, hcopy =>
    simp only [copyStElems, Except.ok.injEq, Prod.mk.injEq] at hcopy
    obtain ⟨rfl, rfl⟩ := hcopy
    exact ⟨H, ⟨CopyOut.refl hnd hheap hwf, hc, fun _ _ h => h⟩, rfl⟩
  | v :: rest, hty, hcn, hcopy =>
    simp only [SVal.hasTy.hasTyElems, Bool.and_eq_true] at hty
    obtain ⟨⟨s₂, mv⟩, hv, h⟩ := bind_ok_inv hcopy
    obtain ⟨⟨s₃, mrest⟩, hrest, h⟩ := bind_ok_inv h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨H₂, hout₂, hmv⟩ := copyStToM_canon hnd hheap hwf hc hty.1 hcn.1 hv
    obtain ⟨H₃, hout₃, hmrest⟩ := copyStElems_canon hout₂.out.nodup hout₂.out.heap
      hout₂.out.heapWf hout₂.canon hty.2 hcn.2 hrest
    refine ⟨H₃, hout₂.trans hout₃, ?_⟩
    simp only [MObj.hasTyH.hasTyHElems, Bool.and_eq_true]
    exact ⟨MVal.hasTyH_mono hout₃.out.ext hmv, hmrest⟩

end

/-! ## Memory back to storage -/

/-- Copying `m`'s members back into storage gives canonical members, all of them. -/
theorem copyMFields_canon {s : Semantics.State} {H : HeapTy} {rem : List Nat} {str : Name}
    (IH : ∀ {mv : Semantics.MVal} {ty : Ty} {sv : Semantics.SVal},
      MVal.hasTyH H mv ty = true → copyMToSt s rem mv = .ok sv → sv.canon ty) :
    ∀ {fields : List (Name × Semantics.MVal)} {sfields : List (Name × Semantics.SVal)},
      MObj.hasTyH.hasTyHFields H str fields = true → copyMFields s rem fields = .ok sfields →
      sfields.map (·.1) = fields.map (·.1) ∧ canonFields str sfields
  | [], sfields, _, hcopy => by
    simp only [copyMFields, Except.ok.injEq] at hcopy
    subst hcopy; exact ⟨rfl, trivial⟩
  | (n, v) :: rest, sfields, h, hcopy => by
    simp only [MObj.hasTyH.hasTyHFields, Bool.and_eq_true] at h
    rw [copyMFields] at hcopy
    obtain ⟨sv, hv, hcopy⟩ := bind_ok_inv hcopy
    obtain ⟨srest, hrest, hcopy⟩ := bind_ok_inv hcopy
    cases hcopy
    obtain ⟨hn, hc⟩ := copyMFields_canon IH h.2 hrest
    refine ⟨by simp [hn], ?_, hc⟩
    have h1 := h.1
    revert h1
    cases lookupBy n (structDef str) with
    | none => intro h1; exact Bool.noConfusion h1
    | some ty => intro h1; exact IH h1 hv

/-- Copying `ns`' elements back into storage gives canonical elements. -/
theorem copyMElems_canon {s : Semantics.State} {H : HeapTy} {rem : List Nat} {elem : Ty}
    (IH : ∀ {mv : Semantics.MVal} {ty : Ty} {sv : Semantics.SVal},
      MVal.hasTyH H mv ty = true → copyMToSt s rem mv = .ok sv → sv.canon ty) :
    ∀ {elems : List Semantics.MVal} {selems : List Semantics.SVal},
      MObj.hasTyH.hasTyHElems H elem elems = true → copyMElems s rem elems = .ok selems →
      canonElems elem selems
  | [], selems, _, hcopy => by
    simp only [copyMElems, Except.ok.injEq] at hcopy
    subst hcopy; trivial
  | v :: rest, selems, h, hcopy => by
    simp only [MObj.hasTyH.hasTyHElems, Bool.and_eq_true] at h
    rw [copyMElems] at hcopy
    obtain ⟨sv, hv, hcopy⟩ := bind_ok_inv hcopy
    obtain ⟨srest, hrest, hcopy⟩ := bind_ok_inv hcopy
    cases hcopy
    exact ⟨IH h.1 hv, copyMElems_canon IH h.2 hrest⟩

/-- Copying a typed memory object back into storage gives a canonical value:
`alice = m;` stores a `Person` with both members, because `m`'s object has
both. -/
theorem copyMToSt_canon {H : HeapTy} {s : Semantics.State} (hheap : heapTypedB H s.heap = true)
    (hc : CanonHeap H s.heap) {rem : List Nat} :
    ∀ {mv : Semantics.MVal} {ty : Ty} {sv : Semantics.SVal},
      MVal.hasTyH H mv ty = true → copyMToSt s rem mv = .ok sv → sv.canon ty := by
  intro mv ty sv h hcopy
  cases mv with
  | prim p =>
    cases p with
    | int n =>
      simp only [copyMToSt, Except.ok.injEq] at hcopy
      subst hcopy
      cases ty with
      | prim pt => cases pt <;> simp_all [MVal.hasTyH, SVal.canon]
      | ref r => simp [MVal.hasTyH] at h
    | bool b =>
      simp only [copyMToSt, Except.ok.injEq] at hcopy
      subst hcopy
      cases ty with
      | prim pt => cases pt <;> simp_all [MVal.hasTyH, SVal.canon]
      | ref r => simp [MVal.hasTyH] at h
  | ref id =>
    cases ty with
    | prim pt => cases pt <;> simp [MVal.hasTyH] at h
    | ref r =>
      rw [MVal.hasTyH_ref] at h
      obtain ⟨obj, hobj, hrow⟩ := heapTypedB_obj hheap h
      by_cases hmem : id ∈ rem
      · simp only [copyMToSt, hmem, dif_pos, State.getObj, hobj] at hcopy
        cases obj with
        | struct fields =>
          cases r with
          | struct str =>
            obtain ⟨fields', hobj', hn⟩ := hc id str h
            rw [hobj] at hobj'
            cases hobj'
            obtain ⟨sfields, hfs, hcopy⟩ := bind_ok_inv hcopy
            cases hcopy
            obtain ⟨hn', hcf⟩ := copyMFields_canon (fun hv hc' => copyMToSt_canon hheap hc hv hc')
              (by simpa [MObj.hasTyH] using hrow) hfs
            exact ⟨hn'.trans hn, hcf⟩
          | array _ => simp [MObj.hasTyH] at hrow
          | fixed _ _ => simp [MObj.hasTyH] at hrow
          | mapping _ _ => simp [MObj.hasTyH] at hrow
        | array elems fx =>
          cases r with
          | array elem =>
            simp only [MObj.hasTyH, Bool.and_eq_true, Bool.not_eq_true'] at hrow
            obtain ⟨selems, hes, hcopy⟩ := bind_ok_inv hcopy
            cases hcopy
            exact ⟨hrow.1, copyMElems_canon (fun hv hc' => copyMToSt_canon hheap hc hv hc')
              hrow.2 hes, trivial⟩
          | fixed elem n =>
            simp only [MObj.hasTyH, Bool.and_eq_true, beq_iff_eq] at hrow
            obtain ⟨selems, hes, hcopy⟩ := bind_ok_inv hcopy
            cases hcopy
            exact ⟨hrow.1.1, (copyMElems_length hes).trans hrow.1.2,
              copyMElems_canon (fun hv hc' => copyMToSt_canon hheap hc hv hc') hrow.2 hes, trivial⟩
          | struct _ => simp [MObj.hasTyH] at hrow
          | mapping _ _ => simp [MObj.hasTyH] at hrow
      · simp only [copyMToSt, hmem, dif_neg, not_false_iff] at hcopy
        exact nomatch hcopy
termination_by rem.length
decreasing_by all_goals
  (have h1 := List.length_erase_of_mem hmem
   have h2 := List.length_pos_of_mem hmem
   omega)

/-! ## The canonical state -/

/-- Storage holds exactly `C`'s roots, in declaration order, each canonical
at its declared type. -/
def CanonStorage (C : Contract) (st : List (Name × Semantics.SVal)) : Prop :=
  st.map (·.1) = C.vars.map (·.1) ∧
    ∀ r T, lookupBy r C.vars = some T → ∃ v, lookupBy r st = some v ∧ v.canon T

/-- What a run keeps beyond `RunWT`: canonical storage, canonical heap. -/
structure Canon (C : Contract) (H : HeapTy) (σ : Semantics.State) : Prop where
  storage : CanonStorage C σ.storage
  heap : CanonHeap H σ.heap

namespace Canon

variable {H : HeapTy} {σ σ' : Semantics.State}

/-- A step that leaves storage and heap alone keeps them canonical:
`uint x = 1;`, `a.transfer(v);`. -/
theorem of_eq (hc : Canon C H σ) (hs : σ'.storage = σ.storage) (hh : σ'.heap = σ.heap) :
    Canon C H σ' :=
  ⟨hs ▸ hc.storage, hh ▸ hc.heap⟩

/-- A read at a typed path finds a canonical value: `alice.account`. -/
theorem find (hc : Canon C H σ) {r : Name} {segs : List Seg} {T : Ty} {v : Semantics.SVal}
    (hT : C.layout.tyAt r segs = some T) (hv : σ.findStorage r segs = .ok v) : v.canon T := by
  obtain ⟨T₀, hr, hT⟩ := Layout.tyAt_split hT
  obtain ⟨v₀, hv₀, hc₀⟩ := hc.storage.2 r T₀ hr
  simp only [State.findStorage, hv₀] at hv
  exact find_canon hc₀ hT hv

/-- A write of a canonical value at a typed path keeps storage canonical:
`alice.age = 3;`. -/
theorem save (hc : Canon C H σ) {r : Name} {segs : List Seg} {T : Ty} {new : Semantics.SVal}
    (hT : C.layout.tyAt r segs = some T) (hnew : new.canon T)
    (h : σ.saveStorage r segs new = .ok σ') : Canon C H σ' := by
  obtain ⟨hheap, -⟩ := SemanticsProperties.State.saveStorage_frame h
  refine ⟨?_, hheap ▸ hc.heap⟩
  obtain ⟨T₀, hr, hT⟩ := Layout.tyAt_split hT
  obtain ⟨v₀, up, hv₀, hup, rfl⟩ := SemanticsProperties.State.saveStorage_ok_inv h
  obtain ⟨_, hv₁, hc₀⟩ := hc.storage.2 r T₀ hr
  cases hv₀.symm.trans hv₁
  have hupc := save_canon hc₀ hT hnew hup
  refine ⟨(map_fst_setBy_of_present (by simp [hv₀])).trans hc.storage.1, fun r' T' hr' => ?_⟩
  by_cases he : r' = r
  · subst he
    cases hr.symm.trans hr'
    exact ⟨up, lookupBy_setBy_self _ _ _, hupc⟩
  · obtain ⟨v, hv, hcv⟩ := hc.storage.2 r' T' hr'
    exact ⟨v, by show lookupBy r' (setBy r up σ.storage) = _; rw [lookupBy_setBy_ne he]; exact hv,
      hcv⟩

/-- An assignment's storage write keeps storage canonical: a word saved, or
a copy laid over what is there (`SVal.overlay_canon`). -/
theorem write (hc : Canon C H σ) {r : Name} {segs : List Seg} {T : Ty} {new : Semantics.SVal}
    (hT : C.layout.tyAt r segs = some T) (hnew : new.canon T)
    (h : σ.writeStorage r segs new = .ok σ') : Canon C H σ' := by
  rcases State.writeStorage_ok_inv h with h | ⟨cur, hcur, h⟩
  · exact hc.save hT hnew h
  · exact hc.save hT (SVal.overlay_canon (hc.find hT hcur) hnew) h

end Canon

/-- A contract starts canonical: each root at its type's default. -/
theorem Canon.init {σ : Semantics.State}
    (hst : σ.storage = C.initStorage) : Canon C [] σ := by
  refine ⟨⟨?_, fun r T hr => ?_⟩, fun _ _ h => nomatch h⟩
  · rw [hst]; simp only [Contract.initStorage, List.map_map, List.map_inj_left, Function.comp_apply,
      implies_true]
  · refine ⟨defaultForTy T, ?_, ?_⟩
    · rw [hst]; simp [Contract.initStorage, Semantics.lookupBy_map_snd, hr]
    · exact defaultForTy_canon

/-! ## The statements' effects are canonical -/

section Effects

variable {H : HeapTy} {σ σ' : Semantics.State}

/-- `b.push(v)` keeps storage canonical. -/
theorem pushAt_canon (hc : Canon C H σ) {E : Ty} {r : Name} {segs : List Seg}
    {val : Semantics.SVal → Res Semantics.SVal} (hty : C.layout.tyAt r segs = some (.ref (.array E)))
    (hval : ∀ slot v, slot.canon E → val slot = .ok v → v.canon E)
    (h : pushAt σ E r segs val = .ok σ') : Canon C H σ' := by
  obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
  obtain ⟨elems, shadow, rfl, he, hsh⟩ := canon_array (hc.find hty hsv)
  obtain ⟨newElem, hnew, h⟩ := bind_ok_inv h
  exact hc.save hty (by exact ⟨rfl, canonElems_append he ⟨hval _ _ (pushSlot_canon hsh).1 hnew,
    trivial⟩, (pushSlot_canon hsh).2⟩) h

/-- `b.push()` as a place keeps storage canonical. -/
theorem pushPlaceAt_canon (hc : Canon C H σ) {E : Ty} {r : Name} {segs : List Seg} {n : Int}
    (hty : C.layout.tyAt r segs = some (.ref (.array E)))
    (h : pushPlaceAt σ E r segs = .ok (σ', n)) : Canon C H σ' := by
  obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
  obtain ⟨elems, shadow, rfl, he, hsh⟩ := canon_array (hc.find hty hsv)
  obtain ⟨σ₁, hσ₁, h⟩ := bind_ok_inv h
  cases h
  exact hc.save hty (by exact ⟨rfl, canonElems_append he ⟨(pushSlot_canon hsh).1, trivial⟩,
    (pushSlot_canon hsh).2⟩) hσ₁

/-- `b.pop()` keeps storage canonical: the popped slot is cleared into the
recycled ones. -/
theorem popAt_canon (hc : Canon C H σ) {E : Ty} {keep : Bool} {r : Name} {segs : List Seg}
    (hty : C.layout.tyAt r segs = some (.ref (.array E))) (h : popAt σ keep r segs = .ok σ') :
    Canon C H σ' := by
  obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
  obtain ⟨elems, shadow, rfl, he, hsh⟩ := canon_array (hc.find hty hsv)
  simp only at h
  split at h
  · exact nomatch h
  · rename_i last restRev hrev
    have hmem : ∀ v, v ∈ last :: restRev → v ∈ elems := by
      intro v hv; rw [← hrev] at hv; exact List.mem_reverse.mp hv
    have hl := canonElems_mem he (hmem last List.mem_cons_self)
    exact hc.save hty (by exact ⟨rfl, canonElems_of_forall fun v hv =>
      canonElems_mem he (hmem v (List.mem_cons_of_mem _ (List.mem_reverse.mp hv))),
      by cases keep
         · exact SVal.defaultOf_canon hl
         · exact hl, hsh⟩) h

/-- A primitive write-back keeps storage canonical: `x += 1`, `x++`. -/
theorem Canon.savePrim (hc : Canon C H σ) {r : Name} {segs : List Seg} {p : PrimTy} {v : Value}
    (hT : C.layout.tyAt r segs = some (.prim p)) (hv : (Value.toSVal v).hasTy (.prim p) = true)
    (h : σ.saveStorage r segs v.toSVal = .ok σ') : Canon C H σ' :=
  hc.save hT (canon_prim_iff.mpr hv) h

/-- `alice.age += 1;` writes a number back. -/
theorem opStore_canon (hc : Canon C H σ) {op : BinOp} {p : PrimTy} {r : Name}
    {segs : List Seg} {v : Value} (hop : op.isArith = true) (hp : p.isNumeric = true)
    (hty : C.layout.tyAt r segs = some (.prim p)) (h : opStore σ op p r segs v = .ok σ') :
    Canon C H σ' := by
  obtain ⟨_, _, _, h₁, h₂, h⟩ := opStore_ok_inv h
  exact hc.savePrim hty (arith_new_wt hop hp h₁ h₂) h

/-- `alice.age++;` writes a number back. -/
theorem bumpStore_canon (hc : Canon C H σ) {op : IncDec} {p : PrimTy} {r : Name}
    {segs : List Seg} {w : Value} (hp : p.isNumeric = true)
    (hty : C.layout.tyAt r segs = some (.prim p)) (h : bumpStore σ op p r segs = .ok (σ', w)) :
    Canon C H σ' := by
  obtain ⟨_, _, hn, hσ₁, -⟩ := bumpStore_ok_inv h
  exact hc.savePrim hty (bump_new_wt hp hn) hσ₁

/-- A write into a memory struct's member leaves the storage alone. -/
theorem memWriteField_storage {id : Nat} {f : Name} {mv : Semantics.MVal}
    (h : memWriteField σ id f mv = .ok σ') : σ'.storage = σ.storage := by
  obtain ⟨o, _, h⟩ := bind_ok_inv h
  split at h
  · cases h; rfl
  · exact nomatch h

/-- A write into a memory array's element leaves the storage alone. -/
theorem memWriteIndex_storage {id : Nat} {i : Int} {mv : Semantics.MVal}
    (h : memWriteIndex σ id i mv = .ok σ') : σ'.storage = σ.storage := by
  obtain ⟨o, _, h⟩ := bind_ok_inv h
  split at h
  · split at h
    · cases h; rfl
    · exact nomatch h
  · exact nomatch h

/-- `m.age = 3;` through a resolved address leaves the storage alone. -/
theorem writeLoc_storage {loc : Addr} {v : Value} (h : writeLoc σ loc v = .ok σ') :
    σ'.storage = σ.storage := by
  cases loc with
  | memoryField id f => exact memWriteField_storage h
  | memoryIndex id i => exact memWriteIndex_storage h

/-- `m.age += 1;` leaves the storage alone. -/
theorem opMem_storage {op : BinOp} {p : PrimTy} {loc : Addr} {v : Value}
    (h : opMem σ op p loc v = .ok σ') : σ'.storage = σ.storage :=
  let ⟨_, _, _, _, _, h⟩ := opMem_ok_inv h
  writeLoc_storage h

/-- `m.age++;` leaves the storage alone. -/
theorem bumpMem_storage {op : IncDec} {p : PrimTy} {loc : Addr} {w : Value}
    (h : bumpMem σ op p loc = .ok (σ', w)) : σ'.storage = σ.storage :=
  let ⟨_, _, _, h, _⟩ := bumpMem_ok_inv h
  writeLoc_storage h

/-- `Person memory m;` allocates a canonical `Person`. -/
theorem allocDefault_canon (hwt : StateWT H C.layout σ) (hc : Canon C H σ) {R : RefTy} {id : Nat}
    (h : allocDefault σ R = .ok (σ', id)) :
    ∃ H', CopyOutC H σ H' σ' ∧ MVal.hasTyH H' (.ref id) (.ref R) = true := by
  simp only [allocDefault] at h
  cases hcopy : copyStToM σ (defaultForRef R) with
  | error e => rw [hcopy] at h; exact nomatch h
  | ok out =>
    obtain ⟨σ₁, mv⟩ := out
    rw [hcopy] at h
    obtain ⟨H', hout, hmv⟩ := copyStToM_canon hwt.heapTyNodup hwt.heap hwt.heapWf hc.heap
      defaultForTy_hasTy defaultForTy_canon hcopy
    cases mv with
    | prim _ => exact nomatch h
    | ref rid =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨H', hout, hmv⟩

/-- `new uint[](n)` copies in a canonical array: `n` fresh defaults. -/
theorem newArrVal_canon {R : RefTy} (h : R.newArrOk = true) (n : Int) :
    (newArrVal R n).canon (.ref R) := by
  cases R with
  | array E =>
    simp only [RefTy.newArrOk, Bool.and_eq_true] at h
    have hE := defaultForTy_canon (T := E)
    refine ⟨rfl, ?_, trivial⟩
    show canonElems E (List.replicate n.toNat (defaultForTy E))
    induction n.toNat with
    | zero => trivial
    | succ k ih => exact ⟨hE, ih⟩
  | struct _ => simp [RefTy.newArrOk] at h
  | fixed _ _ => simp [RefTy.newArrOk] at h
  | mapping _ _ => simp [RefTy.newArrOk] at h

/-- `delete m.inner;` through a resolved address leaves the storage alone. -/
theorem writeAddr_storage {a : Addr} {mv : Semantics.MVal} (h : writeAddr σ mv a = .ok σ') :
    σ'.storage = σ.storage := by
  cases a with
  | memoryField id f => exact memWriteField_storage h
  | memoryIndex id i => exact memWriteIndex_storage h

end Effects

end Solidity

/-! ## The run keeps the state canonical -/

namespace Solidity

open Semantics hiding State
open SemanticsProperties (HeapWellFormed)

variable {C : Contract}

/-- Every local satisfies the trivial predicate. -/
theorem Env.all_true : {Γ : Ctx} → (e : Env C Γ) → Env.All (C := C) (fun _ _ => True) e
  | [], _ => trivial
  | _ :: _, e => ⟨trivial, Env.all_true e.2⟩

/-- A struct's members, erased, keep their names. -/
theorem MFields.erase_names {H : HTy} : (fs : List (Name × Ty)) → (x : MFields H fs) →
    (MFields.erase fs x).map (·.1) = fs.map (·.1)
  | [], _ => rfl
  | (_, _) :: fs, x => by
    simp only [MFields.erase, List.map_cons, MFields.erase_names fs x.2]

/-- A typed heap erases to a canonical one: an object at a struct type is
the struct's members, all of them. -/
theorem Objs.erase_canon {H : HTy} (start : Nat) : (Rs : List RefTy) → (os : Objs H Rs) →
    CanonHeap (HTy.toHeapTy start Rs) (Objs.erase start Rs os)
  | [], _, _, _, h => nomatch h
  | R :: Rs, os, id, s, h => by
    simp only [HTy.toHeapTy, lookupBy] at h
    simp only [Objs.erase, lookupBy]
    by_cases he : id = start
    · simp only [he, ↓reduceIte, Option.some.injEq, Ty.ref.injEq] at h ⊢
      subst h
      exact ⟨_, rfl, MFields.erase_names _ _⟩
    · simp only [he, ↓reduceIte] at h ⊢
      exact Objs.erase_canon (start + 1) Rs os.2 id s h

/-- **The heap is canonical by construction**: a typed state's erasure,
under the store typing its heap typing lists. -/
theorem State.erase_canonHeap {Γ : Ctx} (σ : State C Γ) :
    CanonHeap (HTy.toHeapTy 0 σ.H) σ.erase.heap :=
  Objs.erase_canon 0 σ.H σ.heap

/-- What a run keeps beyond its types: canonical storage.  The heap is
canonical and every value of its type by construction
(`State.erase_canonHeap`, `State.erase_wt`). -/
def canonInv (C : Contract) : RunInv C where
  glob _ τ := CanonStorage C τ.storage
  loc _ _ _ := True
  loc_mono _ h := h
  reglob _ h := h

/-- The storage canonical. -/
abbrev RunCanon (C : Contract) {Γ : Ctx} (H : HeapTy) (σ : EState C Γ) : Prop :=
  (canonInv C).Holds H σ

namespace RunCanon

variable {Γ : Ctx} {H : HeapTy} {σ : EState C Γ}

theorem of_storage (h : CanonStorage C σ.storage) : RunCanon C H σ := ⟨h, Env.all_true σ.env⟩

theorem of_canon {H₀ : HeapTy} (hc : Canon C H₀ σ.glob) : RunCanon C H σ := of_storage hc.storage

/-- A typed state whose erasure has canonical storage is canonical, its heap
by construction. -/
theorem typed {σ : State C Γ} (h : RunCanon C H σ.erase) :
    Canon C (HTy.toHeapTy 0 σ.H) σ.erase.glob :=
  ⟨h.1, State.erase_canonHeap σ⟩

end RunCanon

/-- A leaf keeps the storage canonical when, from a well-typed canonical
erased state, what it erases to ends in a canonical one. -/
theorem canonInv.ekeeps {Γ Γ' : Ctx} {u : EState C Γ → Res (EState C Γ')}
    (hk : ∀ (H : HeapTy) (σ : EState C Γ) (σ' : EState C Γ'), RunWT C H σ → Canon C H σ.glob →
      u σ = .ok σ' → CanonStorage C σ'.storage) : (canonInv C).EKeeps u :=
  fun σ σ' hwt hcn h _ _ _ => RunCanon.of_storage (hk _ σ.erase σ' hwt (RunCanon.typed hcn) h)

/-- Storage canonical as it was: a step that leaves it alone. -/
theorem CanonStorage.of_eq {st st' : List (Name × Semantics.SVal)} (h : st' = st)
    (hc : CanonStorage C st) : CanonStorage C st' :=
  h ▸ hc

section Effects

variable {Γ : Ctx} {H : HeapTy} {σ σ' : EState C Γ}

/-- A source stores a canonical value: `alice = bob;` a canonical `Person`. -/
theorem Src.value_canon (hwt : RunWT C H σ) (hc : Canon C H σ.glob) {T : Ty} {r : Src C Γ T}
    {sv : Semantics.SVal} (h : r.value σ = .ok sv) : sv.canon T := by
  cases r with
  | val v =>
    obtain ⟨w, hv, h⟩ := bind_ok_inv h
    cases h
    exact canon_prim_iff.mpr (Val.eval_wt hwt v hv)
  | copy p _ =>
    obtain ⟨⟨r, segs⟩, hr, h⟩ := bind_ok_inv h
    exact hc.find (SPath.resolve_wt hwt p hr) h

/-- `x ⊕= e` keeps the storage canonical. -/
theorem OpLoc.store_canon (hwt : RunWT C H σ) (hc : Canon C H σ.glob) {op : BinOp}
    (hop : op.isArith = true) :
    ∀ {p : PrimTy} (l : OpLoc C Γ p) {v : Value}, p.isNumeric = true →
      l.store σ op v = .ok σ' → CanonStorage C σ'.storage
  | p, .local i, v, hp, h => by
    obtain ⟨n₁, _, h⟩ := bind_ok_inv h
    obtain ⟨n₂, _, h⟩ := bind_ok_inv h
    cases h
    exact hc.storage
  | p, .root r hr, v, hp, h => by
    obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
    exact (opStore_canon hc hop hp (Contract.layout_tyAt_root hr) hτ).storage
  | p, .field b f hf, v, hp, h => by
    obtain ⟨⟨rt, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
    exact (opStore_canon hc hop hp (Loc.resolve_wt hwt (.field b f hf) hr) hτ).storage
  | p, .index it b i, v, hp, h => by
    obtain ⟨⟨rt, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
    exact (opStore_canon hc hop hp (Loc.resolve_wt hwt (.index it b (.simple i)) hr) hτ).storage
  | p, .mfield b f hf, v, hp, h => by
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
    exact CanonStorage.of_eq (opMem_storage hτ) hc.storage
  | p, .mindex ak b i, v, hp, h => by
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    bind_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
    exact CanonStorage.of_eq (opMem_storage hτ) hc.storage

/-- `x++` keeps the storage canonical. -/
theorem OpLoc.bump_canon (hwt : RunWT C H σ) (hc : Canon C H σ.glob) {op : IncDec} :
    ∀ {p : PrimTy} (l : OpLoc C Γ p) {w : Value}, p.isNumeric = true →
      l.bump σ op = .ok (σ', w) → CanonStorage C σ'.storage
  | p, .local i, w, hp, h => by
    obtain ⟨m, _, h⟩ := bind_ok_inv h
    obtain ⟨n, _, h⟩ := bind_ok_inv h
    cases h
    exact hc.storage
  | p, .root r hr, w, hp, h => by
    obtain ⟨⟨τ, v⟩, hτ, h⟩ := map_ok_inv h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact (bumpStore_canon hc hp (Contract.layout_tyAt_root hr) hτ).storage
  | p, .field b f hf, w, hp, h => by
    obtain ⟨⟨rt, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨⟨τ, v⟩, hτ, h⟩ := map_ok_inv h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact (bumpStore_canon hc hp (Loc.resolve_wt hwt (.field b f hf) hr) hτ).storage
  | p, .index it b i, w, hp, h => by
    obtain ⟨⟨rt, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨⟨τ, v⟩, hτ, h⟩ := map_ok_inv h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact (bumpStore_canon hc hp (Loc.resolve_wt hwt (.index it b (.simple i)) hr) hτ).storage
  | p, .mfield b f hf, w, hp, h => by
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨⟨τ, v⟩, hτ, h⟩ := map_ok_inv h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact CanonStorage.of_eq (bumpMem_storage hτ) hc.storage
  | p, .mindex ak b i, w, hp, h => by
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    bind_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨⟨τ, v⟩, hτ, h⟩ := map_ok_inv h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact CanonStorage.of_eq (bumpMem_storage hτ) hc.storage

/-- `m.age = 3;` leaves the storage alone. -/
theorem MLoc.write_storage {mv : Semantics.MVal} :
    ∀ {T : Ty} (l : MLoc C Γ T), l.write σ mv = .ok σ' → σ'.storage = σ.storage
  | _, .field b f hf, h => by
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
    exact memWriteField_storage hτ
  | _, .index ak b i, h => by
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    bind_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
    exact memWriteIndex_storage hτ

/-- An allocation's copy keeps the state canonical. -/
theorem CopyOutC.wtCanon (hwt : RunWT C H σ) (hc : Canon C H σ.glob) {H' : HeapTy}
    {τ : Semantics.State} (hout : CopyOutC H σ.glob H' τ) :
    RunWT C H' (σ.withGlob τ) ∧ Canon C H' (σ.withGlob τ).glob :=
  ⟨hwt.withGlob hout.out.ext (hwt.glob.ofCopyOut hout.out),
    Canon.of_eq ⟨hout.out.storage ▸ hc.storage, hout.canon⟩ rfl rfl⟩

/-- `m = n;` and `m = alice;` keep the state canonical, the second by
allocating a canonical copy. -/
theorem MRhs.eval_canon (hwt : RunWT C H σ) (hc : Canon C H σ.glob) {R : RefTy}
    {r : MRhs C Γ R} {σ₁ : EState C Γ} {id : Nat} (h : r.eval σ = .ok (σ₁, id)) :
    ∃ H', H.Extends H' ∧ (RunWT C H' σ₁ ∧ Canon C H' σ₁.glob) ∧
      MVal.hasTyH H' (.ref id) (.ref R) = true := by
  cases r with
  | alias p =>
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id', hid, h⟩ := bind_ok_inv h
    cases h
    have := MPath.mval_wt hwt p hm0
    rw [MVal.asRef_ok hid] at this
    exact ⟨H, .refl H, ⟨hwt, hc⟩, this⟩
  | copy p _ =>
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
    obtain ⟨⟨τ, mv⟩, hcopy, h⟩ := bind_ok_inv h
    obtain ⟨id', hid, h⟩ := bind_ok_inv h
    cases h
    have hT := SPath.resolve_wt hwt p hr
    obtain ⟨H', hout, hmv⟩ := copyStToM_canon hwt.glob.heapTyNodup hwt.glob.heap
      hwt.glob.heapWf hc.heap (findStorage_hasTy hwt.glob.storage hT hsv) (hc.find hT hsv) hcopy
    rw [MVal.asRef_ok hid] at hmv
    exact ⟨H', hout.out.ext, CopyOutC.wtCanon hwt hc hout, hmv⟩
  | newArr n hn =>
    bind_inv h
    obtain ⟨nv, _, h⟩ := bind_ok_inv h
    obtain ⟨⟨τ, mv⟩, hcopy, h⟩ := bind_ok_inv h
    obtain ⟨id', hid, h⟩ := bind_ok_inv h
    cases h
    obtain ⟨H', hout, hmv⟩ := copyStToM_canon hwt.glob.heapTyNodup hwt.glob.heap
      hwt.glob.heapWf hc.heap (newArrVal_hasTy hn nv) (newArrVal_canon hn nv) hcopy
    rw [MVal.asRef_ok hid] at hmv
    exact ⟨H', hout.out.ext, CopyOutC.wtCanon hwt hc hout, hmv⟩

/-- `p = alice;` and `p = persons.push();` keep the state canonical. -/
theorem ARhs.eval_canon (hwt : RunWT C H σ) (hc : Canon C H σ.glob) {R : RefTy}
    {r : ARhs C Γ R} {σ₁ : EState C Γ} {p : Name × List Seg} (h : r.eval σ = .ok (σ₁, p)) :
    Canon C H σ₁.glob := by
  cases r with
  | path q =>
    obtain ⟨rs, hr, h⟩ := bind_ok_inv h
    cases h
    exact hc
  | push b hd =>
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨⟨τ, n⟩, hpush, h⟩ := bind_ok_inv h
    cases h
    exact (pushPlaceAt_canon hc (SPath.resolve_wt hwt b hr) hpush).of_eq rfl rfl

/-- Entering a call keeps the state canonical: a memory return is a
canonical default. -/
theorem CallRet.enter_canon {rs Γ' : Ctx} (ret : CallRet Γ rs Γ') {τ τ' : Semantics.State}
    {r : Env C rs} (hτ : StateWT H C.layout τ) (hc : Canon C H τ) (h : ret.enter τ = .ok (τ', r)) :
    ∃ H', H.Extends H' ∧ (StateWT H' C.layout τ' ∧ Canon C H' τ') ∧ Env.All (LTy.WT C H') r := by
  cases ret with
  | none => cases h; exact ⟨H, .refl H, ⟨hτ, hc⟩, trivial⟩
  | val p x res => cases h; exact ⟨H, .refl H, ⟨hτ, hc⟩, LTy.WT.default p, trivial⟩
  | rets bs => cases h; exact ⟨H, .refl H, ⟨hτ, hc⟩, Binders.defaults_wt bs⟩
  | mem R x hd hm =>
    obtain ⟨⟨τ₁, id⟩, ha, h⟩ := bind_ok_inv h
    cases h
    obtain ⟨H', hout, hid⟩ := allocDefault_canon hτ hc ha
    exact ⟨H', hout.out.ext, ⟨hτ.ofCopyOut hout.out, ⟨hout.out.storage ▸ hc.storage, hout.canon⟩⟩,
      LTy.WT.mem_some hid, trivial⟩

end Effects

/-! ### One statement at a time -/

section Leaves

variable {Γ : Ctx} (hnd : nodupKeysB C.vars = true)
include hnd

theorem keepsC_assign {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) :
    (canonInv C).TKeeps (TRun.assign l r) :=
  RunInv.TKeeps.of_agrees hnd (TRun.assign_erase l r) <| canonInv.ekeeps
    fun H σ σ' hwt hc h => by
  dsimp only at h
  obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
  obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
  obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
  have hT := Loc.resolve_wt hwt l hr
  exact ((hc.write hT (Src.value_canon hwt hc hsv) hτ).of_eq rfl rfl).storage

theorem keepsC_rebind {R : RefTy} (i : Idx Γ (.alias R)) (r : ARhs C Γ R) :
    (canonInv C).TKeeps (TRun.rebind i r) :=
  RunInv.TKeeps.of_agrees hnd (TRun.rebind_erase i r) <| canonInv.ekeeps
    fun H σ σ' hwt hc h => by
  dsimp only at h
  obtain ⟨⟨σ₁, root, segs⟩, he, h⟩ := bind_ok_inv h
  cases h
  exact ((ARhs.eval_canon hwt hc he).of_eq rfl rfl).storage

theorem keepsC_assignLocal {p : PrimTy} (i : Idx Γ (.val p)) (r : Val C Γ p) :
    (canonInv C).TKeeps (TRun.assignLocal i r) :=
  RunInv.TKeeps.of_agrees hnd (TRun.assignLocal_erase i r) <| canonInv.ekeeps
    fun H σ σ' hwt hc h => by
  obtain ⟨w, hv, h⟩ := bind_ok_inv h
  cases h
  exact (hc.of_eq rfl rfl).storage

theorem keepsC_declLocal (p : PrimTy) (init : Option (Val C Γ p)) :
    (canonInv C).TKeeps (TRun.declLocal p init) :=
  RunInv.TKeeps.of_agrees hnd (TRun.declLocal_erase p init) <| canonInv.ekeeps
    fun H σ σ' hwt hc h => by
  dsimp only at h
  cases init with
  | none =>
    cases h
    exact (hc.of_eq rfl rfl).storage
  | some e =>
    obtain ⟨w, hv, h⟩ := bind_ok_inv h
    cases h
    exact (hc.of_eq rfl rfl).storage

theorem keepsC_declStorage (R : RefTy) (init : Option (ARhs C Γ R)) :
    (canonInv C).TKeeps (TRun.declStorage R init) :=
  RunInv.TKeeps.of_agrees hnd (TRun.declStorage_erase R init) <| canonInv.ekeeps
    fun H σ σ' hwt hc h => by
  dsimp only at h
  cases init with
  | none =>
    cases h
    exact (hc.of_eq rfl rfl).storage
  | some r =>
    obtain ⟨⟨σ₁, root, segs⟩, he, h⟩ := bind_ok_inv h
    cases h
    exact ((ARhs.eval_canon hwt hc he).of_eq rfl rfl).storage

theorem keepsC_opAssign {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) (r : Val C Γ p) :
    (canonInv C).TKeeps (TRun.opAssign op l r) :=
  RunInv.TKeeps.of_agrees hnd (TRun.opAssign_erase op hop hp l r) <| canonInv.ekeeps
    fun H σ σ' hwt hc h => by
  obtain ⟨v, _, h⟩ := bind_ok_inv h
  exact OpLoc.store_canon hwt hc (compound_isArith hop) l hp h

theorem keepsC_incDec {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
    (canonInv C).TKeeps (TRun.incDec op l) :=
  RunInv.TKeeps.of_agrees hnd (TRun.incDec_erase op hp l) <| canonInv.ekeeps
    fun H σ σ' hwt hc h => by
  obtain ⟨⟨σ₁, w⟩, hb, h⟩ := bind_ok_inv h
  cases h
  exact OpLoc.bump_canon hwt hc l hp hb

theorem keepsC_assignIncDec {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
    (canonInv C).TKeeps (TRun.assignIncDec i op l) :=
  RunInv.TKeeps.of_agrees hnd (TRun.assignIncDec_erase i op hp l) <| canonInv.ekeeps
    fun H σ σ' hwt hc h => by
  dsimp only at h
  obtain ⟨⟨σ₁, w⟩, hb, h⟩ := bind_ok_inv h
  cases h
  exact (OpLoc.bump_canon hwt hc l hp hb : CanonStorage C σ₁.storage)

theorem keepsC_push {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E))
    (hd : (v.isSome || E.defaultOkS) = true) : (canonInv C).TKeeps (TRun.push b v) :=
  RunInv.TKeeps.of_agrees hnd (TRun.push_erase b v) <| canonInv.ekeeps
    fun H σ σ' hwt hc h => by
  dsimp only at h
  obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
  obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
  have hT := SPath.resolve_wt hwt b hr
  refine ((pushAt_canon hc hT ?_ hτ).of_eq rfl rfl).storage
  intro slot w hslot hw
  cases v with
  | none =>
    cases hw
    exact hslot
  | some r =>
    obtain ⟨v, hv, hw⟩ := bind_ok_inv hw
    cases hw
    exact SVal.strip_canon (Src.value_canon hwt hc hv)

theorem keepsC_pop {E : Ty} (b : SPath C Γ (.array E)) : (canonInv C).TKeeps (TRun.pop b) :=
  RunInv.TKeeps.of_agrees hnd (TRun.pop_erase b) <| canonInv.ekeeps
    fun H σ σ' hwt hc h => by
  dsimp only at h
  obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
  obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
  have hT := SPath.resolve_wt hwt b hr
  exact ((popAt_canon hc hT hτ).of_eq rfl rfl).storage

theorem keepsC_transfer (r a : Val C Γ .uint) : (canonInv C).TKeeps (TRun.transfer r a) :=
  RunInv.TKeeps.of_agrees hnd (TRun.transfer_erase r a) <| canonInv.ekeeps
    fun H σ σ' hwt hc h => by
  iterate 4 bind_inv h
  obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
  unfold Solidity.transferAt at hτ
  split at hτ
  · exact nomatch hτ
  · cases hτ; rw [Semantics.State.pay_eq]; exact hc.storage

theorem keepsC_send (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) :
    (canonInv C).TKeeps (TRun.send pv r a) :=
  RunInv.TKeeps.of_agrees hnd (TRun.send_erase pv r a) <| canonInv.ekeeps
    fun H σ σ' hwt hc h => by
  obtain ⟨_, _, h⟩ := bind_ok_inv h
  obtain ⟨addr, _, h⟩ := bind_ok_inv h
  obtain ⟨_, _, h⟩ := bind_ok_inv h
  obtain ⟨amt, _, h⟩ := bind_ok_inv h
  unfold sendAt at h
  split at h
  · exact nomatch h
  · have hp : Canon C H (σ.glob.pay addr amt) := by
      rw [Semantics.State.pay_eq]; exact hc.of_eq rfl rfl
    split at h <;> cases h
    · exact (hp.of_eq rfl rfl).storage
    · exact (hp.of_eq rfl rfl).storage
    · exact (hc.of_eq rfl rfl).storage

theorem keepsC_declMem (R : RefTy) (init : Option (MRhs C Γ R))
    (hd : (init.isSome || (Ty.ref R).defaultOkS) = true) (hm : (Ty.ref R).mapFree = true) :
    (canonInv C).TKeeps (TRun.declMem R init hm) :=
  RunInv.TKeeps.of_agrees hnd (TRun.declMem_erase R init hm) <| canonInv.ekeeps
    fun H σ σ' hwt hc h => by
  dsimp only at h
  cases init with
  | none =>
    obtain ⟨⟨τ, id⟩, ha, h⟩ := bind_ok_inv h
    cases h
    obtain ⟨H', hout, hid⟩ := allocDefault_canon hwt.glob hc ha
    have h₁ := CopyOutC.wtCanon hwt hc hout
    exact (h₁.2.of_eq rfl rfl).storage
  | some r =>
    obtain ⟨⟨σ₁, id⟩, he, h⟩ := bind_ok_inv h
    cases h
    obtain ⟨H', hext, h₁, hid⟩ := MRhs.eval_canon hwt hc he
    exact (h₁.2.of_eq rfl rfl).storage

theorem keepsC_rebindMem {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) :
    (canonInv C).TKeeps (TRun.rebindMem i r) :=
  RunInv.TKeeps.of_agrees hnd (TRun.rebindMem_erase i r) <| canonInv.ekeeps
    fun H σ σ' hwt hc h => by
  dsimp only at h
  obtain ⟨⟨σ₁, id⟩, he, h⟩ := bind_ok_inv h
  cases h
  obtain ⟨H', hext, h₁, hid⟩ := MRhs.eval_canon hwt hc he
  exact (h₁.2.of_eq rfl rfl).storage

theorem keepsC_assignFromMem {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) :
    (canonInv C).TKeeps (TRun.assignFromMem l p) :=
  RunInv.TKeeps.of_agrees hnd (TRun.assignFromMem_erase l p) <| canonInv.ekeeps
    fun H σ σ' hwt hc h => by
  dsimp only at h
  obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
  obtain ⟨id, hid, h⟩ := bind_ok_inv h
  obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
  obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
  obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
  have hm := MPath.mval_wt hwt p hm0
  rw [MVal.asRef_ok hid] at hm
  have hT := Loc.resolve_wt hwt l hr
  exact ((hc.write hT (copyMToSt_canon hwt.glob.heap hc.heap hm hsv) hτ).of_eq rfl rfl).storage

theorem keepsC_assignMem {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) :
    (canonInv C).TKeeps (TRun.assignMem l r) :=
  RunInv.TKeeps.of_agrees hnd (TRun.assignMem_erase l r) <| canonInv.ekeeps
    fun H σ σ' hwt hc h => by
  obtain ⟨mv, hmv, h⟩ := bind_ok_inv h
  exact CanonStorage.of_eq (MLoc.write_storage l h) hc.storage

theorem keepsC_delete {T : Ty} (l : Loc C Γ T) : (canonInv C).TKeeps (TRun.delete l) :=
  RunInv.TKeeps.of_agrees hnd (TRun.delete_erase l) <| canonInv.ekeeps
    fun H σ σ' hwt hc h => by
  dsimp only at h
  obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
  obtain ⟨cur, hcur, h⟩ := bind_ok_inv h
  obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
  have hty := Loc.resolve_wt hwt l hr
  exact ((hc.save hty (SVal.defaultOf_canon (hc.find hty hcur)) hτ).of_eq rfl rfl).storage

theorem keepsC_deleteMem {T : Ty} (p : MPath C Γ T) (hd : T.defaultOkS = true) :
    (canonInv C).TKeeps (TRun.deleteMem p) :=
  RunInv.TKeeps.of_agrees hnd (TRun.deleteMem_erase p) <| canonInv.ekeeps
    fun H σ σ' hwt hc h => by
  dsimp only at h
  cases p with
  | var i _ =>
    obtain ⟨⟨τ, id⟩, ha, h⟩ := bind_ok_inv h
    cases h
    obtain ⟨H', hout, hid⟩ := allocDefault_canon hwt.glob hc ha
    have h₁ := CopyOutC.wtCanon hwt hc hout
    exact (h₁.2.of_eq rfl rfl).storage
  | loc l =>
    obtain ⟨a, ha, h⟩ := bind_ok_inv h
    obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
    cases T with
    | prim p => exact CanonStorage.of_eq (writeAddr_storage hτ) hc.storage
    | ref R =>
      obtain ⟨⟨τ₁, id⟩, hal, hτ⟩ := bind_ok_inv hτ
      obtain ⟨H', hout, hid⟩ := allocDefault_canon hwt.glob hc hal
      exact CanonStorage.of_eq ((writeAddr_storage hτ).trans hout.out.storage) hc.storage

theorem keepsC_assignNew {R : RefTy} (l : NewLhs C Γ R) (n : Simple C Γ .uint)
    (hn : R.newArrOk = true) : (canonInv C).TKeeps (TRun.assignNew l n hn) :=
  RunInv.TKeeps.of_agrees hnd (TRun.assignNew_erase l n hn) <| canonInv.ekeeps
    fun H σ σ' hwt hc h => by
  dsimp only at h
  bind_inv h
  obtain ⟨nv, _, h⟩ := bind_ok_inv h
  obtain ⟨⟨τ, mv⟩, hcopy, h⟩ := bind_ok_inv h
  obtain ⟨id, hid, h⟩ := bind_ok_inv h
  obtain ⟨H', hout, hmv⟩ := copyStToM_canon hwt.glob.heapTyNodup hwt.glob.heap hwt.glob.heapWf
    hc.heap (newArrVal_hasTy hn nv) (newArrVal_canon hn nv) hcopy
  rw [MVal.asRef_ok (show mv.asRef = .ok id from hid)] at hmv
  have hg₁ : StateWT H' C.layout τ := hwt.glob.ofCopyOut hout.out
  have hc₁ : Canon C H' τ := ⟨hout.out.storage ▸ hc.storage, hout.canon⟩
  have h₁ := CopyOutC.wtCanon hwt hc hout
  cases l with
  | store l =>
    obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨τ', hτ', rfl⟩ := map_ok_inv h
    have hT := Loc.resolve_wt h₁.1 l hr
    exact ((hc₁.write hT (copyMToSt_canon hg₁.heap hc₁.heap hmv hsv) hτ').of_eq rfl rfl).storage
  | mem l =>
    exact CanonStorage.of_eq (MLoc.write_storage l h) h₁.2.storage

end Leaves

/-- A call's entry keeps the storage canonical: a memory return variable is
allocated, the storage left alone. -/
theorem canonInv.enter (hnd : nodupKeysB C.vars = true) {Γ Γ' ps rs : Ctx}
    (ret : CallRet Γ rs Γ') (σ : State C Γ) (a : TEnv C σ.H ps)
    (hcn : RunCanon C (HTy.toHeapTy 0 σ.H) (σ.withEnv a).erase) :
    RunCanon C (HTy.toHeapTy 0 (ret.enterT (σ.withEnv a)).st.H)
      (ret.enterT (σ.withEnv a)).st.erase := by
  obtain ⟨τ', r, hen, he⟩ := CallRet.enterT_ok ret σ a
  rw [he]
  obtain ⟨_, _, ⟨_, hc'⟩, _⟩ := CallRet.enter_canon ret (State.erase_wt hnd σ).glob
    ((RunCanon.typed hcn).of_eq rfl rfl) hen
  exact RunCanon.of_canon (hc'.of_eq rfl rfl)

mutual

/-- **Canonicity, statement level.**  A statement run from a well-typed
canonical state ends in one: after `alice.age = 3;` `alice` still has both
members, after `balances[7] += 1;` key `7` is there once, after
`alice = m;` the copy has every member `m`'s object has, which is all of
them. -/
theorem Stmt.keeps_canon (hnd : nodupKeysB C.vars = true) :
    {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → (canonInv C).TKeeps (Stmt.runR s)
  | _, _, .assign l r => keepsC_assign hnd l r
  | _, _, .rebind i r => keepsC_rebind hnd i r
  | _, _, .assignLocal i r => keepsC_assignLocal hnd i r
  | _, _, .declLocal p _ init => keepsC_declLocal hnd p init
  | _, _, .declStorage R _ init => keepsC_declStorage hnd R init
  | _, _, .opAssign op hop hp l r => keepsC_opAssign hnd op hop hp l r
  | _, _, .incDec op hp l => keepsC_incDec hnd op hp l
  | _, _, .assignIncDec i op hp l _ => keepsC_assignIncDec hnd i op hp l
  | _, _, .push b v hd => keepsC_push hnd b v hd
  | _, _, .pop b => keepsC_pop hnd b
  | _, _, .transfer r a => keepsC_transfer hnd r a
  | _, _, .send pv r a => keepsC_send hnd pv r a
  | _, _, .declMem R _ init hd hm => keepsC_declMem hnd R init hd hm
  | _, _, .rebindMem i r => keepsC_rebindMem hnd i r
  | _, _, .assignFromMem l p => keepsC_assignFromMem hnd l p
  | _, _, .assignMem l r => keepsC_assignMem hnd l r
  | _, _, .delete l => keepsC_delete hnd l
  | _, _, .deleteMem p hd => keepsC_deleteMem hnd p hd
  | _, _, .assignNew l n hn => keepsC_assignNew hnd l n hn
  | _, _, .ite c thn els =>
    RunInv.tkeeps_ite c thn.ext els.ext (Prog.keeps_canon hnd thn) (Prog.keeps_canon hnd els)
  | _, _, .require c => RunInv.tkeeps_require c
  | _, _, .assert c => RunInv.tkeeps_assert c
  | _, _, .revert => RunInv.tkeeps_revert
  | _, _, .call _ args ret body =>
    RunInv.tkeeps_call args ret body.ext
      (fun _ _ a _ _ => Env.all_true a) (canonInv.enter hnd ret) (Prog.keeps_canon hnd body)
  | _, _, .tryCall call rets ok err code pnc other =>
    RunInv.tkeeps_tryCall call rets ok.ext err.ext code pnc.ext other.ext
      (fun _ _ r _ _ => Env.all_true r) (fun _ _ r _ => Env.all_true r)
      (Prog.keeps_canon hnd ok) (Prog.keeps_canon hnd err) (Prog.keeps_canon hnd pnc)
      (Prog.keeps_canon hnd other)
  | _, _, .loop _ c body => RunInv.tkeeps_loop c body.ext (Prog.keeps_canon hnd body)
  | _, _, .block body => RunInv.tkeeps_block body.ext (Prog.keeps_canon hnd body)

/-- **Canonicity, block level.** -/
theorem Prog.keeps_canon (hnd : nodupKeysB C.vars = true) :
    {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → (canonInv C).TKeeps (Prog.runR P)
  | _, _, .nil => RunInv.tkeeps_nil
  | _, _, .cons s P => RunInv.tkeeps_seq (Stmt.keeps_canon hnd s) (Prog.keeps_canon hnd P)

end

/-- **Canonicity**: a block run by the typed run from a state whose erasure
has canonical storage ends, if in a state, in one whose erasure has; its
heap and its values are canonical and typed by construction. -/
theorem Prog.run_canon (hnd : nodupKeysB C.vars = true) {Γ Γ' : Ctx} (P : Prog C Γ Γ')
    {σ : State C Γ} {o : Out C σ.H Γ'} (hc : CanonStorage C σ.erase.storage)
    (h : P.run σ = .ok o) : CanonStorage C o.st.erase.storage :=
  (Prog.keeps_canon hnd P σ o (RunCanon.of_storage hc) h).1

end Solidity

namespace Solidity

open Semantics
open SemanticsProperties (lookupBy_setBy_self lookupBy_setBy_ne HeapWellFormed
  lookupBy_eq_some_mem)

variable {C : Contract}

/-! ## Reachable storages -/

/-- The state a contract starts in: each root at its type's default, no
locals, an empty heap. -/
def Contract.initState (C : Contract) : Semantics.State := { storage := C.initStorage }

/-- A deployment of no value from address `0` starts in `initState`, but
for the ledger, which books the `0` paid at `0` (`getNet` reads `0` either
way). -/
theorem Contract.deployState_empty (C : Contract) :
    C.deployState {} = { C.initState with net := [(0, 0)] } := rfl

/-- A storage is reachable when a scoped program runs, by the typed
interpreter (`Prog.run`, `Semantics/Run.lean`), from the
contract's initial state to a state whose storage erases to it.  The
program's locals are used as declared, and its values are of their types, by
construction; what the typed run keeps on the erasure
(`Prog.run_canon`, `Prog.run_tight`) holds of a reachable
storage.  A `bool` mapping key is hashed as `0`/`1` (decisions 10 and 14). -/
def Reachable (C : Contract) (st : List (Name × Semantics.SVal)) : Prop :=
  ∃ (Γ' : Ctx) (P : Prog C [] Γ') (o : Out C (State.init C).H Γ'),
    P.run (State.init C) = .ok o ∧ o.st.storage.erase = st

/-- The erasure of the state a contract starts in. -/
theorem Reachable.init_erase : (State.init C).erase = EState.ofSem C.initState :=
  State.init_erase C

/-- **Reachable ⇒ well-typed and canonical.**  Every storage a scoped
program reaches from `C`'s initial state holds `C`'s roots in order, each
well-typed and canonical: no run of `StandardExample` leaves `alice` without
her `account`. -/
theorem reachable_canon (hnd : nodupKeysB C.vars = true) {st : List (Name × Semantics.SVal)}
    (h : Reachable C st) : wellTypedStorageB C.layout st = true ∧ CanonStorage C st := by
  obtain ⟨Γ', P, o, hrun, rfl⟩ := h
  have hc : CanonStorage C (State.init C).erase.storage := by
    rw [Reachable.init_erase]; exact (Canon.init (σ := C.initState) rfl).storage
  exact ⟨Storage.erase_wt hnd o.st.storage, Prog.run_canon hnd P hc hrun⟩

/-! ## What is not reachable

Three storages `wellTypedStorageB` accepts and no scoped program reaches
(`Reachable`): the facts `SVal.hasTy` forgets are exactly what refutes
them. -/

section Witnesses

/-- One mapping root. -/
def Balances : Contract := contract!{ mapping(uint => uint) balances; }

/-- One `Account` root. -/
def Accounts : Contract := contract!{ Account acct; }

/-- `uint x;` starts at `0`. -/
theorem defaultForTy_uint : defaultForTy Ty.uint = SVal.int 0 := by
  simp [defaultForTy]

/-- A mapping whose absent keys read `5`: well-typed, not reachable,
since
every mapping's default is its type's default. -/
theorem map_default_not_reachable :
    wellTypedStorageB Balances.layout [("balances", .map [] (.int 5))] = true ∧
      ¬ Reachable Balances [("balances", .map [] (.int 5))] := by
  refine ⟨by decide, fun h => ?_⟩
  obtain ⟨-, -, hc⟩ := reachable_canon (by decide) h
  obtain ⟨v, hv, hcv⟩ := hc "balances" _ rfl
  simp only [lookupBy, if_pos] at hv
  cases hv
  have hd : SVal.int 5 = defaultForTy Ty.uint := hcv.2.2.1
  rw [defaultForTy_uint] at hd
  cases hd

/-- An `Account` without its `token`: well-typed (`hasTy` checks the members
present), not reachable, since every struct carries all its members. -/
theorem struct_missing_field_not_reachable :
    wellTypedStorageB Accounts.layout [("acct", .struct [("balance", .int 0)])] = true ∧
      ¬ Reachable Accounts [("acct", .struct [("balance", .int 0)])] := by
  refine ⟨by decide, fun h => ?_⟩
  obtain ⟨-, -, hc⟩ := reachable_canon (by decide) h
  obtain ⟨v, hv, hcv⟩ := hc "acct" _ rfl
  simp only [lookupBy, if_pos] at hv
  cases hv
  have hn := hcv.1
  simp [structDef] at hn

/-- A mapping with key `1` twice: well-typed, not reachable,
since keys only
grow by `setBy`. -/
theorem map_dup_key_not_reachable :
    wellTypedStorageB Balances.layout
        [("balances", .map [(1, .int 0), (1, .int 1)] (.int 0))] = true ∧
      ¬ Reachable Balances [("balances", .map [(1, .int 0), (1, .int 1)] (.int 0))] := by
  refine ⟨by decide, fun h => ?_⟩
  obtain ⟨-, -, hc⟩ := reachable_canon (by decide) h
  obtain ⟨v, hv, hcv⟩ := hc "balances" _ rfl
  simp only [lookupBy, if_pos] at hv
  cases hv
  exact absurd hcv.1 (by decide)

end Witnesses

end Solidity
