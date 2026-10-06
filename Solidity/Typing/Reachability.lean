import Solidity.Typing.Soundness

/-!
# What every reachable state satisfies beyond its types

`Soundness.lean` shows `RunWT` is *sufficient*: every checked run keeps it.
This module asks what else a run keeps, which `SVal.hasTy` forgets — the
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

`Prog.run_canon` is the preservation theorem, `reachable_canon` its
corollary from a contract's initial state, and the two refutations the
removed untyped layer left as `sorry` follow: a storage whose mapping default
is not the default (`map_default_not_reachable`) and one whose struct misses
a member (`struct_missing_field_not_reachable`) are well-typed and not
reachable.

The converse is `Constructibility.lean`: canonical is not enough, and
canonical and tight (`SVal.tight`) is exactly reachable.
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
def Semantics.SVal.canon : SVal → Ty → Prop
  | SVal.int _, Ty.int => True
  | SVal.int _, Ty.uint => True
  | SVal.bool _, Ty.bool => True
  | SVal.struct fields, Ty.ref (RefTy.struct s) =>
      fields.map (·.1) = (structDef s).map (·.1) ∧ canonFields s fields
  | SVal.array elems shadow fx, Ty.ref (RefTy.array E) =>
      fx = false ∧ canonElems E elems ∧ canonElems E shadow
  | SVal.array elems shadow fx, Ty.ref (RefTy.fixed E n) =>
      fx = true ∧ elems.length = n ∧ canonElems E elems ∧ canonElems E shadow
  | SVal.map entries dflt, Ty.ref (RefTy.mapping _ V) =>
      nodupKeysB entries = true ∧ canonEntries V entries ∧ dflt = defaultForTy V ∧ dflt.canon V
  | _, _ => False
where
  canonFields (s : Name) : List (Name × SVal) → Prop
    | [] => True
    | (n, v) :: rest =>
        (match lookupBy n (structDef s) with
         | some T => v.canon T
         | none => False) ∧ canonFields s rest
  canonElems (E : Ty) : List SVal → Prop
    | [] => True
    | v :: rest => v.canon E ∧ canonElems E rest
  canonEntries (V : Ty) : List (Int × SVal) → Prop
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
theorem canonFields_lookup {s : Name} {fields : List (Name × SVal)} {n : Name} {v : SVal}
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
theorem canonFields_setBy {s : Name} {fields : List (Name × SVal)} {n : Name} {w : SVal}
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
theorem canonElems_mem {E : Ty} {elems : List SVal} {v : SVal} (h : canonElems E elems)
    (hm : v ∈ elems) : v.canon E := by
  induction elems with
  | nil => cases hm
  | cons w rest ih =>
    cases hm with
    | head => exact h.1
    | tail _ hm => exact ih h.2 hm

/-- Elements canonical one by one make a canonical `uint[]`. -/
theorem canonElems_of_forall {E : Ty} {elems : List SVal} (h : ∀ v ∈ elems, v.canon E) :
    canonElems E elems := by
  induction elems with
  | nil => trivial
  | cons v rest ih =>
    exact ⟨h v List.mem_cons_self, ih fun w hw => h w (List.mem_cons_of_mem _ hw)⟩

/-- An entry of a canonical mapping is canonical: `balances[7]`. -/
theorem canonEntries_lookup {V : Ty} {entries : List (Int × SVal)} {i : Int} {v : SVal}
    (h : canonEntries V entries) (hl : lookupBy i entries = some v) : v.canon V := by
  induction entries with
  | nil => simp [lookupBy] at hl
  | cons p rest ih =>
    obtain ⟨j, w⟩ := p
    by_cases hi : i = j
    · subst hi; simp [lookupBy] at hl; subst hl; exact h.1
    · simp [lookupBy, hi] at hl; exact ih h.2 hl

/-- `balances[7] = 1` keeps the entries canonical. -/
theorem canonEntries_setBy {V : Ty} {entries : List (Int × SVal)} {i : Int} {w : SVal}
    (h : canonEntries V entries) (hw : w.canon V) : canonEntries V (setBy i w entries) := by
  induction entries with
  | nil => simp [setBy, canonEntries, hw]
  | cons p rest ih =>
    obtain ⟨j, v⟩ := p
    by_cases hi : i = j
    · subst hi; simp [setBy, canonEntries, hw, h.2]
    · simp only [setBy, if_neg hi, canonEntries]; exact ⟨h.1, ih h.2⟩

/-- `values[i] = 3` keeps the elements canonical. -/
theorem canonElems_set {E : Ty} {elems : List SVal} {i : Nat} {w : SVal}
    (h : canonElems E elems) (hw : w.canon E) : canonElems E (elems.set i w) := by
  induction elems generalizing i with
  | nil => exact h
  | cons v rest ih =>
    cases i with
    | zero => exact ⟨hw, h.2⟩
    | succ n => exact ⟨h.1, ih h.2⟩

/-- `values.push(3)` appends a canonical element. -/
theorem canonElems_append {E : Ty} {xs ys : List SVal} (hx : canonElems E xs)
    (hy : canonElems E ys) : canonElems E (xs ++ ys) := by
  induction xs with
  | nil => exact hy
  | cons v rest ih => exact ⟨hx.1, ih hx.2⟩

/-- The live elements of a canonical slot list are canonical. -/
theorem canonElems_take {E : Ty} {xs : List SVal} (n : Nat) (h : canonElems E xs) :
    canonElems E (xs.take n) :=
  canonElems_of_forall fun _ hv => canonElems_mem h (List.mem_of_mem_take hv)

/-- The slots past the end of a canonical slot list are canonical. -/
theorem canonElems_drop {E : Ty} {xs : List SVal} (n : Nat) (h : canonElems E xs) :
    canonElems E (xs.drop n) :=
  canonElems_of_forall fun _ hv => canonElems_mem h (List.mem_of_mem_drop hv)

end Lists

/-! ## Shapes -/

section Shapes

/-- A canonical `Person` is a struct with `Person`'s members. -/
theorem canon_struct {v : SVal} {s : Name} (h : v.canon (.ref (.struct s))) :
    ∃ fields, v = .struct fields ∧ fields.map (·.1) = (structDef s).map (·.1) ∧
      canonFields s fields := by
  cases v with
  | prim p => cases p <;> exact h.elim
  | struct fields => exact ⟨fields, rfl, h⟩
  | array _ _ _ => exact h.elim
  | map _ _ => exact h.elim

/-- A canonical `uint[]` is an array of canonical numbers, recycled slots
included. -/
theorem canon_array {v : SVal} {E : Ty} (h : v.canon (.ref (.array E))) :
    ∃ elems shadow, v = .array elems shadow false ∧ canonElems E elems ∧ canonElems E shadow := by
  cases v with
  | prim p => cases p <;> exact h.elim
  | struct _ => exact h.elim
  | array elems shadow fx => obtain ⟨rfl, h⟩ := h; exact ⟨elems, shadow, rfl, h⟩
  | map _ _ => exact h.elim

/-- A canonical `uint[3]` is a marked array of three canonical numbers. -/
theorem canon_fixed {v : SVal} {E : Ty} {n : Nat} (h : v.canon (.ref (.fixed E n))) :
    ∃ elems shadow, v = .array elems shadow true ∧ elems.length = n ∧ canonElems E elems ∧
      canonElems E shadow := by
  cases v with
  | prim p => cases p <;> exact h.elim
  | struct _ => exact h.elim
  | array elems shadow fx => obtain ⟨rfl, h⟩ := h; exact ⟨elems, shadow, rfl, h⟩
  | map _ _ => exact h.elim

/-- A canonical `mapping(uint => uint)` has unique keys and the default
default. -/
theorem canon_map {v : SVal} {K V : Ty} (h : v.canon (.ref (.mapping K V))) :
    ∃ entries dflt, v = .map entries dflt ∧ nodupKeysB entries = true ∧
      canonEntries V entries ∧ dflt = defaultForTy V ∧ dflt.canon V := by
  cases v with
  | prim p => cases p <;> exact h.elim
  | struct _ => exact h.elim
  | array _ _ _ => exact h.elim
  | map entries dflt => exact ⟨entries, dflt, rfl, h⟩

/-- On a primitive type canonical is well-typed: `3` at `uint`. -/
theorem canon_prim_iff {v : SVal} {p : PrimTy} :
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
theorem find_canon : ∀ {segs : List Seg} {v : SVal} {T T' : Ty} {w : SVal},
    v.canon T → tyAtSegs T segs = some T' → v.find segs = .ok w → w.canon T'
  | [], v, T, T', w, h, hs, hf => by
    simp only [tyAtSegs, Option.some.injEq] at hs
    subst hs
    simp only [SVal.find, Except.ok.injEq] at hf
    subst hf; exact h
  | seg :: rest, v, T, T', w, h, hs, hf => by
    simp only [tyAtSegs] at hs
    cases hseg : segTy T seg with
    | none => rw [hseg] at hs; exact nomatch hs
    | some Tm =>
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
            simp only [SVal.find] at hf
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
            simp only [SVal.find] at hf
            split at hf
            · exact find_canon (canonElems_mem (canonElems_append he hsh) (List.get_mem _ _)) hs hf
            · exact nomatch hf
          | fixed E _ =>
            obtain ⟨elems, sh, rfl, -, he, hsh⟩ := canon_fixed h
            simp only [segTy, Option.some.injEq] at hseg
            subst hseg
            simp only [SVal.find] at hf
            split at hf
            · exact find_canon (canonElems_mem (canonElems_append he hsh) (List.get_mem _ _)) hs hf
            · exact nomatch hf
          | mapping K V =>
            obtain ⟨es, d, rfl, -, hes, -, hd⟩ := canon_map h
            simp only [segTy, Option.some.injEq] at hseg
            subst hseg
            simp only [SVal.find] at hf
            split at hf
            · rename_i v' hl
              exact find_canon (canonEntries_lookup hes hl) hs hf
            · exact find_canon hd hs hf

/-- Saving a canonical value at a typed path keeps the tree canonical:
`alice.age = 3` leaves `alice` with both members, `balances[7] = 1` adds
key `7` once. -/
theorem save_canon : ∀ {segs : List Seg} {v : SVal} {T T' : Ty} {new w : SVal},
    v.canon T → tyAtSegs T segs = some T' → new.canon T' → v.save segs new = .ok w →
      w.canon T
  | [], v, T, T', new, w, _, hs, hn, hf => by
    simp only [tyAtSegs, Option.some.injEq] at hs
    subst hs
    simp only [SVal.save, Except.ok.injEq] at hf
    subst hf; exact hn
  | seg :: rest, v, T, T', new, w, h, hs, hn, hf => by
    simp only [tyAtSegs] at hs
    cases hseg : segTy T seg with
    | none => rw [hseg] at hs; exact nomatch hs
    | some Tm =>
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
            simp only [SVal.save] at hf
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
            simp only [SVal.save] at hf
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
            simp only [SVal.save] at hf
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
            simp only [SVal.save] at hf
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
theorem SVal.defaultOf_canon : ∀ {v : SVal} {T : Ty}, v.canon T → v.defaultOf.canon T
  | .prim (.int _), .prim .int, _ | .prim (.int _), .prim .uint, _
  | .prim (.bool _), .prim .bool, _ => trivial
  | .struct fields, .ref (.struct s), h => by
    obtain ⟨hn, hf⟩ := h
    refine ⟨?_, SVal.defaultOfFields_canon hf⟩
    rw [← hn]; exact defaultOfFields_names fields
  | .array _ _ false, .ref (.array _), h =>
    ⟨rfl, trivial, canonElems_append (SVal.defaultOfElems_canon h.2.1) h.2.2⟩
  | .array elems _ true, .ref (.fixed _ _), h =>
    ⟨rfl, (SVal.defaultOfElems_length elems).trans h.2.1, SVal.defaultOfElems_canon h.2.2.1,
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
theorem SVal.defaultOfFields_canon {s : Name} :
    ∀ {fields : List (Name × SVal)}, canonFields s fields →
      canonFields s (SVal.defaultOf.defaultOfFields fields)
  | [], _ => trivial
  | (n, v) :: rest, h => by
    refine ⟨?_, SVal.defaultOfFields_canon h.2⟩
    have h1 := h.1
    revert h1
    cases lookupBy n (structDef s) with
    | none => exact fun h => h.elim
    | some T => exact fun h => SVal.defaultOf_canon h

/-- `delete values` clears each element in place. -/
theorem SVal.defaultOfElems_canon {E : Ty} :
    ∀ {elems : List SVal}, canonElems E elems →
      canonElems E (SVal.defaultOf.defaultOfElems elems)
  | [], _ => trivial
  | _ :: _, h => ⟨SVal.defaultOf_canon h.1, SVal.defaultOfElems_canon h.2⟩

/-- `delete` keeps the member names. -/
theorem defaultOfFields_names : ∀ (fields : List (Name × SVal)),
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

/-- A fresh default is canonical: `Person memory m;` and `values.push();`
start from one, and so does every root. -/
theorem defaultForTy_canon : ∀ {T : Ty}, defaultOk T = true → (defaultForTy T).canon T := by
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

/-- The slot `persons.push();` lands on is canonical, and so are the
recycled slots left. -/
theorem pushSlot_canon {E : Ty} {shadow : List SVal} (hsh : canonElems E shadow) :
    (defaultOk E = true → (pushSlot E shadow).1.canon E) ∧
      canonElems E (pushSlot E shadow).2 := by
  cases shadow with
  | nil => exact ⟨fun hok => defaultForTy_canon hok, trivial⟩
  | cons c rest =>
    refine ⟨fun hok => ?_, hsh.2⟩
    simp only [pushSlot]
    split
    · exact defaultForTy_canon hok
    · exact hsh.1

/-! ## Copies

A copy lays the source over what is there (`SVal.overlay`); onto fresh slots
it lands stripped of what is past its arrays' ends (`SVal.strip`). -/

/-- Stripping keeps the member names. -/
theorem stripFields_names : ∀ (fields : List (Name × SVal)),
    (SVal.strip.stripFields fields).map (·.1) = fields.map (·.1)
  | [] => rfl
  | (n, _) :: rest => by
    simp only [SVal.strip.stripFields, List.map_cons, stripFields_names rest]

/-- A copy takes the source's member names. -/
theorem overlayFields_names (ofs : List (Name × SVal)) : ∀ (nfs : List (Name × SVal)),
    (SVal.overlay.overlayFields ofs nfs).map (·.1) = nfs.map (·.1)
  | [] => rfl
  | (n, _) :: rest => by
    simp only [SVal.overlay.overlayFields, List.map_cons, overlayFields_names ofs rest]

mutual

/-- A value laid on fresh slots stays canonical. -/
theorem SVal.strip_canon : ∀ {v : SVal} {T : Ty}, v.canon T → v.strip.canon T
  | .prim _, _, h => by simpa only [SVal.strip] using h
  | .struct fields, .ref (.struct _), h =>
    ⟨(stripFields_names fields).trans h.1, SVal.stripFields_canon h.2⟩
  | .array _ _ _, .ref (.array _), h => ⟨h.1, SVal.stripElems_canon h.2.1, trivial⟩
  | .array elems _ _, .ref (.fixed _ _), h =>
    ⟨h.1, (SVal.stripElems_length' elems).trans h.2.1, SVal.stripElems_canon h.2.2.1, trivial⟩
  | .map _ _, .ref (.mapping _ _), h => h
  | .struct _, .prim p, h | .array _ _ _, .prim p, h | .map _ _, .prim p, h => by
    cases p <;> exact h.elim
  | .struct _, .ref (.array _), h | .struct _, .ref (.mapping _ _), h
  | .struct _, .ref (.fixed _ _), h => h.elim
  | .array _ _ _, .ref (.struct _), h | .array _ _ _, .ref (.mapping _ _), h => h.elim
  | .map _ _, .ref (.struct _), h | .map _ _, .ref (.array _), h
  | .map _ _, .ref (.fixed _ _), h => h.elim

theorem SVal.stripFields_canon {s : Name} :
    ∀ {fields : List (Name × SVal)}, canonFields s fields →
      canonFields s (SVal.strip.stripFields fields)
  | [], _ => trivial
  | (n, v) :: rest, h => by
    refine ⟨?_, SVal.stripFields_canon h.2⟩
    have h1 := h.1
    revert h1
    cases lookupBy n (structDef s) with
    | none => exact fun h => h.elim
    | some T => exact fun h => SVal.strip_canon h

theorem SVal.stripElems_canon {E : Ty} :
    ∀ {elems : List SVal}, canonElems E elems → canonElems E (SVal.strip.stripElems elems)
  | [], _ => trivial
  | _ :: _, h => ⟨SVal.strip_canon h.1, SVal.stripElems_canon h.2⟩

end

mutual

/-- **A copy keeps storage canonical**: `bob = alice;` over a `Person`
leaves a `Person`, each member laid over the old one. -/
theorem SVal.overlay_canon {old new : SVal} {T : Ty} (ho : old.canon T) (hn : new.canon T) :
    (old.overlay new).canon T := by
  match new with
  | .prim p => cases old <;> simpa [SVal.overlay, SVal.strip] using hn
  | .struct nfs =>
      cases old with
      | struct ofs =>
          cases T with
          | prim p => cases p <;> exact hn.elim
          | ref r =>
              cases r with
              | struct s =>
                  exact ⟨(overlayFields_names ofs nfs).trans hn.1,
                    SVal.overlayFields_canon ho.2 hn.2⟩
              | array _ => exact hn.elim
              | fixed _ _ => exact hn.elim
              | mapping _ _ => exact hn.elim
      | prim _ => simp only [SVal.overlay]; exact SVal.strip_canon hn
      | array _ _ _ => simp only [SVal.overlay]; exact SVal.strip_canon hn
      | map _ _ => simp only [SVal.overlay]; exact SVal.strip_canon hn
  | .array nel nsh nfx =>
      cases old with
      | array oel osh ofx =>
          cases T with
          | prim p => cases p <;> exact hn.elim
          | ref r =>
              cases r with
              | array E =>
                  exact ⟨hn.1, SVal.overlayElems_canon (canonElems_append ho.2.1 ho.2.2) hn.2.1,
                    canonElems_append (SVal.defaultOfElems_canon (canonElems_drop _ ho.2.1))
                      (canonElems_drop _ ho.2.2)⟩
              | fixed E n =>
                  exact ⟨hn.1, (SVal.overlayElems_length _ nel).trans hn.2.1,
                    SVal.overlayElems_canon (canonElems_append ho.2.2.1 ho.2.2.2) hn.2.2.1,
                    canonElems_append (SVal.defaultOfElems_canon (canonElems_drop _ ho.2.2.1))
                      (canonElems_drop _ ho.2.2.2)⟩
              | struct _ => exact hn.elim
              | mapping _ _ => exact hn.elim
      | prim _ => simp only [SVal.overlay]; exact SVal.strip_canon hn
      | struct _ => simp only [SVal.overlay]; exact SVal.strip_canon hn
      | map _ _ => simp only [SVal.overlay]; exact SVal.strip_canon hn
  | .map ne nd =>
      cases old with
      | map oe od => simpa only [SVal.overlay] using ho
      | prim _ => simp only [SVal.overlay]; exact SVal.strip_canon hn
      | struct _ => simp only [SVal.overlay]; exact SVal.strip_canon hn
      | array _ _ _ => simp only [SVal.overlay]; exact SVal.strip_canon hn

theorem SVal.overlayFields_canon {s : Name} {ofs nfs : List (Name × SVal)}
    (ho : canonFields s ofs) (hn : canonFields s nfs) :
    canonFields s (SVal.overlay.overlayFields ofs nfs) := by
  match nfs with
  | [] => trivial
  | (n, v) :: rest =>
      refine ⟨?_, SVal.overlayFields_canon ho hn.2⟩
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
              exact SVal.overlay_canon hoc h1

theorem SVal.overlayElems_canon {E : Ty} {olds news : List SVal}
    (ho : canonElems E olds) (hn : canonElems E news) :
    canonElems E (SVal.overlay.overlayElems olds news) := by
  match olds, news with
  | o :: os, v :: rest => exact ⟨SVal.overlay_canon ho.1 hn.1, SVal.overlayElems_canon ho.2 hn.2⟩
  | [], rest => simpa only [SVal.overlay.overlayElems] using SVal.stripElems_canon hn
  | _ :: _, [] => trivial

end

/-! ## The heap keeps struct members -/

/-- Every memory object the store typing claims at a struct carries exactly
the struct's members: `Person memory m;` allocates both. -/
def CanonHeap (H : HeapTy) (heap : List (Nat × MObj)) : Prop :=
  ∀ id s, lookupBy id H = some (.ref (.struct s)) →
    ∃ fields, lookupBy id heap = some (.struct fields) ∧
      fields.map (·.1) = (structDef s).map (·.1)

/-- A storage→memory copy that also keeps the heap canonical and leaves the
objects that were there alone. -/
structure CopyOutC (H : HeapTy) (s : State) (H' : HeapTy) (s' : State) : Prop where
  out : CopyOut H s H' s'
  canon : CanonHeap H' s'.heap
  frame : ∀ id obj, lookupBy id s.heap = some obj → lookupBy id s'.heap = some obj

/-- Two copies in a row: `alice`'s members, then `alice` herself. -/
theorem CopyOutC.trans {H₁ H₂ H₃ : HeapTy} {s₁ s₂ s₃ : State} (h₁ : CopyOutC H₁ s₁ H₂ s₂)
    (h₂ : CopyOutC H₂ s₂ H₃ s₃) : CopyOutC H₁ s₁ H₃ s₃ :=
  ⟨h₁.out.trans h₂.out, h₂.canon, fun id obj h => h₂.frame id obj (h₁.frame id obj h)⟩

/-- Copying `alice` into memory: the copies of its members first. -/
theorem copyStFields_names {s s' : State} :
    ∀ {fields : List (Name × SVal)} {mfields : List (Name × MVal)},
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
theorem CopyOutC.alloc {H H₁ : HeapTy} {s s₁ : State} {r : RefTy} {obj : MObj}
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
theorem copyStToM_canon {H : HeapTy} {s s' : State} {v : SVal} {ty : Ty} {mv : MVal}
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
theorem copyStFields_canon {H : HeapTy} {s s₁ : State} {str : Name}
    {fields : List (Name × SVal)} {mfields : List (Name × MVal)}
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
theorem copyStElems_canon {H : HeapTy} {s s₁ : State} {elem : Ty}
    {elems : List SVal} {melems : List MVal}
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
theorem copyMFields_canon {s : State} {H : HeapTy} {rem : List Nat} {str : Name}
    (IH : ∀ {mv : MVal} {ty : Ty} {sv : SVal},
      MVal.hasTyH H mv ty = true → copyMToSt s rem mv = .ok sv → sv.canon ty) :
    ∀ {fields : List (Name × MVal)} {sfields : List (Name × SVal)},
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
theorem copyMElems_canon {s : State} {H : HeapTy} {rem : List Nat} {elem : Ty}
    (IH : ∀ {mv : MVal} {ty : Ty} {sv : SVal},
      MVal.hasTyH H mv ty = true → copyMToSt s rem mv = .ok sv → sv.canon ty) :
    ∀ {elems : List MVal} {selems : List SVal},
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
theorem copyMToSt_canon {H : HeapTy} {s : State} (hheap : heapTypedB H s.heap = true)
    (hc : CanonHeap H s.heap) {rem : List Nat} :
    ∀ {mv : MVal} {ty : Ty} {sv : SVal},
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
def CanonStorage (C : Contract) (st : List (Name × SVal)) : Prop :=
  st.map (·.1) = C.vars.map (·.1) ∧
    ∀ r T, lookupBy r C.vars = some T → ∃ v, lookupBy r st = some v ∧ v.canon T

/-- What a run keeps beyond `RunWT`: canonical storage, canonical heap. -/
structure Canon (C : Contract) (H : HeapTy) (σ : State) : Prop where
  storage : CanonStorage C σ.storage
  heap : CanonHeap H σ.heap

namespace Canon

variable {H : HeapTy} {σ σ' : State}

/-- A step that leaves storage and heap alone keeps them canonical:
`uint x = 1;`, `a.transfer(v);`. -/
theorem of_eq (hc : Canon C H σ) (hs : σ'.storage = σ.storage) (hh : σ'.heap = σ.heap) :
    Canon C H σ' :=
  ⟨hs ▸ hc.storage, hh ▸ hc.heap⟩

/-- A read at a typed path finds a canonical value: `alice.account`. -/
theorem find (hc : Canon C H σ) {r : Name} {segs : List Seg} {T : Ty} {v : SVal}
    (hT : C.layout.tyAt r segs = some T) (hv : σ.findStorage r segs = .ok v) : v.canon T := by
  obtain ⟨T₀, hr, hT⟩ := Layout.tyAt_split hT
  obtain ⟨v₀, hv₀, hc₀⟩ := hc.storage.2 r T₀ hr
  simp only [State.findStorage, hv₀] at hv
  exact find_canon hc₀ hT hv

/-- A write of a canonical value at a typed path keeps storage canonical:
`alice.age = 3;`. -/
theorem save (hc : Canon C H σ) {r : Name} {segs : List Seg} {T : Ty} {new : SVal}
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
theorem write (hc : Canon C H σ) {r : Name} {segs : List Seg} {T : Ty} {new : SVal}
    (hT : C.layout.tyAt r segs = some T) (hnew : new.canon T)
    (h : σ.writeStorage r segs new = .ok σ') : Canon C H σ' := by
  rcases State.writeStorage_ok_inv h with h | ⟨cur, hcur, h⟩
  · exact hc.save hT hnew h
  · exact hc.save hT (SVal.overlay_canon (hc.find hT hcur) hnew) h

end Canon

/-- A contract starts canonical: each root at its type's default. -/
theorem Canon.init {σ : State} (hok : C.vars.all (·.2.defaultOkS) = true)
    (hst : σ.storage = C.initStorage) : Canon C [] σ := by
  refine ⟨⟨?_, fun r T hr => ?_⟩, fun _ _ h => nomatch h⟩
  · rw [hst]; simp [Contract.initStorage]
  · refine ⟨defaultForTy T, ?_, ?_⟩
    · rw [hst]; simp [Contract.initStorage, lookupBy_map_snd, hr]
    · have hmem := lookupBy_eq_some_mem hr
      exact defaultForTy_canon (defaultOk_of_defaultOkS (List.all_eq_true.mp hok _ hmem))

/-! ## The statements' effects are canonical -/

section Effects

variable {Γ : Ctx} {H : HeapTy} {σ σ' : State}

/-- A source stores a canonical value: `alice = bob;` a canonical `Person`. -/
theorem Src.value_canon (hwt : RunWT C Γ H σ) (hc : Canon C H σ) {T : Ty} {r : Src C T}
    {sv : SVal} (hw : r.wt Γ = true) (h : r.value σ = .ok sv) : sv.canon T := by
  cases r with
  | val v =>
    obtain ⟨w, hv, h⟩ := bind_ok_inv h
    cases h
    exact canon_prim_iff.mpr (Val.eval_wt hwt v hw hv)
  | copy p _ =>
    obtain ⟨⟨r, segs⟩, hr, h⟩ := bind_ok_inv h
    exact hc.find (SPath.resolve_wt hwt p hw hr) h

/-- `b.push(v)` keeps storage canonical. -/
theorem pushAt_canon (hc : Canon C H σ) {E : Ty} {r : Name} {segs : List Seg}
    {val : SVal → Res SVal} (hty : C.layout.tyAt r segs = some (.ref (.array E)))
    (hval : ∀ slot v, (defaultOk E = true → slot.canon E) → val slot = .ok v → v.canon E)
    (h : pushAt σ E r segs val = .ok σ') : Canon C H σ' := by
  obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
  obtain ⟨elems, shadow, rfl, he, hsh⟩ := canon_array (hc.find hty hsv)
  obtain ⟨newElem, hnew, h⟩ := bind_ok_inv h
  exact hc.save hty (by exact ⟨rfl, canonElems_append he ⟨hval _ _ (pushSlot_canon hsh).1 hnew,
    trivial⟩, (pushSlot_canon hsh).2⟩) h

/-- `b.push()` as a place keeps storage canonical. -/
theorem pushPlaceAt_canon (hc : Canon C H σ) {E : Ty} {r : Name} {segs : List Seg} {n : Int}
    (hty : C.layout.tyAt r segs = some (.ref (.array E))) (hok : defaultOk E = true)
    (h : pushPlaceAt σ E r segs = .ok (σ', n)) : Canon C H σ' := by
  obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
  obtain ⟨elems, shadow, rfl, he, hsh⟩ := canon_array (hc.find hty hsv)
  obtain ⟨σ₁, hσ₁, h⟩ := bind_ok_inv h
  cases h
  exact hc.save hty (by exact ⟨rfl, canonElems_append he ⟨(pushSlot_canon hsh).1 hok, trivial⟩,
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

/-- A write into a memory struct's member keeps its members. -/
theorem memWriteField_canon (hc : Canon C H σ) {id : Nat} {s f : Name}
    {T : Ty} {mv : MVal} (hid : lookupBy id H = some (.ref (.struct s)))
    (hf : lookupBy f (structDef s) = some T) (h : memWriteField σ id f mv = .ok σ') :
    Canon C H σ' := by
  obtain ⟨fields, hobj, hn⟩ := hc.heap id s hid
  obtain ⟨o, ho, h⟩ := bind_ok_inv h
  simp only [State.getObj, hobj] at ho
  cases ho
  cases h
  refine ⟨hc.storage, fun id' s' hid' => ?_⟩
  show ∃ fs, lookupBy id' (setBy id _ σ.heap) = some (.struct fs) ∧ _
  by_cases he : id' = id
  · subst he
    rw [hid] at hid'; cases hid'
    refine ⟨setBy f mv fields, lookupBy_setBy_self _ _ _, ?_⟩
    rw [map_fst_setBy_of_present (lookupBy_isSome_of_map_fst hn (by simp [hf]))]
    exact hn
  · rw [lookupBy_setBy_ne he]; exact hc.heap id' s' hid'

/-- A write into a memory array's element touches no struct. -/
theorem memWriteIndex_canon (hwt : RunWT C Γ H σ) (hc : Canon C H σ) {id : Nat} {i : Int}
    {R : RefTy} {E : Ty} {mv : MVal} (hid : lookupBy id H = some (.ref R))
    (hR : R.arrElem? = some E)
    (h : memWriteIndex σ id i mv = .ok σ') : Canon C H σ' := by
  obtain ⟨obj, hobj, hty⟩ := heapTypedB_obj hwt.heap hid
  obtain ⟨o, ho, h⟩ := bind_ok_inv h
  simp only [State.getObj, hobj] at ho
  cases ho
  cases obj with
  | array elems fx =>
    simp only at h
    split at h
    · cases h
      refine ⟨hc.storage, fun id' s' hid' => ?_⟩
      show ∃ fs, lookupBy id' (setBy id _ σ.heap) = some (.struct fs) ∧ _
      have he : id' ≠ id := by
        rintro rfl; rw [hid] at hid'; cases hid'; simp [RefTy.arrElem?] at hR
      rw [lookupBy_setBy_ne he]; exact hc.heap id' s' hid'
    · exact nomatch h
  | struct _ => exact nomatch h

/-- `m.age = 3;` through a resolved address keeps the heap canonical. -/
theorem writeLoc_canon (hwt : RunWT C Γ H σ) (hc : Canon C H σ) {p : PrimTy} {loc : Addr}
    {v : Value} (hloc : AddrTy H p loc) (h : writeLoc σ loc v = .ok σ') : Canon C H σ' := by
  cases loc with
  | memoryField id f =>
    obtain ⟨s, hid, hf⟩ := hloc
    exact memWriteField_canon hc hid hf h
  | memoryIndex id i =>
    obtain ⟨R, hid, hR⟩ := hloc
    exact memWriteIndex_canon hwt hc hid hR h

/-- `m.age += 1;` keeps the heap canonical. -/
theorem opMem_canon (hwt : RunWT C Γ H σ) (hc : Canon C H σ) {op : BinOp} {p : PrimTy}
    {loc : Addr} {v : Value} (hloc : AddrTy H p loc) (h : opMem σ op p loc v = .ok σ') :
    Canon C H σ' := by
  obtain ⟨_, _, _, -, -, h⟩ := opMem_ok_inv h
  exact writeLoc_canon hwt hc hloc h

/-- `m.age++;` keeps the heap canonical. -/
theorem bumpMem_canon (hwt : RunWT C Γ H σ) (hc : Canon C H σ) {op : IncDec} {p : PrimTy}
    {loc : Addr} {w : Value} (hloc : AddrTy H p loc) (h : bumpMem σ op p loc = .ok (σ', w)) :
    Canon C H σ' := by
  obtain ⟨_, _, -, hσ₁, -⟩ := bumpMem_ok_inv h
  exact writeLoc_canon hwt hc hloc hσ₁

/-- `x ⊕= e` keeps the state canonical. -/
theorem OpLoc.store_canon (hwt : RunWT C Γ H σ) (hc : Canon C H σ) {op : BinOp}
    (hop : op.isArith = true) :
    ∀ {p : PrimTy} (l : OpLoc C p) {v : Value}, p.isNumeric = true → l.wt Γ = true →
      l.store σ op v = .ok σ' → Canon C H σ'
  | p, .local x, v, hp, hw, h => by
    obtain ⟨b, hb, _⟩ := hwt.lookup hw
    simp only [OpLoc.store, opLocal, hb, bind, Except.bind] at h
    cases b with
    | val old =>
      simp only [pure, Except.pure] at h
      split at h
      · exact nomatch h
      · split at h
        · exact nomatch h
        · cases h; exact hc.of_eq rfl rfl
    | spath _ _ => exact nomatch h
    | mref _ => exact nomatch h
    | store _ => exact nomatch h
    | ledger _ => exact nomatch h
  | p, .root r hr, v, hp, _, h => opStore_canon hc hop hp (Contract.layout_tyAt_root hr) h
  | p, .field b f hf, v, hp, hw, h => by
    obtain ⟨⟨rt, segs⟩, hr, h⟩ := bind_ok_inv h
    exact opStore_canon hc hop hp (Loc.resolve_wt hwt (.field b f hf) hw hr) h
  | p, .index it b i, v, hp, hw, h => by
    obtain ⟨⟨rt, segs⟩, hr, h⟩ := bind_ok_inv h
    exact opStore_canon hc hop hp (Loc.resolve_wt hwt (.index it b (.simple i)) hw hr) h
  | p, @OpLoc.mfield _ s _ b f hf, v, hp, hw, h => by
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    have hb := MPath.mval_wt hwt b hw hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    exact opMem_canon hwt hc (loc := .memoryField id f) ⟨s, hb, hf⟩ h
  | p, .mindex ak b i, v, hp, hw, h => by
    simp only [OpLoc.wt, Bool.and_eq_true] at hw
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    have hb := MPath.mval_wt hwt b hw.1 hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    bind_inv h
    obtain ⟨iv, _, h⟩ := bind_ok_inv h
    exact opMem_canon hwt hc (loc := .memoryIndex id iv) ⟨_, hb, ak.arrElem⟩ h

/-- `x++` keeps the state canonical. -/
theorem OpLoc.bump_canon (hwt : RunWT C Γ H σ) (hc : Canon C H σ) {op : IncDec} :
    ∀ {p : PrimTy} (l : OpLoc C p) {w : Value}, p.isNumeric = true → l.wt Γ = true →
      l.bump σ op = .ok (σ', w) → Canon C H σ'
  | p, .local x, w, hp, hw, h => by
    obtain ⟨b, hb, _⟩ := hwt.lookup hw
    simp only [OpLoc.bump, bumpLocal, hb, bind, Except.bind] at h
    cases b with
    | val old =>
      simp only [pure, Except.pure] at h
      split at h
      · exact nomatch h
      · split at h
        · exact nomatch h
        · cases h; exact hc.of_eq rfl rfl
    | spath _ _ => exact nomatch h
    | mref _ => exact nomatch h
    | store _ => exact nomatch h
    | ledger _ => exact nomatch h
  | p, .root r hr, w, hp, _, h => bumpStore_canon hc hp (Contract.layout_tyAt_root hr) h
  | p, .field b f hf, w, hp, hw, h => by
    obtain ⟨⟨rt, segs⟩, hr, h⟩ := bind_ok_inv h
    exact bumpStore_canon hc hp (Loc.resolve_wt hwt (.field b f hf) hw hr) h
  | p, .index it b i, w, hp, hw, h => by
    obtain ⟨⟨rt, segs⟩, hr, h⟩ := bind_ok_inv h
    exact bumpStore_canon hc hp (Loc.resolve_wt hwt (.index it b (.simple i)) hw hr) h
  | p, @OpLoc.mfield _ s _ b f hf, w, hp, hw, h => by
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    have hb := MPath.mval_wt hwt b hw hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    exact bumpMem_canon hwt hc (loc := .memoryField id f) ⟨s, hb, hf⟩ h
  | p, .mindex ak b i, w, hp, hw, h => by
    simp only [OpLoc.wt, Bool.and_eq_true] at hw
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    have hb := MPath.mval_wt hwt b hw.1 hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    bind_inv h
    obtain ⟨iv, _, h⟩ := bind_ok_inv h
    exact bumpMem_canon hwt hc (loc := .memoryIndex id iv) ⟨_, hb, ak.arrElem⟩ h

/-- `m.age = 3;` keeps the heap canonical. -/
theorem MLoc.write_canon (hwt : RunWT C Γ H σ) (hc : Canon C H σ) {mv : MVal} :
    ∀ {T : Ty} (l : MLoc C T), l.wt Γ = true → l.write σ mv = .ok σ' → Canon C H σ'
  | _, @MLoc.field _ s _ b f hf, hw, h => by
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    have hb := MPath.mval_wt hwt b hw hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    exact memWriteField_canon hc hb hf h
  | _, .index ak b i, hw, h => by
    simp only [MLoc.wt, Bool.and_eq_true] at hw
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    have hb := MPath.mval_wt hwt b hw.1 hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    bind_inv h
    obtain ⟨iv, _, h⟩ := bind_ok_inv h
    exact memWriteIndex_canon hwt hc hb ak.arrElem h

/-- `Person memory m;` allocates a canonical `Person`. -/
theorem allocDefault_canon (hwt : RunWT C Γ H σ) (hc : Canon C H σ) {R : RefTy} {id : Nat}
    (hok : defaultOk (Ty.ref R) = true) (h : allocDefault σ R = .ok (σ', id)) :
    ∃ H', CopyOutC H σ H' σ' ∧ MVal.hasTyH H' (.ref id) (.ref R) = true := by
  simp only [allocDefault] at h
  cases hcopy : copyStToM σ (defaultForRef R) with
  | error e => rw [hcopy] at h; exact nomatch h
  | ok out =>
    obtain ⟨σ₁, mv⟩ := out
    rw [hcopy] at h
    obtain ⟨H', hout, hmv⟩ := copyStToM_canon hwt.heapTyNodup hwt.heap hwt.heapWf hc.heap
      (defaultForTy_hasTy hok) (defaultForTy_canon hok) hcopy
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
    have hE := defaultForTy_canon (defaultOk_of_defaultOkS h.2)
    refine ⟨rfl, ?_, trivial⟩
    show canonElems E (List.replicate n.toNat (defaultForTy E))
    induction n.toNat with
    | zero => trivial
    | succ k ih => exact ⟨hE, ih⟩
  | struct _ => simp [RefTy.newArrOk] at h
  | fixed _ _ => simp [RefTy.newArrOk] at h
  | mapping _ _ => simp [RefTy.newArrOk] at h

/-- `delete m.inner;` through a resolved address keeps the heap canonical. -/
theorem writeAddr_canon (hwt : RunWT C Γ H σ) (hc : Canon C H σ) {T : Ty} {a : Addr}
    {mv : MVal} (ha : AddrTyT H T a) (h : writeAddr σ mv a = .ok σ') : Canon C H σ' := by
  cases a with
  | memoryField id f =>
    obtain ⟨s, hid, hf⟩ := ha
    exact memWriteField_canon hc hid hf h
  | memoryIndex id i =>
    obtain ⟨R, hid, hR⟩ := ha
    exact memWriteIndex_canon hwt hc hid hR h

/-- `m = n;` and `m = alice;` keep the state canonical, the second by
allocating a canonical copy. -/
theorem MRhs.bind_canon (hwt : RunWT C Γ H σ) (hc : Canon C H σ) {x : Var} {R : RefTy}
    {r : MRhs C R} (hw : r.wt Γ = true) (h : r.bind σ x = .ok σ') :
    ∃ H' σ₁ id, H.Extends H' ∧ RunWT C Γ H' σ₁ ∧ Canon C H' σ₁ ∧
      MVal.hasTyH H' (.ref id) (.ref R) = true ∧ σ' = σ₁.setEnv x (.mref id) := by
  cases r with
  | alias p =>
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    cases h
    have := MPath.mval_wt hwt p hw hm0
    rw [MVal.asRef_ok hid] at this
    exact ⟨H, σ, id, HeapTy.Extends.refl H, hwt, hc, this, rfl⟩
  | copy p _ =>
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
    obtain ⟨⟨σ₁, mv⟩, hcopy, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    cases h
    have hT := SPath.resolve_wt hwt p hw hr
    obtain ⟨H', hout, hmv⟩ := copyStToM_canon hwt.heapTyNodup hwt.heap hwt.heapWf hc.heap
      (findStorage_hasTy hwt.storage hT hsv) (hc.find hT hsv) hcopy
    rw [MVal.asRef_ok hid] at hmv
    exact ⟨H', σ₁, id, hout.out.ext, hwt.ofCopyOut hout.out,
      ⟨hout.out.storage ▸ hc.storage, hout.canon⟩, hmv, rfl⟩
  | newArr n hn =>
    bind_inv h
    obtain ⟨nv, _, h⟩ := bind_ok_inv h
    obtain ⟨⟨σ₁, mv⟩, hcopy, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    cases h
    obtain ⟨H', hout, hmv⟩ := copyStToM_canon hwt.heapTyNodup hwt.heap hwt.heapWf hc.heap
      (newArrVal_hasTy hn nv) (newArrVal_canon hn nv) hcopy
    rw [MVal.asRef_ok hid] at hmv
    exact ⟨H', σ₁, id, hout.out.ext, hwt.ofCopyOut hout.out,
      ⟨hout.out.storage ▸ hc.storage, hout.canon⟩, hmv, rfl⟩

/-- `p = alice;` and `p = persons.push();` keep the state canonical. -/
theorem ARhs.bind_canon (hwt : RunWT C Γ H σ) (hc : Canon C H σ) {x : Var} {R : RefTy}
    {r : ARhs C R} (hw : r.wt Γ = true) (h : r.bind σ x = .ok σ') : Canon C H σ' := by
  cases r with
  | path p =>
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    cases h
    exact hc.of_eq rfl rfl
  | push b hd =>
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨⟨σ₁, n⟩, hpush, h⟩ := bind_ok_inv h
    cases h
    exact (pushPlaceAt_canon hc (SPath.resolve_wt hwt b hw hr) (defaultOk_of_defaultOkS hd)
      hpush).of_eq rfl rfl


end Effects

/-! ## The run keeps the state canonical -/

/-- Binding a call's parameters only binds locals to values, so it keeps
whatever such a binding keeps. -/
theorem Arg.bindSeq_induct {P : State → Prop} (hset : ∀ τ x w, P τ → P (τ.setEnv x (.val w))) :
    ∀ {args : List (Arg C)} {σ σ' : State}, P σ → Arg.bindSeq args σ = .ok σ' → P σ'
  | [], _, _, hp, h => by cases h; exact hp
  | a :: _, σ, _, hp, h => by
    obtain ⟨w, _, h⟩ := bind_ok_inv h
    exact Arg.bindSeq_induct hset (hset σ a.x w hp) h

/-- Leaving a call binds at most its result local to a value. -/
theorem CallRet.leave_induct {P : State → Prop} (hset : ∀ τ x w, P τ → P (τ.setEnv x (.val w)))
    {σ σ' : State} : (ret : CallRet) → P σ → CallRet.leave (C := C) σ ret = .ok σ' → P σ'
  | .none, hp, h | .val _ _ Option.none, hp, h | .rets _, hp, h => by cases h; exact hp
  | .val _ _ (some _), hp, h => by
    obtain ⟨w, _, h⟩ := bind_ok_inv h
    cases h; exact hset _ _ w hp

/-- Binding a call's parameters touches only locals. -/
theorem Arg.bindSeq_locals {args : List (Arg C)} {σ σ' : State} (h : Arg.bindSeq args σ = .ok σ') :
    σ'.storage = σ.storage ∧ σ'.heap = σ.heap :=
  Arg.bindSeq_induct (P := fun τ => τ.storage = σ.storage ∧ τ.heap = σ.heap)
    (fun _ _ _ hp => hp) ⟨rfl, rfl⟩ h

/-- Binding the locals an outcome of an external call binds only binds
locals to values. -/
theorem bindData_induct {P : State → Prop} (hset : ∀ τ x w, P τ → P (τ.setEnv x (.val w))) :
    ∀ {xs : List (PrimTy × Var)} {vs : List Value} {σ σ' : State}, P σ →
      bindData xs vs σ = .ok σ' → P σ'
  | [], _, _, _, hp, h => by cases h; exact hp
  | _ :: _, [], _, _, _, h => by simp [bindData] at h
  | (_, x) :: _, w :: _, σ, _, hp, h => by
    simp only [bindData] at h
    split at h
    · exact bindData_induct hset (hset σ x w hp) h
    · cases h

/-- The locals an outcome of an external call binds are only locals. -/
theorem bindData_locals {xs : List (PrimTy × Var)} {vs : List Value} {σ σ' : State}
    (h : bindData xs vs σ = .ok σ') : σ'.storage = σ.storage ∧ σ'.heap = σ.heap :=
  bindData_induct (P := fun τ => τ.storage = σ.storage ∧ τ.heap = σ.heap)
    (fun _ _ _ hp => hp) ⟨rfl, rfl⟩ h

theorem CallRet.leave_locals {σ σ' : State} (ret : CallRet)
    (h : CallRet.leave (C := C) σ ret = .ok σ') : σ'.storage = σ.storage ∧ σ'.heap = σ.heap :=
  CallRet.leave_induct (P := fun τ => τ.storage = σ.storage ∧ τ.heap = σ.heap)
    (fun _ _ _ hp => hp) ret ⟨rfl, rfl⟩ h

mutual

/-- **Canonicity, statement level.**  A checked statement run from a
well-typed canonical state ends in one: after `alice.age = 3;` `alice`
still has both members, after `balances[7] += 1;` key `7` is there once,
after `alice = m;` the copy has every member `m`'s object has, which is all
of them. -/
theorem Stmt.run_canon : ∀ (s : Stmt C) {Γ Γ' : Ctx} {H : HeapTy} {σ σ' : State},
    RunWT C Γ H σ → Canon C H σ → s.wt Γ = some Γ' → s.run σ = .ok σ' →
      ∃ H', H.Extends H' ∧ RunWT C Γ' H' σ' ∧ Canon C H' σ'
  | .assign l r, Γ, Γ', H, σ, σ', hwt, hcn, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    have hT := Loc.resolve_wt hwt l hc.1 hr
    exact ⟨H, .refl H, hwt.write hT (Src.value_wt hwt hc.2 hsv) h,
      hcn.write hT (Src.value_canon hwt hcn hc.2 hsv) h⟩
  | .rebind x r, Γ, Γ', H, σ, σ', hwt, hcn, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    have hcn' := ARhs.bind_canon hwt hcn hc.2 h
    obtain ⟨σ₁, root, segs, hwt₁, hty, rfl⟩ := ARhs.bind_wt hwt hc.2 h
    exact ⟨H, .refl H, hwt₁.setEnv_same hc.1 (by simp [BTy.matchesB, hty]), hcn'⟩
  | .assignLocal x r, Γ, Γ', H, σ, σ', hwt, hcn, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    obtain ⟨w, hv, h⟩ := bind_ok_inv h
    cases h
    exact ⟨H, .refl H,
      hwt.setEnv_same hc.1 (by simpa [BTy.matchesB] using Val.eval_wt hwt r hc.2 hv),
      hcn.of_eq rfl rfl⟩
  | .declLocal p x init, Γ, Γ', H, σ, σ', hwt, hcn, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Stmt.run] at h
    cases init with
    | none =>
      obtain ⟨w, hv, h⟩ := bind_ok_inv h
      cases hv; cases h
      exact ⟨H, .refl H, hwt.setEnv (by cases p <;> rfl), hcn.of_eq rfl rfl⟩
    | some e =>
      obtain ⟨w, hv, h⟩ := bind_ok_inv h
      cases h
      exact ⟨H, .refl H, hwt.setEnv
        (by simpa [BTy.matchesB] using Val.eval_wt hwt e (by simpa using hc) hv),
        hcn.of_eq rfl rfl⟩
  | .declStorage R x init, Γ, Γ', H, σ, σ', hwt, hcn, hs, h => by
    cases init with
    | none =>
      cases hs; cases h
      exact ⟨H, .refl H, hwt, hcn⟩
    | some r =>
      obtain ⟨hc, rfl⟩ := wt_if hs
      have hcn' := ARhs.bind_canon hwt hcn hc h
      obtain ⟨σ₁, root, segs, hwt₁, hty, rfl⟩ := ARhs.bind_wt hwt hc h
      exact ⟨H, .refl H, hwt₁.setEnv (by simp [BTy.matchesB, hty]), hcn'⟩
  | .opAssign op hop hp l r, Γ, Γ', H, σ, σ', hwt, hcn, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    obtain ⟨v, _, h⟩ := bind_ok_inv h
    exact ⟨H, .refl H, OpLoc.store_wt hwt (compound_isArith hop) l hp hc.1 h,
      OpLoc.store_canon hwt hcn (compound_isArith hop) l hp hc.1 h⟩
  | .incDec op hp l, Γ, Γ', H, σ, σ', hwt, hcn, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    obtain ⟨⟨σ₁, w⟩, hb, h⟩ := bind_ok_inv h
    cases h
    exact ⟨H, .refl H, (OpLoc.bump_wt hwt l hp hc hb).1, OpLoc.bump_canon hwt hcn l hp hc hb⟩
  | .assignIncDec x op hp l _, Γ, Γ', H, σ, σ', hwt, hcn, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨σ₁, w⟩, hb, h⟩ := bind_ok_inv h
    cases h
    obtain ⟨hwt₁, hw⟩ := OpLoc.bump_wt hwt l hp hc.2 hb
    exact ⟨H, .refl H, hwt₁.setEnv_same hc.1 (by simpa [BTy.matchesB] using hw),
      (OpLoc.bump_canon hwt hcn l hp hc.2 hb).of_eq rfl rfl⟩
  | .push b v hd, Γ, Γ', H, σ, σ', hwt, hcn, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    have hT := SPath.resolve_wt hwt b hc.1 hr
    refine ⟨H, .refl H, pushAt_wt hwt hT ?_ h, pushAt_canon hcn hT ?_ h⟩
    · intro slot w hslot hw
      cases v with
      | none =>
        cases hw
        exact hslot (defaultOk_of_defaultOkS (by simpa using hd))
      | some r =>
        obtain ⟨v, hv, hw⟩ := bind_ok_inv hw
        cases hw
        exact SVal.strip_hasTy (Src.value_wt hwt (by simpa using hc.2) hv)
    · intro slot w hslot hw
      cases v with
      | none =>
        cases hw
        exact hslot (defaultOk_of_defaultOkS (by simpa using hd))
      | some r =>
        obtain ⟨v, hv, hw⟩ := bind_ok_inv hw
        cases hw
        exact SVal.strip_canon (Src.value_canon hwt hcn (by simpa using hc.2) hv)
  | .pop b, Γ, Γ', H, σ, σ', hwt, hcn, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    have hT := SPath.resolve_wt hwt b hc hr
    exact ⟨H, .refl H, popAt_wt hwt hT h, popAt_canon hcn hT h⟩
  | .transfer r a, Γ, Γ', H, σ, σ', hwt, hcn, hs, h => by
    obtain ⟨_, rfl⟩ := wt_if hs
    iterate 4 bind_inv h
    refine ⟨H, .refl H, hwt.transferAt h, ?_⟩
    unfold transferAt at h
    split at h
    · exact nomatch h
    · cases h; rw [State.pay_eq]; exact hcn.of_eq rfl rfl
  | .declMem R x init hd, Γ, Γ', H, σ, σ', hwt, hcn, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    cases init with
    | none =>
      obtain ⟨⟨σ₁, id⟩, ha, h⟩ := bind_ok_inv h
      cases h
      obtain ⟨H', hout, hid⟩ := allocDefault_canon hwt hcn
        (defaultOk_of_defaultOkS (by simpa using hd)) ha
      exact ⟨H', hout.out.ext,
        (hwt.ofCopyOut hout.out).setEnv (by simpa [BTy.matchesB] using hid),
        Canon.of_eq ⟨hout.out.storage ▸ hcn.storage, hout.canon⟩ rfl rfl⟩
    | some r =>
      obtain ⟨H', σ₁, id, hext, hwt₁, hcn₁, hid, rfl⟩ :=
        MRhs.bind_canon hwt hcn (by simpa using hc) h
      exact ⟨H', hext, hwt₁.setEnv (by simpa [BTy.matchesB] using hid), hcn₁.of_eq rfl rfl⟩
  | .rebindMem x r, Γ, Γ', H, σ, σ', hwt, hcn, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    obtain ⟨H', σ₁, id, hext, hwt₁, hcn₁, hid, rfl⟩ := MRhs.bind_canon hwt hcn hc.2 h
    have hx : Ctx.has Γ x (.mem (.ref _)) = true := hc.1
    exact ⟨H', hext, hwt₁.setEnv_same hx (by simpa [BTy.matchesB] using hid),
      hcn₁.of_eq rfl rfl⟩
  | .assignFromMem l p, Γ, Γ', H, σ, σ', hwt, hcn, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    have hm := MPath.mval_wt hwt p hc.2 hm0
    rw [MVal.asRef_ok hid] at hm
    have hT := Loc.resolve_wt hwt l hc.1 hr
    exact ⟨H, .refl H, hwt.write hT (copyMem_hasTy hwt.heap hm hsv) h,
      hcn.write hT (copyMToSt_canon hwt.heap hcn.heap hm hsv) h⟩
  | .assignMem l r, Γ, Γ', H, σ, σ', hwt, hcn, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    obtain ⟨mv, hmv, h⟩ := bind_ok_inv h
    exact ⟨H, .refl H, MLoc.write_wt hwt l (MSrc.mval_wt hwt hc.2 hmv) hc.1 h,
      MLoc.write_canon hwt hcn l hc.1 h⟩
  | .delete l, Γ, Γ', H, σ, σ', hwt, hcn, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨cur, hcur, h⟩ := bind_ok_inv h
    have hty := Loc.resolve_wt hwt l hc hr
    exact ⟨H, .refl H,
      hwt.save hty (SVal.defaultOf_hasTy (findStorage_hasTy hwt.storage hty hcur)) h,
      hcn.save hty (SVal.defaultOf_canon (hcn.find hty hcur)) h⟩
  | @Stmt.deleteMem _ T p hd, Γ, Γ', H, σ, σ', hwt, hcn, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    cases p with
    | var x =>
      obtain ⟨⟨σ₁, id⟩, ha, h⟩ := bind_ok_inv h
      cases h
      obtain ⟨H', hout, hid⟩ := allocDefault_canon hwt hcn (defaultOk_of_defaultOkS hd) ha
      exact ⟨H', hout.out.ext,
        (hwt.ofCopyOut hout.out).setEnv_same hc (by simpa [BTy.matchesB] using hid),
        Canon.of_eq ⟨hout.out.storage ▸ hcn.storage, hout.canon⟩ rfl rfl⟩
    | loc l =>
      obtain ⟨a, ha, h⟩ := bind_ok_inv h
      have hat := MLoc.addr_wt hwt l hc ha
      cases T with
      | prim p =>
        refine ⟨H, .refl H, writeAddr_wt hwt hat (Value.toMVal_hasTyH ?_) h,
          writeAddr_canon hwt hcn hat h⟩
        cases p <;> rfl
      | ref R =>
        obtain ⟨⟨σ₁, id⟩, hal, h⟩ := bind_ok_inv h
        obtain ⟨H', hout, hid⟩ := allocDefault_canon hwt hcn (defaultOk_of_defaultOkS hd) hal
        have hwt₁ := hwt.ofCopyOut hout.out
        have hcn₁ : Canon C H' σ₁ := ⟨hout.out.storage ▸ hcn.storage, hout.canon⟩
        exact ⟨H', hout.out.ext, writeAddr_wt hwt₁ (hat.mono hout.out.ext) hid h,
          writeAddr_canon hwt₁ hcn₁ (hat.mono hout.out.ext) h⟩
  | .assignNew l n hn, Γ, Γ', H, σ, σ', hwt, hcn, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    bind_inv h
    obtain ⟨nv, _, h⟩ := bind_ok_inv h
    obtain ⟨⟨σ₁, mv⟩, hcopy, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    obtain ⟨H', hout, hmv⟩ := copyStToM_canon hwt.heapTyNodup hwt.heap hwt.heapWf hcn.heap
      (newArrVal_hasTy hn nv) (newArrVal_canon hn nv) hcopy
    rw [MVal.asRef_ok hid] at hmv
    have hwt₁ := hwt.ofCopyOut hout.out
    have hcn₁ : Canon C H' σ₁ := ⟨hout.out.storage ▸ hcn.storage, hout.canon⟩
    cases l with
    | store l =>
      obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
      obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
      have hT := Loc.resolve_wt hwt₁ l hc.1 hr
      exact ⟨H', hout.out.ext, hwt₁.write hT (copyMem_hasTy hwt₁.heap hmv hsv) h,
        hcn₁.write hT (copyMToSt_canon hwt₁.heap hcn₁.heap hmv hsv) h⟩
    | mem l =>
      exact ⟨H', hout.out.ext, MLoc.write_wt hwt₁ l hmv hc.1 h, MLoc.write_canon hwt₁ hcn₁ l hc.1 h⟩
  | .ite c thn els, Γ, Γ', H, σ, σ', hwt, hcn, hs, h => by
    simp only [Stmt.wt] at hs
    split at hs
    · split at hs
      · rename_i Γt Γe ht he
        obtain ⟨hle, rfl⟩ := wt_if hs
        simp only [Bool.and_eq_true] at hle
        obtain ⟨cv, _, h⟩ := bind_ok_inv h
        split at h
        · obtain ⟨H', hext, hwt', hcn'⟩ := Prog.run_canon thn hwt hcn ht h
          exact ⟨H', hext, hwt'.weaken hle.1, hcn'⟩
        · obtain ⟨H', hext, hwt', hcn'⟩ := Prog.run_canon els hwt hcn he h
          exact ⟨H', hext, hwt'.weaken hle.2, hcn'⟩
        · exact nomatch h
      · exact nomatch hs
    · exact nomatch hs
  | .require c, Γ, Γ', H, σ, σ', hwt, hcn, hs, h => by
    obtain ⟨_, rfl⟩ := wt_if hs
    obtain ⟨cv, _, h⟩ := bind_ok_inv h
    unfold guardOk at h
    split at h
    · cases h; exact ⟨H, .refl H, hwt, hcn⟩
    · exact nomatch h
    · exact nomatch h
  | .assert c, Γ, Γ', H, σ, σ', hwt, hcn, hs, h => by
    obtain ⟨_, rfl⟩ := wt_if hs
    obtain ⟨cv, _, h⟩ := bind_ok_inv h
    unfold assertOk at h
    split at h
    · cases h; exact ⟨H, .refl H, hwt, hcn⟩
    · exact nomatch h
    · exact nomatch h
  | .revert, _, _, _, _, _, _, _, _, h => nomatch h
  | .call _ args _ ret body, Γ, Γ', H, σ, σ', hwt, hcn, hs, h => by
    simp only [Stmt.wt] at hs
    split at hs
    · rename_i Γ₁ h₁
      split at hs
      · rename_i Γ₂ h₂
        obtain ⟨hr, rfl⟩ := wt_if hs
        simp only [Stmt.run] at h
        obtain ⟨σ₁, hσ₁, h⟩ := bind_ok_inv h
        obtain ⟨σ₂, hσ₂, h⟩ := bind_ok_inv h
        obtain ⟨hs₁, hh₁⟩ := Arg.bindSeq_locals hσ₁
        obtain ⟨hs₁', hh₁'⟩ : (ret.enter σ₁).storage = σ.storage ∧ (ret.enter σ₁).heap = σ.heap :=
          CallRet.enter_induct (P := fun τ => τ.storage = σ.storage ∧ τ.heap = σ.heap)
            (fun _ _ _ h => h) ret ⟨hs₁, hh₁⟩
        have hcn₁ : Canon C H (ret.enter σ₁) := hcn.of_eq hs₁' hh₁'
        obtain ⟨H', hext, hwt₂, hcn₂⟩ :=
          Prog.run_canon body (CallRet.enter_wt (Arg.bindSeq_wt hwt h₁ hσ₁) ret) hcn₁ h₂ hσ₂
        obtain ⟨hs₃, hh₃⟩ := CallRet.leave_locals ret h
        exact ⟨H', hext, CallRet.leave_wt hwt₂ ret hr h, hcn₂.of_eq hs₃ hh₃⟩
      · exact nomatch hs
    · exact nomatch hs
  | .tryCall c rets ok err code pnc other, Γ, Γ', H, σ, σ', hwt, hcn, hs, h => by
    simp only [Stmt.wt] at hs
    split at hs
    · split at hs
      · rename_i Γ₁ Γ₂ Γ₃ Γ₄ h₁ h₂ h₃ h₄
        obtain ⟨hle, rfl⟩ := wt_if hs
        simp only [Bool.and_eq_true] at hle
        simp only [Stmt.run] at h
        obtain ⟨k, _, h⟩ := bind_ok_inv h
        split at h
        · exact nomatch h
        · obtain ⟨σ₁, hb, h⟩ := bind_ok_inv h
          obtain ⟨hs₁, hh₁⟩ := bindData_locals hb
          obtain ⟨H', hext, hwt', hcn'⟩ :=
            Prog.run_canon ok (bindData_wt hwt hb) (hcn.of_eq hs₁ hh₁) h₁ h
          exact ⟨H', hext, hwt'.weaken hle.1.1.1, hcn'⟩
        · obtain ⟨H', hext, hwt', hcn'⟩ := Prog.run_canon err hwt hcn h₂ h
          exact ⟨H', hext, hwt'.weaken hle.1.1.2, hcn'⟩
        · obtain ⟨σ₁, hb, h⟩ := bind_ok_inv h
          obtain ⟨hs₁, hh₁⟩ := bindData_locals hb
          obtain ⟨H', hext, hwt', hcn'⟩ :=
            Prog.run_canon pnc (bindData_wt hwt hb) (hcn.of_eq hs₁ hh₁) h₃ h
          exact ⟨H', hext, hwt'.weaken hle.1.2, hcn'⟩
        · obtain ⟨H', hext, hwt', hcn'⟩ := Prog.run_canon other hwt hcn h₄ h
          exact ⟨H', hext, hwt'.weaken hle.2, hcn'⟩
      · exact nomatch hs
    · exact nomatch hs

/-- **Canonicity, block level.** -/
theorem Prog.run_canon : ∀ (P : List (Stmt C)) {Γ Γ' : Ctx} {H : HeapTy} {σ σ' : State},
    RunWT C Γ H σ → Canon C H σ → Prog.wt Γ P = some Γ' → Prog.run σ P = .ok σ' →
      ∃ H', H.Extends H' ∧ RunWT C Γ' H' σ' ∧ Canon C H' σ'
  | [], Γ, Γ', H, σ, σ', hwt, hcn, hs, h => by
    cases hs; cases h
    exact ⟨H, .refl H, hwt, hcn⟩
  | s :: P, Γ, Γ', H, σ, σ', hwt, hcn, hs, h => by
    simp only [Prog.wt] at hs
    split at hs
    · rename_i Γ₁ h₁
      obtain ⟨σ₁, hσ₁, h⟩ := bind_ok_inv h
      obtain ⟨H₁, hext₁, hwt₁, hcn₁⟩ := Stmt.run_canon s hwt hcn h₁ hσ₁
      obtain ⟨H₂, hext₂, hwt₂, hcn₂⟩ := Prog.run_canon P hwt₁ hcn₁ hs h
      exact ⟨H₂, hext₁.trans hext₂, hwt₂, hcn₂⟩
    · exact nomatch hs

end

/-! ## Reachable storages -/

/-- The state a contract starts in: each root at its type's default, no
locals, an empty heap. -/
def Contract.initState (C : Contract) : State := { storage := C.initStorage }

/-- A storage is reachable when a program whose locals check runs from the
initial state to a state holding it. -/
def Reachable (C : Contract) (st : List (Name × SVal)) : Prop :=
  ∃ (P : Prog C) (Γ' : Ctx) (σ : State),
    Prog.wt [] P = some Γ' ∧ Prog.run C.initState P = .ok σ ∧ σ.storage = st

/-- **Reachable ⇒ well-typed and canonical.**  Every storage a checked
program reaches from `C`'s initial state holds `C`'s roots in order, each
well-typed and canonical: no run of `StandardExample` leaves `alice` without
her `account`. -/
theorem reachable_canon (hnd : nodupKeysB C.vars = true)
    (hok : C.vars.all (·.2.defaultOkS) = true) {st : List (Name × SVal)}
    (h : Reachable C st) : wellTypedStorageB C.layout st = true ∧ CanonStorage C st := by
  obtain ⟨P, Γ', σ, hP, hrun, rfl⟩ := h
  obtain ⟨_, _, hwt, hcn⟩ := Prog.run_canon P (RunWT.init hnd hok rfl rfl) (Canon.init hok rfl)
    hP hrun
  exact ⟨hwt.storage, hcn.storage⟩

/-! ## What is not reachable

Three storages `wellTypedStorageB` accepts and no program reaches: the
facts `SVal.hasTy` forgets are exactly what refutes them. -/

section Witnesses

/-- One mapping root. -/
def Balances : Contract := contract!{ mapping(uint => uint) balances; }

/-- One `Account` root. -/
def Accounts : Contract := contract!{ Account acct; }

/-- One `uint` root. -/
def Counter : Contract := contract!{ uint total; }

/-- `uint x;` starts at `0`. -/
theorem defaultForTy_uint : defaultForTy Ty.uint = SVal.int 0 := by
  simp [defaultForTy]

/-- A mapping whose absent keys read `5`: well-typed, not reachable, since
every mapping's default is its type's default. -/
theorem map_default_not_reachable :
    wellTypedStorageB Balances.layout [("balances", .map [] (.int 5))] = true ∧
      ¬ Reachable Balances [("balances", .map [] (.int 5))] := by
  refine ⟨by decide, fun h => ?_⟩
  obtain ⟨-, -, hc⟩ := reachable_canon (by decide) (by decide) h
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
  obtain ⟨-, -, hc⟩ := reachable_canon (by decide) (by decide) h
  obtain ⟨v, hv, hcv⟩ := hc "acct" _ rfl
  simp only [lookupBy, if_pos] at hv
  cases hv
  have hn := hcv.1
  simp [structDef] at hn

/-- A mapping with key `1` twice: well-typed, not reachable, since keys only
grow by `setBy`. -/
theorem map_dup_key_not_reachable :
    wellTypedStorageB Balances.layout
        [("balances", .map [(1, .int 0), (1, .int 1)] (.int 0))] = true ∧
      ¬ Reachable Balances [("balances", .map [(1, .int 0), (1, .int 1)] (.int 0))] := by
  refine ⟨by decide, fun h => ?_⟩
  obtain ⟨-, -, hc⟩ := reachable_canon (by decide) (by decide) h
  obtain ⟨v, hv, hcv⟩ := hc "balances" _ rfl
  simp only [lookupBy, if_pos] at hv
  cases hv
  exact absurd hcv.1 (by decide)

/-- `uint` range is not something a run keeps: literals are unchecked, so
`total = -5;` reaches a negative `uint`, and `canon` rightly asks no range. -/
theorem uint_negative_reachable : Reachable Counter [("total", .int (-5))] := by
  refine
  ⟨[.assign (.root "total" rfl) (.val (.simple (.lit (-5) rfl)))], [],
    { storage := [("total", .int (-5))] }, rfl, ?_, rfl⟩
  simp [Contract.initState, Contract.initStorage, Counter, Prog.run, Stmt.run, Src.value,
    Val.eval, Simple.eval, Loc.resolve, State.saveStorage, lookupBy, setBy, SVal.save,
    Value.toSVal]
  rfl

end Witnesses

end Solidity
