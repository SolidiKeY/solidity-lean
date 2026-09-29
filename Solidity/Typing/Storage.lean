import Solidity.Semantics.Properties

/-!
# Storage layout typing

The interpreter's storage (`State.storage`) is untyped; a `Layout`
declares the static types of the storage roots, with struct bodies from
`Semantics.structDef`.  `SVal.hasTy` says a storage value inhabits a type,
and `wellTypedStorageB` lifts that to whole storages.  The workhorse is
`findStorage_hasTy`: the value found at a layout-typed path inhabits that
type, the semantic content of every `\hasSort`-family taclet read.
-/

namespace Solidity
namespace Semantics

open SemanticsProperties (lookupBy_eq_some_mem)

/-- Declared types of the global storage roots (the contract-level
layout); struct bodies come from `structDef`. -/
structure Layout where
  globals : List (Name × Ty)
  deriving Repr

/-- Static type one path segment deeper. -/
def segTy : Ty -> Seg -> Option Ty
  | Ty.ref (RefTy.struct s), Seg.field n => lookupBy n (structDef s)
  | Ty.ref (RefTy.array elem), Seg.at _ => some elem
  | Ty.ref (RefTy.fixed elem _), Seg.at _ => some elem
  | Ty.ref (RefTy.mapping _ value), Seg.at _ => some value
  | _, _ => none

/-- Element/value type of an indexable type (`Seg.at` steps). -/
def elemTy : Ty -> Option Ty
  | Ty.ref (RefTy.array elem) => some elem
  | Ty.ref (RefTy.fixed elem _) => some elem
  | Ty.ref (RefTy.mapping _ value) => some value
  | _ => none

def tyAtSegs : Ty -> List Seg -> Option Ty
  | ty, [] => some ty
  | ty, seg :: rest =>
      match segTy ty seg with
      | some ty' => tyAtSegs ty' rest
      | none => none

/-- Static type of the storage path `root.segs` under the layout. -/
def Layout.tyAt (L : Layout) (root : Name) (segs : List Seg) : Option Ty :=
  match lookupBy root L.globals with
  | some ty => tyAtSegs ty segs
  | none => none

def isNumericTy : Ty -> Bool
  | Ty.prim p => p.isNumeric
  | _ => false

/-- The value inhabits the type. Value-driven on struct fields: every
field *present* in the value must match its `structDef` schema entry
(absent fields make `SVal.find` fail, so they never reach a read).  An
array is of its kind: a dynamic one unmarked, a fixed-size one marked and
exactly as long as its type says. -/
def SVal.hasTy : SVal -> Ty -> Bool
  | SVal.int _, Ty.int => true
  | SVal.int _, Ty.uint => true
  | SVal.bool _, Ty.bool => true
  | SVal.struct fields, Ty.ref (RefTy.struct s) => hasTyFields s fields
  | SVal.array elems shadow fx, Ty.ref (RefTy.array elem) =>
      !fx && hasTyElems elem elems && hasTyElems elem shadow
  | SVal.array elems shadow fx, Ty.ref (RefTy.fixed elem n) =>
      fx && elems.length == n && hasTyElems elem elems && hasTyElems elem shadow
  | SVal.map entries dflt, Ty.ref (RefTy.mapping _ value) =>
      hasTyEntries value entries && dflt.hasTy value
  | _, _ => false
where
  hasTyFields (s : Name) : List (Name × SVal) -> Bool
    | [] => true
    | (n, v) :: rest =>
        (match lookupBy n (structDef s) with
         | some ty => v.hasTy ty
         | none => false) && hasTyFields s rest
  hasTyElems (elem : Ty) : List SVal -> Bool
    | [] => true
    | v :: rest => v.hasTy elem && hasTyElems elem rest
  hasTyEntries (value : Ty) : List (Int × SVal) -> Bool
    | [] => true
    | (_, v) :: rest => v.hasTy value && hasTyEntries value rest

/-- Non-primitive storage value (a tree node): what KeY's `Struct` sort
denotes (arrays and mappings are `Struct` nodes with `at`/`MapField`
fields in `structHeader.key`). -/
def SVal.isRefVal : SVal -> Bool
  | SVal.struct _ => true
  | SVal.array _ _ _ => true
  | SVal.map _ _ => true
  | _ => false

/-! ### Runtime sorts

The KeY sort of a *value* the interpreter holds — the runtime side of
`Ty.keySort`, which is the static side. The two do not always agree,
and that is the point of having both: a storage array or mapping is a
`Struct` node at runtime (`structRules.key` builds it from `mtSt` with
`at(i)` fields, and the copy taclets read it `find<[Struct]>`), while
its static type's sort is `T[]` / `mapping(K => V)`, a sibling of
`Struct` below `StValue`. `Counterexamples/StaticRuntimeSort.lean`
exhibits the gap. -/

def PrimVal.keySort : PrimVal -> KeySort
  | PrimVal.int _ => KeySort.int
  | PrimVal.bool _ => KeySort.bool

/-- The sort of a storage value: `Prim` subsorts for the primitives,
`Struct` for every tree node. -/
def SVal.keySort : SVal -> KeySort
  | SVal.prim p => p.keySort
  | SVal.struct _ => KeySort.struct
  | SVal.array _ _ _ => KeySort.struct
  | SVal.map _ _ => KeySort.struct

/-- The sort of a memory slot value: `Prim` subsorts inline, `Identity`
for a reference. -/
def MVal.keySort : MVal -> KeySort
  | MVal.prim p => p.keySort
  | MVal.ref _ => KeySort.identity

/-- Every storage value is an `StValue` — the runtime content of
`save(Struct, List, StValue)`, and why a `find<[StValue]>` read claims
nothing. -/
theorem SVal.keySort_le_stValue (v : SVal) :
    (v.keySort).le KeySort.stValue = true := by
  cases v with
  | prim p => cases p <;> rfl
  | _ => rfl

/-- Every memory value is a `MemValue` — `write(Memory, Identity, Field, MemValue)`. -/
theorem MVal.keySort_le_memValue (m : MVal) :
    (m.keySort).le KeySort.memValue = true := by
  cases m with
  | prim p => cases p <;> rfl
  | ref _ => rfl

/-- A tree node is exactly a `Struct`-sorted value. -/
theorem SVal.isRefVal_iff_keySort_struct (v : SVal) :
    v.isRefVal = true ↔ v.keySort = KeySort.struct := by
  cases v with
  | prim p => cases p <;> simp [SVal.isRefVal, SVal.keySort, PrimVal.keySort]
  | _ => simp [SVal.isRefVal, SVal.keySort]

/-- On primitive types the static and runtime sorts agree: a well-typed
`int`/`uint` cell holds an `int`, a `bool` cell a `bool`. -/
theorem hasTy_keySort_of_primitive {ty : Ty} {v : SVal}
    (hprim : ty.isPrimitive = true) (h : v.hasTy ty = true) :
    v.keySort = ty.keySort false := by
  cases ty with
  | prim pt =>
      cases v with
      | prim pv => cases pt <;> cases pv <;> simp [SVal.hasTy] at h <;> rfl
      | struct fields => simp [SVal.hasTy] at h
      | array elems => simp [SVal.hasTy] at h
      | map entries dflt => simp [SVal.hasTy] at h
  | ref r => simp [Ty.isPrimitive] at hprim

/-- Every declared global root is present with a value of its type. -/
def wellTypedStorageB (L : Layout) (storage : List (Name × SVal)) : Bool :=
  L.globals.all fun g =>
    match lookupBy g.1 storage with
    | some v => v.hasTy g.2
    | none => false

/-! ## Association-list and `hasTy` inversion lemmas -/

theorem hasTyFields_lookup {s : Name} {fields : List (Name × SVal)}
    {n : Name} {v : SVal}
    (hwt : SVal.hasTy.hasTyFields s fields = true)
    (hlook : lookupBy n fields = some v) :
    ∃ ty, lookupBy n (structDef s) = some ty ∧ v.hasTy ty = true := by
  induction fields with
  | nil => simp [lookupBy] at hlook
  | cons p rest ih =>
      obtain ⟨n', v'⟩ := p
      simp only [SVal.hasTy.hasTyFields, Bool.and_eq_true] at hwt
      by_cases hn : n = n'
      · subst hn
        simp [lookupBy] at hlook
        subst hlook
        cases hdef : lookupBy n (structDef s) with
        | none => rw [hdef] at hwt; simp at hwt
        | some ty =>
            rw [hdef] at hwt
            exact ⟨ty, rfl, hwt.1⟩
      · simp [lookupBy, hn] at hlook
        exact ih hwt.2 hlook

theorem hasTyElems_mem {elem : Ty} {elems : List SVal} {v : SVal}
    (hwt : SVal.hasTy.hasTyElems elem elems = true) (hmem : v ∈ elems) :
    v.hasTy elem = true := by
  induction elems with
  | nil => cases hmem
  | cons w rest ih =>
      simp only [SVal.hasTy.hasTyElems, Bool.and_eq_true] at hwt
      cases hmem with
      | head => exact hwt.1
      | tail _ hmem => exact ih hwt.2 hmem

/-- A slot of a typed array, live or past the end, is typed. -/
theorem hasTyElems_mem_append {elem : Ty} {xs ys : List SVal} {v : SVal}
    (hx : SVal.hasTy.hasTyElems elem xs = true) (hy : SVal.hasTy.hasTyElems elem ys = true)
    (hmem : v ∈ xs ++ ys) : v.hasTy elem = true :=
  (List.mem_append.mp hmem).elim (hasTyElems_mem hx) (hasTyElems_mem hy)

theorem hasTyEntries_lookup {value : Ty} {entries : List (Int × SVal)}
    {i : Int} {v : SVal}
    (hwt : SVal.hasTy.hasTyEntries value entries = true)
    (hlook : lookupBy i entries = some v) : v.hasTy value = true := by
  induction entries with
  | nil => simp [lookupBy] at hlook
  | cons p rest ih =>
      obtain ⟨i', v'⟩ := p
      simp only [SVal.hasTy.hasTyEntries, Bool.and_eq_true] at hwt
      by_cases hi : i = i'
      · subst hi
        simp [lookupBy] at hlook
        subst hlook
        exact hwt.1
      · simp [lookupBy, hi] at hlook
        exact ih hwt.2 hlook

theorem hasTy_numeric {ty : Ty} {v : SVal} (hnum : isNumericTy ty = true)
    (h : v.hasTy ty = true) : ∃ n, v = SVal.int n := by
  cases ty with
  | prim pt =>
      cases v with
      | prim pv =>
          cases pt <;> simp [isNumericTy, PrimTy.isNumeric] at hnum <;>
            cases pv <;> simp [SVal.hasTy] at h <;> exact ⟨_, rfl⟩
      | struct fields => simp [SVal.hasTy] at h
      | array elems => simp [SVal.hasTy] at h
      | map entries dflt => simp [SVal.hasTy] at h
  | ref r => simp [isNumericTy] at hnum

theorem hasTy_isRefVal {ty : Ty} {v : SVal} (href : ty.isReference = true)
    (h : v.hasTy ty = true) : v.isRefVal = true := by
  cases ty with
  | ref ref => cases ref <;> cases v <;>
      simp_all [SVal.hasTy, SVal.isRefVal]
  | _ => simp [Ty.isReference, Ty.isPrimitive] at href

/-! ## `find` preserves typing -/

theorem find_hasTy {segs : List Seg} :
    ∀ {v : SVal} {ty ty' : Ty} {w : SVal},
      v.hasTy ty = true -> tyAtSegs ty segs = some ty' ->
      v.find segs = Except.ok w -> w.hasTy ty' = true := by
  induction segs with
  | nil =>
      intro v ty ty' w hty hsegs hfind
      simp [tyAtSegs] at hsegs
      simp [SVal.find] at hfind
      subst hsegs hfind
      exact hty
  | cons seg rest ih =>
      intro v ty ty' w hty hsegs hfind
      simp only [tyAtSegs] at hsegs
      cases hseg : segTy ty seg with
      | none => rw [hseg] at hsegs; simp at hsegs
      | some tym =>
          rw [hseg] at hsegs
          simp at hsegs
          cases seg with
          | field n =>
              -- `segTy ty (field n)` forces `ty = ref (struct s)`.
              cases ty with
              | ref ref =>
                  cases ref with
                  | struct s =>
                      simp only [segTy] at hseg
                      cases v <;> simp [SVal.hasTy] at hty
                      case struct fields =>
                        simp only [SVal.find] at hfind
                        cases hlook : lookupBy n fields with
                        | none => rw [hlook] at hfind; simp at hfind
                        | some v' =>
                            rw [hlook] at hfind
                            obtain ⟨tyf, hdef, htyv⟩ :=
                              hasTyFields_lookup hty hlook
                            rw [hseg] at hdef
                            cases hdef
                            exact ih htyv hsegs hfind
                  | array elem => simp [segTy] at hseg
                  | fixed elem _ => simp [segTy] at hseg
                  | mapping key value => simp [segTy] at hseg
              | _ => simp [segTy] at hseg
          | «at» i =>
              cases ty with
              | ref ref =>
                  cases ref with
                  | struct s => simp [segTy] at hseg
                  | array elem =>
                      simp only [segTy] at hseg
                      cases hseg
                      cases v <;> simp [SVal.hasTy] at hty
                      case array elems shadow fx =>
                        simp only [SVal.find] at hfind
                        split at hfind
                        · exact ih
                            (hasTyElems_mem_append hty.1.2 hty.2 ((elems ++ shadow).get_mem _))
                            hsegs hfind
                        · simp at hfind
                  | fixed elem n =>
                      simp only [segTy] at hseg
                      cases hseg
                      cases v <;> simp [SVal.hasTy] at hty
                      case array elems shadow fx =>
                        simp only [SVal.find] at hfind
                        split at hfind
                        · exact ih
                            (hasTyElems_mem_append hty.1.2 hty.2 ((elems ++ shadow).get_mem _))
                            hsegs hfind
                        · simp at hfind
                  | mapping key value =>
                      simp only [segTy] at hseg
                      cases hseg
                      cases v <;> simp [SVal.hasTy] at hty
                      case map entries dflt =>
                        simp only [SVal.find] at hfind
                        cases hlook : lookupBy i entries with
                        | none =>
                            rw [hlook] at hfind
                            exact ih hty.2 hsegs hfind
                        | some v' =>
                            rw [hlook] at hfind
                            exact ih (hasTyEntries_lookup hty.1 hlook)
                              hsegs hfind
              | _ => simp [segTy] at hseg

theorem findStorage_hasTy {L : Layout} {s : State} {root : Name}
    {segs : List Seg} {ty' : Ty} {v : SVal}
    (hst : wellTypedStorageB L s.storage = true)
    (hty : L.tyAt root segs = some ty')
    (hfind : s.findStorage root segs = Except.ok v) :
    v.hasTy ty' = true := by
  simp only [Layout.tyAt] at hty
  cases hglob : lookupBy root L.globals with
  | none => rw [hglob] at hty; simp at hty
  | some ty0 =>
      rw [hglob] at hty
      have hmem := lookupBy_eq_some_mem hglob
      have hall := (List.all_eq_true.mp hst) _ hmem
      simp only [State.findStorage] at hfind
      cases hroot : lookupBy root s.storage with
      | none => rw [hroot] at hfind; simp at hfind
      | some v0 =>
          rw [hroot] at hfind
          rw [hroot] at hall
          exact find_hasTy hall hty hfind

/-! ## `tyAt` under path extension -/

theorem tyAtSegs_append_seg {ty t t' : Ty} {segs : List Seg} {seg : Seg}
    (h : tyAtSegs ty segs = some t) (hseg : segTy t seg = some t') :
    tyAtSegs ty (segs ++ [seg]) = some t' := by
  induction segs generalizing ty with
  | nil =>
      simp [tyAtSegs] at h
      subst h
      simp [tyAtSegs, hseg]
  | cons s0 rest ih =>
      simp only [tyAtSegs] at h
      cases h0 : segTy ty s0 with
      | none => rw [h0] at h; simp at h
      | some tym =>
          rw [h0] at h
          simp only [List.cons_append, tyAtSegs, h0]
          exact ih h

/-- A typed path starts at a declared root: `alice.age` at `Person`'s `age`. -/
theorem Layout.tyAt_split {L : Layout} {r : Name} {segs : List Seg} {T' : Ty}
    (h : L.tyAt r segs = some T') :
    ∃ T, lookupBy r L.globals = some T ∧ tyAtSegs T segs = some T' := by
  simp only [Layout.tyAt] at h
  split at h
  · rename_i T hr; exact ⟨T, hr, h⟩
  · exact nomatch h

theorem tyAt_append_seg {L : Layout} {root : Name} {segs : List Seg}
    {seg : Seg} {t t' : Ty} (h : L.tyAt root segs = some t)
    (hseg : segTy t seg = some t') :
    L.tyAt root (segs ++ [seg]) = some t' := by
  simp only [Layout.tyAt] at h ⊢
  cases hglob : lookupBy root L.globals with
  | none => rw [hglob] at h; simp at h
  | some ty0 =>
      rw [hglob] at h
      exact tyAtSegs_append_seg h hseg

/-! ## Inverting the writes

What a write that returned did, one lemma per interpreter step, so the
invariant proofs (`Soundness`, `Reachability`, `Constructibility`) do not
each re-run its `bind`s. -/

/-- `bind_inv h` drops the first step of the run `h` returned from:
`obtain ⟨_, _, h⟩ := bind_ok_inv h`. -/
macro "bind_inv " h:ident : tactic => `(tactic| obtain ⟨_, _, $h⟩ := bind_ok_inv $h)

theorem Value.asInt_ok {v : Value} {n : Int} (h : v.asInt = .ok n) : v = .int n := by
  cases v with
  | int m => cases h; rfl
  | bool _ => exact nomatch h

/-- An assignment's storage write saved the value, or laid it over what was there. -/
theorem State.writeStorage_ok_inv {σ σ' : State} {r : Name} {segs : List Seg} {new : SVal}
    (h : σ.writeStorage r segs new = .ok σ') :
    σ.saveStorage r segs new = .ok σ' ∨
      ∃ cur, σ.findStorage r segs = .ok cur ∧ σ.saveStorage r segs (cur.overlay new) = .ok σ' := by
  unfold State.writeStorage at h
  split at h
  · exact .inl h
  all_goals
    obtain ⟨cur, hcur, h⟩ := bind_ok_inv h
    exact .inr ⟨cur, hcur, h⟩

/-- `alice.age += x;` saved the checked result of the operation. -/
theorem opStore_ok_inv {σ σ' : State} {op : BinOp} {p : PrimTy} {r : Name} {segs : List Seg}
    {v : Value} (h : opStore σ op p r segs v = .ok σ') :
    ∃ old n new, applyBinOp op old v = .ok n ∧ checkArith (.prim p) n = .ok new ∧
      σ.saveStorage r segs new.toSVal = .ok σ' := by
  bind_inv h
  obtain ⟨old, _, h⟩ := bind_ok_inv h
  obtain ⟨n, hn, h⟩ := bind_ok_inv h
  obtain ⟨new, hnew, h⟩ := bind_ok_inv h
  exact ⟨old, n, new, hn, hnew, h⟩

/-- `m.age += x;` wrote the checked result of the operation. -/
theorem opMem_ok_inv {σ σ' : State} {op : BinOp} {p : PrimTy} {loc : Addr} {v : Value}
    (h : opMem σ op p loc v = .ok σ') :
    ∃ old n new, applyBinOp op old v = .ok n ∧ checkArith (.prim p) n = .ok new ∧
      writeLoc σ loc new = .ok σ' := by
  obtain ⟨old, _, h⟩ := bind_ok_inv h
  obtain ⟨n, hn, h⟩ := bind_ok_inv h
  obtain ⟨new, hnew, h⟩ := bind_ok_inv h
  exact ⟨old, n, new, hn, hnew, h⟩

/-- `alice.age++` saved the checked bump of the number it read, and yields
the new number or the old one. -/
theorem bumpStore_ok_inv {σ σ' : State} {op : IncDec} {p : PrimTy} {r : Name}
    {segs : List Seg} {w : Value} (h : bumpStore σ op p r segs = .ok (σ', w)) :
    ∃ m new, checkArith (.prim p) (.int (if op.isIncrement then m + 1 else m - 1)) = .ok new ∧
      σ.saveStorage r segs new.toSVal = .ok σ' ∧ w = (if op.isPre then new else .int m) := by
  bind_inv h
  obtain ⟨old, _, h⟩ := bind_ok_inv h
  obtain ⟨m, hm, h⟩ := bind_ok_inv h
  obtain ⟨new, hnew, h⟩ := bind_ok_inv h
  obtain ⟨σ₁, hσ₁, h⟩ := bind_ok_inv h
  cases h
  cases Value.asInt_ok hm
  exact ⟨m, new, hnew, hσ₁, rfl⟩

/-- `m.age++` wrote the checked bump of the number it read, and yields the
new number or the old one. -/
theorem bumpMem_ok_inv {σ σ' : State} {op : IncDec} {p : PrimTy} {loc : Addr} {w : Value}
    (h : bumpMem σ op p loc = .ok (σ', w)) :
    ∃ m new, checkArith (.prim p) (.int (if op.isIncrement then m + 1 else m - 1)) = .ok new ∧
      writeLoc σ loc new = .ok σ' ∧ w = (if op.isPre then new else .int m) := by
  obtain ⟨old, _, h⟩ := bind_ok_inv h
  obtain ⟨m, hm, h⟩ := bind_ok_inv h
  obtain ⟨new, hnew, h⟩ := bind_ok_inv h
  obtain ⟨σ₁, hσ₁, h⟩ := bind_ok_inv h
  cases h
  cases Value.asInt_ok hm
  exact ⟨m, new, hnew, hσ₁, rfl⟩

end Semantics
end Solidity
