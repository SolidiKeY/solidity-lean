import Solidity.Semantics
import Solidity.RuleSoundness

/-!
# Storage layout typing

The typing layer the sort-faithfulness theorems
(`SortFaithfulness.lean`) run on. The interpreter's storage
(`State.storage`) is untyped; a `Layout` declares the static types of
the global storage roots (the per-contract layout), with struct bodies
coming from `Semantics.structDef`. `SVal.hasTy` says a storage value
inhabits a type, `wellTypedStorageB` lifts that to whole storages, and
`wtStorageExpr` checks that a *simple-shaped* storage place expression's
type annotations agree with the layout (resolved through the env's
`spath` aliases, exactly mirroring `resolveS`).

The workhorse lemmas connect the static side to the interpreter:
`resolveS_wt_tyAt` (a well-annotated place resolves purely to a path
whose layout type is the expression's annotation) and
`findStorage_hasTy` (the value found at a layout-typed path inhabits
that type); together they give `generic_read_hasTy`, the semantic
content of every varcond-resolved (`\hasSort`-family) taclet read.
-/

namespace Solidity
namespace Semantics

/-- Declared types of the global storage roots (the contract-level
layout); struct bodies come from `structDef`. -/
structure Layout where
  globals : List (Name × Ty)
  deriving Repr

/-- Static type one path segment deeper. -/
def segTy : Ty -> Seg -> Option Ty
  | Ty.ref (RefTy.struct s), Seg.field n => lookupBy n (structDef s)
  | Ty.ref (RefTy.array elem), Seg.at _ => some elem
  | Ty.ref (RefTy.mapping _ value), Seg.at _ => some value
  | _, _ => none

/-- Element/value type of an indexable type (`Seg.at` steps). -/
def elemTy : Ty -> Option Ty
  | Ty.ref (RefTy.array elem) => some elem
  | Ty.ref (RefTy.mapping _ value) => some value
  | _ => none

theorem segTy_at (ty : Ty) (i : Int) : segTy ty (Seg.at i) = elemTy ty := by
  cases ty with
  | ref ref => cases ref <;> rfl
  | _ => rfl

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
(absent fields make `SVal.find` fail, so they never reach a read). -/
def SVal.hasTy : SVal -> Ty -> Bool
  | SVal.int _, Ty.int => true
  | SVal.int _, Ty.uint => true
  | SVal.bool _, Ty.bool => true
  | SVal.struct fields, Ty.ref (RefTy.struct s) => hasTyFields s fields
  | SVal.array elems, Ty.ref (RefTy.array elem) => hasTyElems elem elems
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
  | SVal.array _ => true
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
  | SVal.array _ => KeySort.struct
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

/-- The expression's storage annotations agree with the layout, resolved
through the env's `spath` aliases. Only the simple place shapes the
read-bearing taclets match (`var`, `field`/`index` over a simple base)
are accepted; everything else is `false`. Mirrors `resolveS` arm for
arm, including env shadowing of globals. -/
def wtStorageExpr (L : Layout) (env : List (Name × Binding)) :
    WrappedExpr -> Bool
  | WrappedExpr.var Kind.storage ty fld =>
      match lookupBy fld.name env with
      | some (Binding.spath root segs) => L.tyAt root segs == some ty
      | some _ => false
      | none =>
          fld.origin == some StorageOrigin.global &&
            lookupBy fld.name L.globals == some ty
  | WrappedExpr.field Kind.storage ty base fld =>
      base.simple && wtStorageExpr L env base &&
        segTy base.ty (Seg.field fld.name) == some ty
  | WrappedExpr.index Kind.storage ty base index =>
      base.simple && wtStorageExpr L env base && index.simple &&
        elemTy base.ty == some ty
  | _ => false

/-- The fragment of Solidity's static typing that sort-faithfulness
leans on, per statement shape: assignment sides agree in type, memory
places are reference-typed (`bool memory` is not Solidity), compound
assignment and `++`/`--` targets are numeric, pushed values have the
array's element type. -/
def stmtTypingOk : Stmt -> Bool
  | Stmt.assign lhs rhs =>
      lhs.expr.ty == rhs.ty &&
        (!lhs.expr.isMemory || lhs.expr.ty.isReference) &&
        (match rhs with
         | WrappedExpr.incDec _ target => isNumericTy target.ty
         | _ => true)
  | Stmt.compoundAssign _ lhs _ => isNumericTy lhs.expr.ty
  | Stmt.expr (WrappedExpr.incDec _ target) => isNumericTy target.ty
  | Stmt.push target (some value) => elemTy target.expr.ty == some value.ty
  | Stmt.pushAssign target value => elemTy target.expr.ty == some value.ty
  | _ => true

/-! ## Association-list and `hasTy` inversion lemmas -/

theorem lookupBy_eq_some_mem [DecidableEq κ] {k : κ} {l : List (κ × α)}
    {v : α} (h : lookupBy k l = some v) : (k, v) ∈ l := by
  induction l with
  | nil => simp [lookupBy] at h
  | cons p rest ih =>
      obtain ⟨k', v'⟩ := p
      by_cases hk : k = k'
      · subst hk
        simp [lookupBy] at h
        simp [h]
      · simp [lookupBy, hk] at h
        exact List.mem_cons_of_mem _ (ih h)

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

theorem hasTy_bool {v : SVal} (h : v.hasTy Ty.bool = true) :
    ∃ b, v = SVal.bool b := by
  cases v with
  | prim pv => cases pv <;> simp [SVal.hasTy] at h <;> exact ⟨_, rfl⟩
  | _ => simp [SVal.hasTy] at h

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
                      case array elems =>
                        simp only [SVal.find] at hfind
                        split at hfind
                        · exact ih
                            (hasTyElems_mem hty (elems.get_mem _))
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

/-! ## Purity of simple-expression evaluation -/

/-- Simple expressions are pure (`RuleSoundness.pureExpr`), so the
purity kit of `RuleSoundness` applies to them. -/
theorem simple_pureExpr {e : WrappedExpr} (hsimple : e.simple = true) :
    RuleSoundness.pureExpr e = true := by
  cases e <;> first
    | rfl
    | exact Bool.noConfusion hsimple

theorem evalInt_simple_pure {s s' : State} {e : WrappedExpr} {i : Int}
    (hsimple : e.simple = true)
    (h : evalInt s e = Except.ok (s', i)) : s' = s :=
  RuleSoundness.evalInt_pure (simple_pureExpr hsimple) h

/-! ## `resolveS` on well-annotated simple places -/

/-- A well-annotated simple storage place is a storage variable. -/
theorem wt_simple_var {L : Layout} {env : List (Name × Binding)}
    {e : WrappedExpr} (hsimple : e.simple = true)
    (hwt : wtStorageExpr L env e = true) :
    ∃ ty fld, e = WrappedExpr.var Kind.storage ty fld := by
  cases e
  case var kind ty fld =>
    cases kind
    case storage => exact ⟨ty, fld, rfl⟩
    all_goals exact Bool.noConfusion hwt
  case bool b => exact Bool.noConfusion hwt
  case intLit ty v => exact Bool.noConfusion hwt
  all_goals exact Bool.noConfusion hsimple

theorem resolveS_var_tyAt {L : Layout} {s s' : State} {ty : Ty}
    {fld : Field} {root : Name} {segs : List Seg}
    (hwt : wtStorageExpr L s.env (WrappedExpr.var Kind.storage ty fld) = true)
    (h : resolveS s (WrappedExpr.var Kind.storage ty fld) =
      Except.ok (s', root, segs)) :
    s' = s ∧ L.tyAt root segs = some ty := by
  rw [resolveS] at h
  simp only [wtStorageExpr] at hwt
  cases henv : lookupBy fld.name s.env with
  | none =>
      rw [henv] at h hwt
      simp [Bool.and_eq_true, beq_iff_eq] at hwt
      simp only [hwt.1] at h
      simp at h
      obtain ⟨hs, hroot, hsegs⟩ := h
      subst hs hroot hsegs
      exact ⟨rfl, by simp [Layout.tyAt, hwt.2, tyAtSegs]⟩
  | some b =>
      rw [henv] at h hwt
      cases b <;> simp at h hwt
      case spath root0 segs0 =>
        obtain ⟨hs, hroot, hsegs⟩ := h
        subst hs hroot hsegs
        exact ⟨rfl, by simpa [beq_iff_eq] using hwt⟩

/-- The master lemma: a well-annotated (simple-shaped) storage place
resolves without touching the state, to a path whose layout type is the
expression's own type annotation. -/
theorem resolveS_wt_tyAt {L : Layout} {s s' : State} {e : WrappedExpr}
    {root : Name} {segs : List Seg}
    (hwt : wtStorageExpr L s.env e = true)
    (h : resolveS s e = Except.ok (s', root, segs)) :
    s' = s ∧ L.tyAt root segs = some e.ty := by
  cases e
  case bool b => exact Bool.noConfusion hwt
  case intLit ty v => exact Bool.noConfusion hwt
  case pushPlace target => exact Bool.noConfusion hwt
  case mkCall kind ty name args => exact Bool.noConfusion hwt
  case mkBinop op l r => exact Bool.noConfusion hwt
  case mkUnop op arg => exact Bool.noConfusion hwt
  case mkIncDec op target => exact Bool.noConfusion hwt
  case mkTernary cond thn els => exact Bool.noConfusion hwt
  case var kind ty fld =>
    cases kind
    case memory => exact Bool.noConfusion hwt
    case stack => exact Bool.noConfusion hwt
    case storage => exact resolveS_var_tyAt hwt h
  case field kind ty base fld =>
    cases kind
    case memory => exact Bool.noConfusion hwt
    case stack => exact Bool.noConfusion hwt
    case storage =>
    simp only [wtStorageExpr, Bool.and_eq_true] at hwt
    obtain ⟨⟨hbsimple, hbwt⟩, hfty⟩ := hwt
    obtain ⟨bty, bfld, hbase⟩ := wt_simple_var hbsimple hbwt
    subst hbase
    rw [resolveS] at h
    obtain ⟨⟨s1, root1, segs1⟩, hres, h⟩ := RuleSoundness.bind_ok_inv h
    simp at h
    obtain ⟨hs, hroot, hsegs⟩ := h
    obtain ⟨hs1, hty1⟩ := resolveS_var_tyAt hbwt hres
    subst hs1 hs hroot hsegs
    refine ⟨rfl, ?_⟩
    have hseg : segTy bty (Seg.field fld.name) = some ty := by
      simpa [beq_iff_eq, WrappedExpr.ty, Typed.WrappedExpr.ty] using hfty
    simpa [WrappedExpr.ty, Typed.WrappedExpr.ty]
      using tyAt_append_seg hty1 hseg
  case index kind ty base index =>
    cases kind
    case memory => exact Bool.noConfusion hwt
    case stack => exact Bool.noConfusion hwt
    case storage =>
    simp only [wtStorageExpr, Bool.and_eq_true] at hwt
    obtain ⟨⟨⟨hbsimple, hbwt⟩, hisimple⟩, hety⟩ := hwt
    obtain ⟨bty, bfld, hbase⟩ := wt_simple_var hbsimple hbwt
    subst hbase
    rw [resolveS] at h
    obtain ⟨⟨s1, root1, segs1⟩, hres, h⟩ := RuleSoundness.bind_ok_inv h
    obtain ⟨⟨s2, i⟩, hint, h⟩ := RuleSoundness.bind_ok_inv h
    simp at h
    obtain ⟨hs, hroot, hsegs⟩ := h
    obtain ⟨hs1, hty1⟩ := resolveS_var_tyAt hbwt hres
    have hs2 := evalInt_simple_pure hisimple hint
    subst hs1 hs2 hs hroot hsegs
    refine ⟨rfl, ?_⟩
    have hat : segTy bty (Seg.at i) = some ty := by
      rw [segTy_at]
      simpa [beq_iff_eq, WrappedExpr.ty, Typed.WrappedExpr.ty] using hety
    simpa [WrappedExpr.ty, Typed.WrappedExpr.ty]
      using tyAt_append_seg hty1 hat

/-- Semantic content of every varcond-resolved (`\hasSort`-family)
taclet read: the value actually found at a well-annotated storage place
inhabits the place's static type. -/
theorem generic_read_hasTy {L : Layout} {s s' : State} {e : WrappedExpr}
    {root : Name} {segs : List Seg} {v : SVal}
    (hst : wellTypedStorageB L s.storage = true)
    (hwt : wtStorageExpr L s.env e = true)
    (hres : resolveS s e = Except.ok (s', root, segs))
    (hfind : s'.findStorage root segs = Except.ok v) :
    v.hasTy e.ty = true := by
  obtain ⟨hs, hty⟩ := resolveS_wt_tyAt hwt hres
  subst hs
  exact findStorage_hasTy hst hty hfind

end Semantics
end Solidity
