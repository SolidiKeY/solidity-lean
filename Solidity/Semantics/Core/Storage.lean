import Solidity.Semantics.Core.Value
import Solidity.Eqns

/-!
# Typed storage

A storage value indexed by its type (`docs/intrinsic.md`, Decision 4, M4b):
`SVal T` is the tree of `structRules.key` with the shape `T` gives it, so a
struct has exactly the members `structDef` lists, in order, each of its own
type, an array's elements are all of its element type, a fixed-size array has
exactly its length, and a mapping's values are all of its value type.
`Storage C` is the contract's state variables as one such struct
(`SFields C.vars`), and a typed path `Path T U` leads from a `T` to a `U`, so
the storage operations are total except where the program's index is out of
bounds: they return an `Option`, `none` for that revert (`toRes`).

The shapes mirror `Semantics.SVal`'s, which `SVal.erase` reads off: an array
keeps the slots past its end (`shadow`), a mapping its default.  A
fixed-size array keeps none (no operation puts one there).  Each operation
follows its untyped namesake in `Semantics.lean` line for line, and
`Semantics/Core/StorageErase.lean` proves that it erases to it.

Defaults (`SVal.dflt`) are structural on the rank `structDef_rank_lt`
certifies, so the kernel can reduce them, where `defaultForTy` is
well-founded; their fuel is `rankBound`, which reads no struct name.

Nothing the kernel evaluates `match`es on the indexed families (Gate G0,
conditions 1 and 2): `find`, `findLive`, `save` and `SFields.get`/`set` are
written with the recursors (`Path.rec` over `SVal.view`, `SFields.rec`), the
functions on a whole value are folds (`SVal.fold`), and the array operations
read their array through `SVal.view`.  Each has a `match` twin as its
compiled form; the folds state their equations and are irreducible, so a
proof rewrites them as it would a `match` (`Solidity/Eqns.lean`).
-/

namespace Solidity.Core

open Semantics (structDef lookupBy setBy tyRank fieldsRank structRank)

mutual
/-- A storage value of type `T`. -/
inductive SVal : Ty → Type where
  | prim {p : PrimTy} (v : p.Denote) : SVal (.prim p)
  | struct {s : Name} (fs : SFields (structDef s)) : SVal (.ref (.struct s))
  /-- The live elements and the slots past the end (`Semantics.SVal.array`). -/
  | array {E : Ty} (elems shadow : SList E) : SVal (.ref (.array E))
  | fixed {E : Ty} {n : Nat} (elems : SVec E n) : SVal (.ref (.fixed E n))
  /-- The entries written and the value of every other key. -/
  | map {K V : Ty} (entries : SMap V) (dflt : SVal V) : SVal (.ref (.mapping K V))

/-- One value per member, of the member's type, in the members' order. -/
inductive SFields : List (Name × Ty) → Type where
  | nil : SFields []
  | cons {f : Name} {T : Ty} {fs : List (Name × Ty)} (v : SVal T) (rest : SFields fs) :
      SFields ((f, T) :: fs)

/-- A list of values of one type. -/
inductive SList : Ty → Type where
  | nil {E : Ty} : SList E
  | cons {E : Ty} (v : SVal E) (rest : SList E) : SList E

/-- Exactly `n` values of one type. -/
inductive SVec : Ty → Nat → Type where
  | nil {E : Ty} : SVec E 0
  | cons {E : Ty} {n : Nat} (v : SVal E) (rest : SVec E n) : SVec E (n + 1)

/-- A mapping's entries, by key. -/
inductive SMap : Ty → Type where
  | nil {V : Ty} : SMap V
  | cons {V : Ty} (k : Int) (v : SVal V) (rest : SMap V) : SMap V
end

/-! ## Folds

Every function the kernel evaluates on a whole value (`SVal.erase`,
`defaultOf`, `strip`, `overlay`, `beq`, the `toList`s, `SVal.copyStToM`) is
one fold: what it computes at each type (`Fold.V`, …) and its step at each
constructor, given the results on the constructor's arguments.  A fold is the
recursor of the five families (Gate G0, conditions 1 and 2: no `match` on an
indexed family, whose casts the kernel pays per step), and `SVal.foldM`, by
`match`, its compiled form.  Each function states its equations by `rfl` and
names them its equation lemmas (`Solidity/Eqns.lean`), so proofs unfold it as
they would a `match`.

A step reads a second value of the same type through a view (`SVal.view`,
`SFields.view`, `SVec.view`, `SList.uncons`, `SMap.uncons`), a `casesOn`
whose result type is computed from the index, so it casts nothing. -/

/-- A fold over storage values: its result at each type, and its step at each
constructor. -/
structure Fold where
  V : Ty → Type
  F : List (Name × Ty) → Type
  L : Ty → Type
  W : Ty → Nat → Type
  M : Ty → Type
  prim : {p : PrimTy} → p.Denote → V (.prim p)
  struct : {s : Name} → SFields (structDef s) → F (structDef s) → V (.ref (.struct s))
  array : {E : Ty} → SList E → SList E → L E → L E → V (.ref (.array E))
  fixed : {E : Ty} → {n : Nat} → SVec E n → W E n → V (.ref (.fixed E n))
  map : {K U : Ty} → SMap U → SVal U → M U → V U → V (.ref (.mapping K U))
  fnil : F []
  fcons : {f : Name} → {T : Ty} → {fs : List (Name × Ty)} → SVal T → SFields fs → V T → F fs →
    F ((f, T) :: fs)
  lnil : {E : Ty} → L E
  lcons : {E : Ty} → SVal E → SList E → V E → L E → L E
  wnil : {E : Ty} → W E 0
  wcons : {E : Ty} → {n : Nat} → SVal E → SVec E n → V E → W E n → W E (n + 1)
  mnil : {U : Ty} → M U
  mcons : {U : Ty} → Int → SVal U → SMap U → V U → M U → M U

mutual
/-- `SVal.fold` by `match`, its compiled form. -/
def SVal.foldM (a : Fold) : {T : Ty} → SVal T → a.V T
  | _, .prim v => a.prim v
  | _, .struct fs => a.struct fs (SFields.foldM a fs)
  | _, .array e sh => a.array e sh (SList.foldM a e) (SList.foldM a sh)
  | _, .fixed e => a.fixed e (SVec.foldM a e)
  | _, .map m d => a.map m d (SMap.foldM a m) (SVal.foldM a d)

def SFields.foldM (a : Fold) : {fs : List (Name × Ty)} → SFields fs → a.F fs
  | _, .nil => a.fnil
  | _, .cons v rest => a.fcons v rest (SVal.foldM a v) (SFields.foldM a rest)

def SList.foldM (a : Fold) : {E : Ty} → SList E → a.L E
  | _, .nil => a.lnil
  | _, .cons v rest => a.lcons v rest (SVal.foldM a v) (SList.foldM a rest)

def SVec.foldM (a : Fold) : {E : Ty} → {n : Nat} → SVec E n → a.W E n
  | _, _, .nil => a.wnil
  | _, _, .cons v rest => a.wcons v rest (SVal.foldM a v) (SVec.foldM a rest)

def SMap.foldM (a : Fold) : {U : Ty} → SMap U → a.M U
  | _, .nil => a.mnil
  | _, .cons k v rest => a.mcons k v rest (SVal.foldM a v) (SMap.foldM a rest)
end

/-- A fold of a value, by the recursor. -/
@[implemented_by SVal.foldM]
def SVal.fold (a : Fold) {T : Ty} (v : SVal T) : a.V T :=
  @SVal.rec (fun T _ => a.V T) (fun fs _ => a.F fs) (fun E _ => a.L E) (fun E n _ => a.W E n)
    (fun U _ => a.M U) a.prim a.struct a.array a.fixed a.map a.fnil a.fcons a.lnil a.lcons
    a.wnil a.wcons a.mnil a.mcons T v

@[implemented_by SFields.foldM]
def SFields.fold (a : Fold) {fs : List (Name × Ty)} (x : SFields fs) : a.F fs :=
  @SFields.rec (fun T _ => a.V T) (fun fs _ => a.F fs) (fun E _ => a.L E) (fun E n _ => a.W E n)
    (fun U _ => a.M U) a.prim a.struct a.array a.fixed a.map a.fnil a.fcons a.lnil a.lcons
    a.wnil a.wcons a.mnil a.mcons fs x

@[implemented_by SList.foldM]
def SList.fold (a : Fold) {E : Ty} (l : SList E) : a.L E :=
  @SList.rec (fun T _ => a.V T) (fun fs _ => a.F fs) (fun E _ => a.L E) (fun E n _ => a.W E n)
    (fun U _ => a.M U) a.prim a.struct a.array a.fixed a.map a.fnil a.fcons a.lnil a.lcons
    a.wnil a.wcons a.mnil a.mcons E l

@[implemented_by SVec.foldM]
def SVec.fold (a : Fold) {E : Ty} {n : Nat} (l : SVec E n) : a.W E n :=
  @SVec.rec (fun T _ => a.V T) (fun fs _ => a.F fs) (fun E _ => a.L E) (fun E n _ => a.W E n)
    (fun U _ => a.M U) a.prim a.struct a.array a.fixed a.map a.fnil a.fcons a.lnil a.lcons
    a.wnil a.wcons a.mnil a.mcons E n l

@[implemented_by SMap.foldM]
def SMap.fold (a : Fold) {U : Ty} (m : SMap U) : a.M U :=
  @SMap.rec (fun T _ => a.V T) (fun fs _ => a.F fs) (fun E _ => a.L E) (fun E n _ => a.W E n)
    (fun U _ => a.M U) a.prim a.struct a.array a.fixed a.map a.fnil a.fcons a.lnil a.lcons
    a.wnil a.wcons a.mnil a.mcons U m

mutual
theorem SVal.fold_eq_foldM (a : Fold) : {T : Ty} → (v : SVal T) → v.fold a = v.foldM a
  | _, .prim _ => rfl
  | _, .struct fs => by
    show a.struct fs (fs.fold a) = _
    rw [SFields.fold_eq_foldM a fs, SVal.foldM]
  | _, .array e sh => by
    show a.array e sh (e.fold a) (sh.fold a) = _
    rw [SList.fold_eq_foldM a e, SList.fold_eq_foldM a sh, SVal.foldM]
  | _, .fixed e => by
    show a.fixed e (e.fold a) = _
    rw [SVec.fold_eq_foldM a e, SVal.foldM]
  | _, .map m d => by
    show a.map m d (m.fold a) (d.fold a) = _
    rw [SMap.fold_eq_foldM a m, SVal.fold_eq_foldM a d, SVal.foldM]

theorem SFields.fold_eq_foldM (a : Fold) : {fs : List (Name × Ty)} → (x : SFields fs) →
    x.fold a = x.foldM a
  | _, .nil => rfl
  | _, .cons v rest => by
    show a.fcons v rest (v.fold a) (rest.fold a) = _
    rw [SVal.fold_eq_foldM a v, SFields.fold_eq_foldM a rest, SFields.foldM]

theorem SList.fold_eq_foldM (a : Fold) : {E : Ty} → (l : SList E) → l.fold a = l.foldM a
  | _, .nil => rfl
  | _, .cons v rest => by
    show a.lcons v rest (v.fold a) (rest.fold a) = _
    rw [SVal.fold_eq_foldM a v, SList.fold_eq_foldM a rest, SList.foldM]

theorem SVec.fold_eq_foldM (a : Fold) : {E : Ty} → {n : Nat} → (l : SVec E n) →
    l.fold a = l.foldM a
  | _, _, .nil => rfl
  | _, _, .cons v rest => by
    show a.wcons v rest (v.fold a) (rest.fold a) = _
    rw [SVal.fold_eq_foldM a v, SVec.fold_eq_foldM a rest, SVec.foldM]

theorem SMap.fold_eq_foldM (a : Fold) : {U : Ty} → (m : SMap U) → m.fold a = m.foldM a
  | _, .nil => rfl
  | _, .cons k v rest => by
    show a.mcons k v rest (v.fold a) (rest.fold a) = _
    rw [SVal.fold_eq_foldM a v, SMap.fold_eq_foldM a rest, SMap.foldM]
end

/-! ### Views -/

/-- What a value of type `T` holds, by `T`. -/
def Shape : Ty → Type
  | .prim p => p.Denote
  | .ref (.struct s) => SFields (structDef s)
  | .ref (.array E) => SList E × SList E
  | .ref (.fixed E n) => SVec E n
  | .ref (.mapping _ V) => SMap V × SVal V

/-- A value's contents, at the type its type computes. -/
def SVal.view {T : Ty} (v : SVal T) : Shape T :=
  @SVal.casesOn (fun T _ => Shape T) T v (fun {_} x => x) (fun {_} fs => fs)
    (fun {_} e sh => (e, sh)) (fun {_} {_} e => e) (fun {_} {_} m d => (m, d))

theorem SVal.view_prim {p : PrimTy} (x : p.Denote) : (SVal.prim x).view = x := rfl
theorem SVal.view_struct {s : Name} (fs : SFields (structDef s)) : (SVal.struct fs).view = fs := rfl
theorem SVal.view_array {E : Ty} (e sh : SList E) : (SVal.array e sh).view = (e, sh) := rfl
theorem SVal.view_fixed {E : Ty} {n : Nat} (e : SVec E n) : (SVal.fixed e).view = e := rfl
theorem SVal.view_map {K U : Ty} (m : SMap U) (d : SVal U) :
    (SVal.map (K := K) m d).view = (m, d) := rfl

/-- What the members of `fs` hold: the first one and the others. -/
def FShape : List (Name × Ty) → Type
  | [] => Unit
  | (_, T) :: fs => SVal T × SFields fs

/-- Members' contents, at the type their names compute. -/
def SFields.view {fs : List (Name × Ty)} (x : SFields fs) : FShape fs :=
  @SFields.casesOn (fun fs _ => FShape fs) fs x () (fun {_} {_} {_} v rest => (v, rest))

/-- What a vector of `n` values holds: none, or the first and the others. -/
def VShape (E : Ty) : Nat → Type
  | 0 => Unit
  | n + 1 => SVal E × SVec E n

/-- A vector's contents, at the type its length computes. -/
def SVec.view {E : Ty} {n : Nat} (l : SVec E n) : VShape E n :=
  @SVec.casesOn (fun E n _ => VShape E n) E n l () (fun {_} {_} v rest => (v, rest))

/-- A list's first value and the others, if it has one. -/
def SList.uncons {E : Ty} (l : SList E) : Option (SVal E × SList E) :=
  @SList.casesOn (fun E _ => Option (SVal E × SList E)) E l none (fun {_} v rest => some (v, rest))

/-- A mapping's first entry and the others, if it has one. -/
def SMap.uncons {U : Ty} (m : SMap U) : Option (Int × SVal U × SMap U) :=
  @SMap.casesOn (fun U _ => Option (Int × SVal U × SMap U)) U m none
    (fun {_} k v rest => some (k, v, rest))

/-! ## Erasure -/

/-- The untyped value. -/
def eraseFold : Fold where
  V _ := Semantics.SVal
  F _ := List (Name × Semantics.SVal)
  L _ := List Semantics.SVal
  W _ _ := List Semantics.SVal
  M _ := List (Int × Semantics.SVal)
  prim := fun {p} v => .prim (PrimTy.erase (p := p) v)
  struct := fun _ ih => .struct ih
  array := fun _ _ ie ish => .array ie ish false
  fixed := fun _ ie => .array ie [] true
  map := fun _ _ im id => .map im id
  fnil := []
  fcons := fun {f} {_} {_} _ _ iv ir => (f, iv) :: ir
  lnil := []
  lcons := fun _ _ iv ir => iv :: ir
  wnil := []
  wcons := fun _ _ iv ir => iv :: ir
  mnil := []
  mcons := fun k _ _ iv ir => (k, iv) :: ir

/-- The untyped value. -/
def SVal.erase {T : Ty} (v : SVal T) : Semantics.SVal := v.fold eraseFold
def SFields.erase {fs : List (Name × Ty)} (x : SFields fs) : List (Name × Semantics.SVal) :=
  x.fold eraseFold
def SList.erase {E : Ty} (l : SList E) : List Semantics.SVal := l.fold eraseFold
def SVec.erase {E : Ty} {n : Nat} (l : SVec E n) : List Semantics.SVal := l.fold eraseFold
def SMap.erase {U : Ty} (m : SMap U) : List (Int × Semantics.SVal) := m.fold eraseFold

theorem SVal.erase_prim {p : PrimTy} (v : p.Denote) : (SVal.prim v).erase = .prim (PrimTy.erase v) :=
  rfl
theorem SVal.erase_struct {s : Name} (fs : SFields (structDef s)) :
    (SVal.struct fs).erase = .struct fs.erase := rfl
theorem SVal.erase_array {E : Ty} (e sh : SList E) :
    (SVal.array e sh).erase = .array e.erase sh.erase false := rfl
theorem SVal.erase_fixed {E : Ty} {n : Nat} (e : SVec E n) :
    (SVal.fixed e).erase = .array e.erase [] true := rfl
theorem SVal.erase_map {K U : Ty} (m : SMap U) (d : SVal U) :
    (SVal.map (K := K) m d).erase = .map m.erase d.erase := rfl
theorem SFields.erase_nil : (SFields.nil).erase = [] := rfl
theorem SFields.erase_cons {f : Name} {T : Ty} {fs : List (Name × Ty)} (v : SVal T)
    (rest : SFields fs) : (SFields.cons (f := f) v rest).erase = (f, v.erase) :: rest.erase := rfl
theorem SList.erase_nil {E : Ty} : (SList.nil (E := E)).erase = [] := rfl
theorem SList.erase_cons {E : Ty} (v : SVal E) (rest : SList E) :
    (SList.cons v rest).erase = v.erase :: rest.erase := rfl
theorem SVec.erase_nil {E : Ty} : (SVec.nil (E := E)).erase = [] := rfl
theorem SVec.erase_cons {E : Ty} {n : Nat} (v : SVal E) (rest : SVec E n) :
    (SVec.cons v rest).erase = v.erase :: rest.erase := rfl
theorem SMap.erase_nil {U : Ty} : (SMap.nil (V := U)).erase = [] := rfl
theorem SMap.erase_cons {U : Ty} (k : Int) (v : SVal U) (rest : SMap U) :
    (SMap.cons k v rest).erase = (k, v.erase) :: rest.erase := rfl

attribute [irreducible] SVal.erase SFields.erase SList.erase SVec.erase SMap.erase
attribute [eqns SVal.erase_prim SVal.erase_struct SVal.erase_array SVal.erase_fixed
  SVal.erase_map] SVal.erase
attribute [eqns SFields.erase_nil SFields.erase_cons] SFields.erase
attribute [eqns SList.erase_nil SList.erase_cons] SList.erase
attribute [eqns SVec.erase_nil SVec.erase_cons] SVec.erase
attribute [eqns SMap.erase_nil SMap.erase_cons] SMap.erase

/-! ## Lists, vectors and maps as Lean lists -/

/-- The values of lists, vectors and mappings. -/
def toListFold : Fold where
  V _ := Unit
  F _ := Unit
  L E := List (SVal E)
  W E _ := List (SVal E)
  M U := List (Int × SVal U)
  prim := fun _ => ()
  struct := fun _ _ => ()
  array := fun _ _ _ _ => ()
  fixed := fun _ _ => ()
  map := fun _ _ _ _ => ()
  fnil := ()
  fcons := fun _ _ _ _ => ()
  lnil := []
  lcons := fun v _ _ ir => v :: ir
  wnil := []
  wcons := fun v _ _ ir => v :: ir
  mnil := []
  mcons := fun k v _ _ ir => (k, v) :: ir

namespace SList

/-- `toList` by `match`, its compiled form. -/
def toListM {E : Ty} : SList E → List (SVal E)
  | .nil => []
  | .cons v rest => v :: rest.toListM

@[implemented_by toListM]
def toList {E : Ty} (l : SList E) : List (SVal E) := l.fold toListFold

theorem toList_nil {E : Ty} : (SList.nil (E := E)).toList = [] := rfl
theorem toList_cons {E : Ty} (v : SVal E) (rest : SList E) :
    (SList.cons v rest).toList = v :: rest.toList := rfl

attribute [irreducible] toList
attribute [eqns toList_nil toList_cons] toList

def ofList {E : Ty} : List (SVal E) → SList E
  | [] => .nil
  | v :: rest => .cons v (ofList rest)

@[simp] theorem toList_ofList {E : Ty} : (l : List (SVal E)) → (ofList l).toList = l
  | [] => by rw [ofList, toList_nil]
  | v :: rest => by rw [ofList, toList_cons, toList_ofList rest]

@[simp] theorem ofList_toList {E : Ty} : (l : SList E) → ofList l.toList = l
  | .nil => by rw [toList_nil, ofList]
  | .cons v rest => by rw [toList_cons, ofList, ofList_toList rest]

theorem erase_eq {E : Ty} : (l : SList E) → l.erase = l.toList.map SVal.erase
  | .nil => by simp only [SList.erase, toList, List.map_nil]
  | .cons v rest => by simp only [SList.erase, toList, List.map_cons, erase_eq rest]

/-- The number of values. -/
def length {E : Ty} (l : SList E) : Nat := l.toList.length

end SList

namespace SVec

/-- `toList` by `match`, its compiled form. -/
def toListM {E : Ty} : {n : Nat} → SVec E n → List (SVal E)
  | _, .nil => []
  | _, .cons v rest => v :: rest.toListM

@[implemented_by toListM]
def toList {E : Ty} {n : Nat} (l : SVec E n) : List (SVal E) := l.fold toListFold

theorem toList_nil {E : Ty} : (SVec.nil (E := E)).toList = [] := rfl
theorem toList_cons {E : Ty} {n : Nat} (v : SVal E) (rest : SVec E n) :
    (SVec.cons v rest).toList = v :: rest.toList := rfl

attribute [irreducible] toList
attribute [eqns toList_nil toList_cons] toList

theorem length_toList {E : Ty} : {n : Nat} → (v : SVec E n) → v.toList.length = n
  | _, .nil => by rw [toList_nil, List.length_nil]
  | _, .cons _ rest => by rw [toList_cons, List.length_cons, length_toList rest]

theorem erase_eq {E : Ty} : {n : Nat} → (l : SVec E n) → l.erase = l.toList.map SVal.erase
  | _, .nil => by simp only [SVec.erase, toList, List.map_nil]
  | _, .cons v rest => by simp only [SVec.erase, toList, List.map_cons, erase_eq rest]

/-- `n` copies of a value. -/
def replicate {E : Ty} (v : SVal E) : (n : Nat) → SVec E n
  | 0 => .nil
  | n + 1 => .cons v (replicate v n)

theorem toList_replicate {E : Ty} (v : SVal E) :
    (n : Nat) → (replicate v n).toList = List.replicate n v
  | 0 => by rw [replicate, toList_nil, List.replicate_zero]
  | n + 1 => by rw [replicate, toList_cons, toList_replicate v n, List.replicate_succ]

/-- The value at `i` replaced, as `List.set`. -/
def setFold : Fold where
  V _ := Unit
  F _ := Unit
  L _ := Unit
  W E n := Nat → SVal E → SVec E n
  M _ := Unit
  prim := fun _ => ()
  struct := fun _ _ => ()
  array := fun _ _ _ _ => ()
  fixed := fun _ _ => ()
  map := fun _ _ _ _ => ()
  fnil := ()
  fcons := fun _ _ _ _ => ()
  lnil := ()
  lcons := fun _ _ _ _ => ()
  wnil := fun _ _ => .nil
  wcons := fun v rest _ ih i x =>
    match i with
    | 0 => .cons x rest
    | i + 1 => .cons v (ih i x)
  mnil := ()
  mcons := fun _ _ _ _ _ => ()

/-- `set` by `match`, its compiled form. -/
def setM {E : Ty} : {n : Nat} → SVec E n → Nat → SVal E → SVec E n
  | _, .nil, _, _ => .nil
  | _, .cons _ rest, 0, x => .cons x rest
  | _, .cons v rest, i + 1, x => .cons v (rest.setM i x)

/-- The vector with the value at `i` replaced, as `List.set`. -/
@[implemented_by setM]
def set {E : Ty} {n : Nat} (l : SVec E n) (i : Nat) (x : SVal E) : SVec E n := l.fold setFold i x

theorem set_nil {E : Ty} (i : Nat) (x : SVal E) : (SVec.nil (E := E)).set i x = .nil := rfl
theorem set_cons_zero {E : Ty} {n : Nat} (v : SVal E) (rest : SVec E n) (x : SVal E) :
    (SVec.cons v rest).set 0 x = .cons x rest := rfl
theorem set_cons_succ {E : Ty} {n : Nat} (v : SVal E) (rest : SVec E n) (i : Nat) (x : SVal E) :
    (SVec.cons v rest).set (i + 1) x = .cons v (rest.set i x) := rfl

attribute [irreducible] set
attribute [eqns set_nil set_cons_zero set_cons_succ] set

theorem toList_set {E : Ty} : {n : Nat} → (l : SVec E n) → (i : Nat) → (x : SVal E) →
    (l.set i x).toList = l.toList.set i x
  | _, .nil, _, _ => by rw [set_nil, toList_nil, List.set_nil]
  | _, .cons _ _, 0, _ => by rw [set_cons_zero, toList_cons, toList_cons, List.set_cons_zero]
  | _, .cons v rest, i + 1, x => by
    rw [set_cons_succ, toList_cons, toList_cons, List.set_cons_succ, toList_set rest i x]

end SVec

namespace SMap

/-- `toList` by `match`, its compiled form. -/
def toListM {V : Ty} : SMap V → List (Int × SVal V)
  | .nil => []
  | .cons k v rest => (k, v) :: rest.toListM

@[implemented_by toListM]
def toList {V : Ty} (m : SMap V) : List (Int × SVal V) := m.fold toListFold

theorem toList_nil {V : Ty} : (SMap.nil (V := V)).toList = [] := rfl
theorem toList_cons {V : Ty} (k : Int) (v : SVal V) (rest : SMap V) :
    (SMap.cons k v rest).toList = (k, v) :: rest.toList := rfl

attribute [irreducible] toList
attribute [eqns toList_nil toList_cons] toList

def ofList {V : Ty} : List (Int × SVal V) → SMap V
  | [] => .nil
  | (k, v) :: rest => .cons k v (ofList rest)

@[simp] theorem toList_ofList {V : Ty} : (l : List (Int × SVal V)) → (ofList l).toList = l
  | [] => by rw [ofList, toList_nil]
  | (k, v) :: rest => by rw [ofList, toList_cons, toList_ofList rest]

theorem erase_eq {V : Ty} : (m : SMap V) → m.erase = m.toList.map (fun e => (e.1, e.2.erase))
  | .nil => by simp only [SMap.erase, toList, List.map_nil]
  | .cons k v rest => by simp only [SMap.erase, toList, List.map_cons, erase_eq rest]

end SMap

/-! ## Members by name

A member is named as the syntax names it (`Loc.field b f h`, with
`h : C.fieldType s f = some T`): the first member of that name, as
`lookupBy` finds it. -/

namespace SFields

theorem lookupBy_cons_pos {f f' : Name} {T T' : Ty} {fs : List (Name × Ty)} (e : f = f')
    (h : lookupBy f ((f', T') :: fs) = some T) : T' = T := by
  simp only [lookupBy, if_pos e] at h
  exact Option.some.inj h

theorem lookupBy_cons_neg {f f' : Name} {T T' : Ty} {fs : List (Name × Ty)} (e : ¬f = f')
    (h : lookupBy f ((f', T') :: fs) = some T) : lookupBy f fs = some T := by
  simp only [lookupBy, if_neg e] at h
  exact h

/-- `get` by `match`, its compiled form. -/
def getM {f : Name} : {fs : List (Name × Ty)} → {T : Ty} → SFields fs →
    lookupBy f fs = some T → SVal T
  | _, _, .nil, h => absurd h (by simp only [lookupBy, reduceCtorEq, not_false_eq_true])
  | _, _, @SFields.cons f' _ _ v rest, h =>
    if e : f = f' then lookupBy_cons_pos e h ▸ v
    else rest.getM (lookupBy_cons_neg e h)

/-- `set` by `match`, its compiled form. -/
def setM {f : Name} : {fs : List (Name × Ty)} → {T : Ty} → SFields fs →
    lookupBy f fs = some T → SVal T → SFields fs
  | _, _, .nil, _, _ => .nil
  | _, _, @SFields.cons f' _ _ v rest, h, x =>
    if e : f = f' then .cons ((lookupBy_cons_pos e h).symm ▸ x) rest
    else .cons v (rest.setM (lookupBy_cons_neg e h) x)

/-- The value of the first member named `f`.  By the recursor, for the kernel
(Gate G0, condition 2); `getM` is its compiled form. -/
@[implemented_by getM]
def get {f : Name} {fs : List (Name × Ty)} {T : Ty} (x : SFields fs)
    (h : lookupBy f fs = some T) : SVal T :=
  @SFields.rec (fun _ _ => Unit) (fun fs _ => ∀ T, lookupBy f fs = some T → SVal T)
    (fun _ _ => Unit) (fun _ _ _ => Unit) (fun _ _ => Unit)
    (fun {_} _ => ()) (fun {_} _ _ => ()) (fun {_} _ _ _ _ => ()) (fun {_} {_} _ _ => ())
    (fun {_} {_} _ _ _ _ => ())
    (fun _ h => absurd h (by simp only [lookupBy, reduceCtorEq, not_false_eq_true]))
    (fun {f'} {_} {_} v _ _ ih _ h =>
      if e : f = f' then lookupBy_cons_pos e h ▸ v else ih _ (lookupBy_cons_neg e h))
    (fun {_} => ()) (fun {_} _ _ _ _ => ()) (fun {_} => ()) (fun {_} {_} _ _ _ _ => ())
    (fun {_} => ()) (fun {_} _ _ _ _ _ => ()) fs x T h

/-- The first member named `f` replaced.  By the recursor; `setM` is its
compiled form. -/
@[implemented_by setM]
def set {f : Name} {fs : List (Name × Ty)} {T : Ty} (x : SFields fs)
    (h : lookupBy f fs = some T) (y : SVal T) : SFields fs :=
  @SFields.rec (fun _ _ => Unit) (fun fs _ => ∀ T, lookupBy f fs = some T → SVal T → SFields fs)
    (fun _ _ => Unit) (fun _ _ _ => Unit) (fun _ _ => Unit)
    (fun {_} _ => ()) (fun {_} _ _ => ()) (fun {_} _ _ _ _ => ()) (fun {_} {_} _ _ => ())
    (fun {_} {_} _ _ _ _ => ())
    (fun _ _ _ => .nil)
    (fun {f'} {_} {_} v rest _ ih _ h y =>
      if e : f = f' then .cons ((lookupBy_cons_pos e h).symm ▸ y) rest
      else .cons v (ih _ (lookupBy_cons_neg e h) y))
    (fun {_} => ()) (fun {_} _ _ _ _ => ()) (fun {_} => ()) (fun {_} {_} _ _ _ _ => ())
    (fun {_} => ()) (fun {_} _ _ _ _ _ => ()) fs x T h y

theorem get_cons {f f' : Name} {T T' : Ty} {fs : List (Name × Ty)} (v : SVal T')
    (rest : SFields fs) (h : lookupBy f ((f', T') :: fs) = some T) :
    (SFields.cons v rest).get h =
      if e : f = f' then lookupBy_cons_pos e h ▸ v else rest.get (lookupBy_cons_neg e h) := rfl

theorem set_nil {f : Name} {T : Ty} (h : lookupBy f [] = some T) (y : SVal T) :
    SFields.nil.set h y = .nil := rfl

theorem set_cons {f f' : Name} {T T' : Ty} {fs : List (Name × Ty)} (v : SVal T')
    (rest : SFields fs) (h : lookupBy f ((f', T') :: fs) = some T) (y : SVal T) :
    (SFields.cons v rest).set h y =
      if e : f = f' then .cons ((lookupBy_cons_pos e h).symm ▸ y) rest
      else .cons v (rest.set (lookupBy_cons_neg e h) y) := rfl

end SFields

/-! ## Defaults

`SVal.dflt T` is `defaultForTy T`: by recursion on a bound `k` of the rank,
and inside one rank structurally on the type; a struct's members are of a
smaller rank (`structDef_rank_lt`). -/

/-- A struct's members' defaults, given the defaults below rank `k`. -/
def SFields.dfltBelow (k : Nat) (ih : (T : Ty) → tyRank T < k → SVal T) :
    (fs : List (Name × Ty)) → fieldsRank fs < k → SFields fs
  | [], _ => .nil
  | (_, T) :: fs, h =>
    .cons (ih T (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) h))
      (SFields.dfltBelow k ih fs (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) h))

mutual
/-- The defaults of rank at most `k`, given those below. -/
def SVal.dfltAt (k : Nat) (ih : (T : Ty) → tyRank T < k → SVal T) :
    (T : Ty) → tyRank T < k + 1 → SVal T
  | .prim p, _ => .prim (PrimTy.dflt p)
  | .ref R, h => SVal.dfltRefAt k ih R h

def SVal.dfltRefAt (k : Nat) (ih : (T : Ty) → tyRank T < k → SVal T) :
    (R : RefTy) → tyRank (.ref R) < k + 1 → SVal (.ref R)
  | .struct s, h =>
    .struct (SFields.dfltBelow k ih (structDef s)
      (Nat.lt_of_lt_of_le (Semantics.structDef_rank_lt s) (Nat.le_of_lt_succ h)))
  | .array _, _ => .array .nil .nil
  | .fixed E n, h =>
    .fixed (SVec.replicate
      (SVal.dfltAt k ih E (Nat.lt_of_succ_lt (by simpa only [tyRank] using h))) n)
  | .mapping _ V, h => .map .nil (SVal.dfltAt k ih V (by simpa only [tyRank] using h))
end

/-- The defaults below rank `k`. -/
def SVal.dfltBelow : (k : Nat) → (T : Ty) → tyRank T < k → SVal T
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, T, h => SVal.dfltAt k (SVal.dfltBelow k) T h

/-- A bound on `tyRank` that reads no struct's name (every `structRank` is at
most 4), so the kernel computes the fuel of `SVal.dflt` without matching a
string: `tyRank` itself costs a `structRank` lookup per default. -/
def rankBound : Ty → Nat
  | .prim _ => 0
  | .ref (.struct _) => 4
  | .ref (.array E) => rankBound E
  | .ref (.fixed E _) => rankBound E + 1
  | .ref (.mapping _ V) => rankBound V

theorem structRank_le_four (s : Name) : structRank s ≤ 4 := by
  unfold structRank
  split <;> decide

theorem tyRank_le_rankBound : (T : Ty) → tyRank T ≤ rankBound T
  | .prim _ => Nat.le_refl _
  | .ref (.struct s) => structRank_le_four s
  | .ref (.array E) => tyRank_le_rankBound E
  | .ref (.fixed E _) => Nat.succ_le_succ (tyRank_le_rankBound E)
  | .ref (.mapping _ V) => tyRank_le_rankBound V

/-- The default of `T` (`defaultForTy`). -/
def SVal.dflt (T : Ty) : SVal T :=
  SVal.dfltBelow (rankBound T + 1) T (Nat.lt_succ_of_le (tyRank_le_rankBound T))

/-- Every member at its default. -/
def SFields.dflt : (fs : List (Name × Ty)) → SFields fs
  | [] => .nil
  | (_, T) :: fs => .cons (SVal.dflt T) (SFields.dflt fs)

/-! ## Paths -/

/-- A typed storage path: from a `T` to a `U`, a member by name, an array
slot (live or past the end), a fixed-size array's slot, or a mapping's key.
The index is the program's, unchecked: a read or a write past the slots
reverts (`SVal.find`). -/
inductive Path : Ty → Ty → Type where
  | nil {T : Ty} : Path T T
  | field {s f : Name} {T U : Ty} (h : lookupBy f (structDef s) = some T) (p : Path T U) :
      Path (.ref (.struct s)) U
  | at {E U : Ty} (i : Int) (p : Path E U) : Path (.ref (.array E)) U
  | atF {E U : Ty} {n : Nat} (i : Int) (p : Path E U) : Path (.ref (.fixed E n)) U
  | key {K V U : Ty} (k : Int) (p : Path V U) : Path (.ref (.mapping K V)) U

namespace Path

/-- The untyped segments. -/
def erase : {T U : Ty} → Path T U → List Semantics.Seg
  | _, _, .nil => []
  | _, _, @Path.field _ f _ _ _ p => .field f :: p.erase
  | _, _, .at i p => .at i :: p.erase
  | _, _, .atF i p => .at i :: p.erase
  | _, _, .key k p => .at k :: p.erase

/-- A path followed by another. -/
def append : {T U W : Ty} → Path T U → Path U W → Path T W
  | _, _, _, .nil, q => q
  | _, _, _, .field h p, q => .field h (p.append q)
  | _, _, _, .at i p, q => .at i (p.append q)
  | _, _, _, .atF i p, q => .atF i (p.append q)
  | _, _, _, .key k p, q => .key k (p.append q)

theorem erase_append : {T U W : Ty} → (p : Path T U) → (q : Path U W) →
    (p.append q).erase = p.erase ++ q.erase
  | _, _, _, .nil, _ => rfl
  | _, _, _, .field _ p, q => congrArg (_ :: ·) (erase_append p q)
  | _, _, _, .at _ p, q => congrArg (_ :: ·) (erase_append p q)
  | _, _, _, .atF _ p, q => congrArg (_ :: ·) (erase_append p q)
  | _, _, _, .key _ p, q => congrArg (_ :: ·) (erase_append p q)

/-- The one step `b[i]` takes, by how `R` is indexed. -/
def index : {R : RefTy} → {k : PrimTy} → {V : Ty} → IndexTy R k V → Int → Path (.ref R) V
  | _, _, _, .map, i => .key i .nil
  | _, _, _, .arr .dyn, i => .at i .nil
  | _, _, _, .arr .fixed, i => .atF i .nil

theorem erase_index : {R : RefTy} → {k : PrimTy} → {V : Ty} → (it : IndexTy R k V) → (i : Int) →
    (index it i).erase = [.at i]
  | _, _, _, .map, _ | _, _, _, .arr .dyn, _ | _, _, _, .arr .fixed, _ => rfl

end Path

/-! ## Find and save

The kernel evaluates these (`decide +kernel`, the symbolic execution's
`Eq.refl`), so they are written with the recursor of `Path` and read a value
through `SVal.view`, whose type `Shape T` is computed from `T`: no `match` on
an indexed family, whose casts cost the kernel a factor of 40 here
(`docs/intrinsic.md`, "M4 lane", and Gate G0, condition 2).  The compiler
cannot compile a recursor, so each has a `match` twin (`SVal.findM`, …) as
its `implemented_by`, and a theorem that they are equal
(`Semantics/Core/StorageErase.lean`). -/

/-- `SVal.find` by `match`, its compiled form. -/
def SVal.findM : {T U : Ty} → SVal T → Path T U → Option (SVal U)
  | _, _, v, .nil => some v
  | _, _, .struct fs, .field h p => (fs.get h).findM p
  | _, _, .array e sh, .at i p =>
    if 0 ≤ i then
      match (e.toList ++ sh.toList)[i.toNat]? with
      | some x => x.findM p
      | none => none
    else none
  | _, _, .fixed e, .atF i p =>
    if 0 ≤ i then
      match e.toList[i.toNat]? with
      | some x => x.findM p
      | none => none
    else none
  | _, _, .map m d, .key k p =>
    match lookupBy k m.toList with
    | some x => x.findM p
    | none => d.findM p

/-- `SVal.findLive` by `match`, its compiled form. -/
def SVal.findLiveM : {T U : Ty} → SVal T → Path T U → Option (SVal U)
  | _, _, v, .nil => some v
  | _, _, .struct fs, .field h p => (fs.get h).findLiveM p
  | _, _, .array e _, .at i p =>
    if 0 ≤ i then
      match e.toList[i.toNat]? with
      | some x => x.findLiveM p
      | none => none
    else none
  | _, _, .fixed e, .atF i p =>
    if 0 ≤ i then
      match e.toList[i.toNat]? with
      | some x => x.findLiveM p
      | none => none
    else none
  | _, _, .map m d, .key k p =>
    match lookupBy k m.toList with
    | some x => x.findLiveM p
    | none => d.findLiveM p

/-- `SVal.save` by `match`, its compiled form. -/
def SVal.saveM : {T U : Ty} → SVal T → Path T U → SVal U → Option (SVal T)
  | _, _, _, .nil, new => some new
  | _, _, .struct fs, .field h p, new => do
    let x ← (fs.get h).saveM p new
    some (.struct (fs.set h x))
  | _, _, .array e sh, .at i p, new =>
    if 0 ≤ i then
      match (e.toList ++ sh.toList)[i.toNat]? with
      | some x => do
        let x' ← x.saveM p new
        let slots := (e.toList ++ sh.toList).set i.toNat x'
        some (.array (.ofList (slots.take e.length)) (.ofList (slots.drop e.length)))
      | none => none
    else none
  | _, _, .fixed e, .atF i p, new =>
    if 0 ≤ i then
      match e.toList[i.toNat]? with
      | some x => do
        let x' ← x.saveM p new
        some (.fixed (e.set i.toNat x'))
      | none => none
    else none
  | _, _, .map m d, .key k p, new =>
    match lookupBy k m.toList with
    | some x => do
      let x' ← x.saveM p new
      some (.map (.ofList (setBy k x' m.toList)) d)
    | none => do
      let x' ← d.saveM p new
      some (.map (.ofList (setBy k x' m.toList)) d)

/-- The value at a path (`Semantics.SVal.find`): `none` where an index is past
the slots. -/
@[implemented_by SVal.findM]
def SVal.find {T U : Ty} (v : SVal T) (p : Path T U) : Option (SVal U) :=
  @Path.rec (fun T U _ => SVal T → Option (SVal U))
    (fun {_} v => some v)
    (fun {_} {_} {_} {_} h _ ih v => ih (SFields.get (SVal.view v) h))
    (fun {_} {_} i _ ih v =>
      let w : SList _ × SList _ := SVal.view v
      if 0 ≤ i then
        match (w.1.toList ++ w.2.toList)[i.toNat]? with
        | some x => ih x
        | none => none
      else none)
    (fun {_} {_} {_} i _ ih v =>
      if 0 ≤ i then
        match (SVal.view v : SVec _ _).toList[i.toNat]? with
        | some x => ih x
        | none => none
      else none)
    (fun {_} {_} {_} k _ ih v =>
      let w : SMap _ × SVal _ := SVal.view v
      match lookupBy k w.1.toList with
      | some x => ih x
      | none => ih w.2)
    T U p v

/-- A read that checks every index against the live length
(`Semantics.SVal.findLive`): `find` past an array's end is `none`. -/
@[implemented_by SVal.findLiveM]
def SVal.findLive {T U : Ty} (v : SVal T) (p : Path T U) : Option (SVal U) :=
  @Path.rec (fun T U _ => SVal T → Option (SVal U))
    (fun {_} v => some v)
    (fun {_} {_} {_} {_} h _ ih v => ih (SFields.get (SVal.view v) h))
    (fun {_} {_} i _ ih v =>
      let w : SList _ × SList _ := SVal.view v
      if 0 ≤ i then
        match w.1.toList[i.toNat]? with
        | some x => ih x
        | none => none
      else none)
    (fun {_} {_} {_} i _ ih v =>
      if 0 ≤ i then
        match (SVal.view v : SVec _ _).toList[i.toNat]? with
        | some x => ih x
        | none => none
      else none)
    (fun {_} {_} {_} k _ ih v =>
      let w : SMap _ × SVal _ := SVal.view v
      match lookupBy k w.1.toList with
      | some x => ih x
      | none => ih w.2)
    T U p v

/-- The value with the one at a path replaced (`Semantics.SVal.save`). -/
@[implemented_by SVal.saveM]
def SVal.save {T U : Ty} (v : SVal T) (p : Path T U) (new : SVal U) : Option (SVal T) :=
  @Path.rec (fun T U _ => SVal T → SVal U → Option (SVal T))
    (fun {_} _ new => some new)
    (fun {_} {_} {_} {_} h _ ih v new =>
      let fs : SFields _ := SVal.view v
      do
        let x ← ih (fs.get h) new
        some (.struct (fs.set h x)))
    (fun {_} {_} i _ ih v new =>
      let w : SList _ × SList _ := SVal.view v
      if 0 ≤ i then
        match (w.1.toList ++ w.2.toList)[i.toNat]? with
        | some x => do
          let x' ← ih x new
          let slots := (w.1.toList ++ w.2.toList).set i.toNat x'
          some (.array (.ofList (slots.take w.1.length)) (.ofList (slots.drop w.1.length)))
        | none => none
      else none)
    (fun {_} {_} {_} i _ ih v new =>
      let e : SVec _ _ := SVal.view v
      if 0 ≤ i then
        match e.toList[i.toNat]? with
        | some x => do
          let x' ← ih x new
          some (.fixed (e.set i.toNat x'))
        | none => none
      else none)
    (fun {_} {_} {_} k _ ih v new =>
      let w : SMap _ × SVal _ := SVal.view v
      match lookupBy k w.1.toList with
      | some x => do
        let x' ← ih x new
        some (.map (.ofList (setBy k x' w.1.toList)) w.2)
      | none => do
        let x' ← ih w.2 new
        some (.map (.ofList (setBy k x' w.1.toList)) w.2))
    T U p v new

/-! ## Delete, copy over -/

/-- `delete`'s value. -/
def defaultOfFold : Fold where
  V T := SVal T
  F fs := SFields fs
  L E := SList E
  W E n := SVec E n
  M U := SMap U
  prim := fun {p} _ => .prim (PrimTy.dflt p)
  struct := fun _ ih => .struct ih
  array := fun _ sh ie _ => .array .nil (.ofList (SList.toList ie ++ sh.toList))
  fixed := fun _ ie => .fixed ie
  map := fun m d _ _ => .map m d
  fnil := .nil
  fcons := fun _ _ iv ir => .cons iv ir
  lnil := .nil
  lcons := fun _ _ iv ir => .cons iv ir
  wnil := .nil
  wcons := fun _ _ iv ir => .cons iv ir
  mnil := .nil
  mcons := fun k v rest _ _ => .cons k v rest

/-- `delete`'s value (`Semantics.SVal.defaultOf`): primitives reset, members
and elements recursively, a dynamic array emptied into the slots past its
end, a mapping left as it is. -/
def SVal.defaultOf {T : Ty} (v : SVal T) : SVal T := v.fold defaultOfFold
def SFields.defaultOf {fs : List (Name × Ty)} (x : SFields fs) : SFields fs := x.fold defaultOfFold
def SList.defaultOf {E : Ty} (l : SList E) : SList E := l.fold defaultOfFold
def SVec.defaultOf {E : Ty} {n : Nat} (l : SVec E n) : SVec E n := l.fold defaultOfFold

theorem SVal.defaultOf_prim {p : PrimTy} (v : p.Denote) :
    (SVal.prim v).defaultOf = .prim (PrimTy.dflt p) := rfl
theorem SVal.defaultOf_struct {s : Name} (fs : SFields (structDef s)) :
    (SVal.struct fs).defaultOf = .struct fs.defaultOf := rfl
theorem SVal.defaultOf_array {E : Ty} (e sh : SList E) :
    (SVal.array e sh).defaultOf = .array .nil (.ofList (e.defaultOf.toList ++ sh.toList)) := rfl
theorem SVal.defaultOf_fixed {E : Ty} {n : Nat} (e : SVec E n) :
    (SVal.fixed e).defaultOf = .fixed e.defaultOf := rfl
theorem SVal.defaultOf_map {K U : Ty} (m : SMap U) (d : SVal U) :
    (SVal.map (K := K) m d).defaultOf = .map m d := rfl
theorem SFields.defaultOf_nil : (SFields.nil).defaultOf = .nil := rfl
theorem SFields.defaultOf_cons {f : Name} {T : Ty} {fs : List (Name × Ty)} (v : SVal T)
    (rest : SFields fs) :
    (SFields.cons (f := f) v rest).defaultOf = .cons v.defaultOf rest.defaultOf := rfl
theorem SList.defaultOf_nil {E : Ty} : (SList.nil (E := E)).defaultOf = .nil := rfl
theorem SList.defaultOf_cons {E : Ty} (v : SVal E) (rest : SList E) :
    (SList.cons v rest).defaultOf = .cons v.defaultOf rest.defaultOf := rfl
theorem SVec.defaultOf_nil {E : Ty} : (SVec.nil (E := E)).defaultOf = .nil := rfl
theorem SVec.defaultOf_cons {E : Ty} {n : Nat} (v : SVal E) (rest : SVec E n) :
    (SVec.cons v rest).defaultOf = .cons v.defaultOf rest.defaultOf := rfl

attribute [irreducible] SVal.defaultOf SFields.defaultOf SList.defaultOf SVec.defaultOf
attribute [eqns SVal.defaultOf_prim SVal.defaultOf_struct SVal.defaultOf_array
  SVal.defaultOf_fixed SVal.defaultOf_map] SVal.defaultOf
attribute [eqns SFields.defaultOf_nil SFields.defaultOf_cons] SFields.defaultOf
attribute [eqns SList.defaultOf_nil SList.defaultOf_cons] SList.defaultOf
attribute [eqns SVec.defaultOf_nil SVec.defaultOf_cons] SVec.defaultOf

/-- A value as nothing has written it. -/
def stripFold : Fold where
  V T := SVal T
  F fs := SFields fs
  L E := SList E
  W E n := SVec E n
  M U := SMap U
  prim := fun v => .prim v
  struct := fun _ ih => .struct ih
  array := fun _ _ ie _ => .array ie .nil
  fixed := fun _ ie => .fixed ie
  map := fun m d _ _ => .map m d
  fnil := .nil
  fcons := fun _ _ iv ir => .cons iv ir
  lnil := .nil
  lcons := fun _ _ iv ir => .cons iv ir
  wnil := .nil
  wcons := fun _ _ iv ir => .cons iv ir
  mnil := .nil
  mcons := fun k v rest _ _ => .cons k v rest

/-- A value as written to slots nothing has written (`Semantics.SVal.strip`):
no slots past an array's end. -/
def SVal.strip {T : Ty} (v : SVal T) : SVal T := v.fold stripFold
def SFields.strip {fs : List (Name × Ty)} (x : SFields fs) : SFields fs := x.fold stripFold
def SList.strip {E : Ty} (l : SList E) : SList E := l.fold stripFold
def SVec.strip {E : Ty} {n : Nat} (l : SVec E n) : SVec E n := l.fold stripFold

theorem SVal.strip_prim {p : PrimTy} (v : p.Denote) : (SVal.prim v).strip = .prim v := rfl
theorem SVal.strip_struct {s : Name} (fs : SFields (structDef s)) :
    (SVal.struct fs).strip = .struct fs.strip := rfl
theorem SVal.strip_array {E : Ty} (e sh : SList E) :
    (SVal.array e sh).strip = .array e.strip .nil := rfl
theorem SVal.strip_fixed {E : Ty} {n : Nat} (e : SVec E n) :
    (SVal.fixed e).strip = .fixed e.strip := rfl
theorem SVal.strip_map {K U : Ty} (m : SMap U) (d : SVal U) :
    (SVal.map (K := K) m d).strip = .map m d := rfl
theorem SFields.strip_nil : (SFields.nil).strip = .nil := rfl
theorem SFields.strip_cons {f : Name} {T : Ty} {fs : List (Name × Ty)} (v : SVal T)
    (rest : SFields fs) : (SFields.cons (f := f) v rest).strip = .cons v.strip rest.strip := rfl
theorem SList.strip_nil {E : Ty} : (SList.nil (E := E)).strip = .nil := rfl
theorem SList.strip_cons {E : Ty} (v : SVal E) (rest : SList E) :
    (SList.cons v rest).strip = .cons v.strip rest.strip := rfl
theorem SVec.strip_nil {E : Ty} : (SVec.nil (E := E)).strip = .nil := rfl
theorem SVec.strip_cons {E : Ty} {n : Nat} (v : SVal E) (rest : SVec E n) :
    (SVec.cons v rest).strip = .cons v.strip rest.strip := rfl

attribute [irreducible] SVal.strip SFields.strip SList.strip SVec.strip
attribute [eqns SVal.strip_prim SVal.strip_struct SVal.strip_array SVal.strip_fixed
  SVal.strip_map] SVal.strip
attribute [eqns SFields.strip_nil SFields.strip_cons] SFields.strip
attribute [eqns SList.strip_nil SList.strip_cons] SList.strip
attribute [eqns SVec.strip_nil SVec.strip_cons] SVec.strip

/-- A copy written over an old value: by recursion on the new one, the old
one read through the views. -/
def overlayFold : Fold where
  V T := SVal T → SVal T
  F fs := SFields fs → SFields fs
  L E := List (SVal E) → SList E
  W E n := SVec E n → SVec E n
  M _ := Unit
  prim := fun v _ => .prim v
  struct := fun _ ih o => .struct (ih (SVal.view o))
  array := fun nel _ ie _ o =>
    let w : SList _ × SList _ := SVal.view o
    .array (ie (w.1.toList ++ w.2.toList))
      (.ofList ((w.1.toList.drop nel.length).map SVal.defaultOf ++
        w.2.toList.drop (nel.length - w.1.length)))
  fixed := fun _ ie o => .fixed (ie (SVal.view o))
  map := fun _ _ _ _ o => o
  fnil := fun _ => .nil
  fcons := fun _ _ iv ir os =>
    let w := SFields.view os
    .cons (iv w.1) (ir w.2)
  lnil := fun _ => .nil
  lcons := fun v rest iv ir os =>
    match os with
    | [] => .cons v.strip rest.strip
    | o :: os => .cons (iv o) (ir os)
  wnil := fun _ => .nil
  wcons := fun _ _ iv ir os =>
    let w := SVec.view os
    .cons (iv w.1) (ir w.2)
  mnil := ()
  mcons := fun _ _ _ _ _ => ()

/-- A copy of `new` written over `old` (`Semantics.SVal.overlay`): member by
member in their order, as solc copies, element by element over the slots
it lands on, the old elements past the new length cleared, a mapping kept. -/
def SVal.overlay {T : Ty} (old new : SVal T) : SVal T := new.fold overlayFold old
def SFields.overlay {fs : List (Name × Ty)} (old new : SFields fs) : SFields fs :=
  new.fold overlayFold old
/-- The new elements over the old slots, as far as there are old slots. -/
def SList.overlayOn {E : Ty} (old : List (SVal E)) (new : SList E) : SList E :=
  new.fold overlayFold old
def SVec.overlay {E : Ty} {n : Nat} (old new : SVec E n) : SVec E n := new.fold overlayFold old

theorem SVal.overlay_prim {p : PrimTy} (o : SVal (.prim p)) (v : p.Denote) :
    o.overlay (.prim v) = .prim v := rfl
theorem SVal.overlay_struct {s : Name} (ofs nfs : SFields (structDef s)) :
    (SVal.struct ofs).overlay (.struct nfs) = .struct (ofs.overlay nfs) := rfl
theorem SVal.overlay_array {E : Ty} (oel osh nel nsh : SList E) :
    (SVal.array oel osh).overlay (.array nel nsh) =
      .array (SList.overlayOn (oel.toList ++ osh.toList) nel)
        (.ofList ((oel.toList.drop nel.length).map SVal.defaultOf ++
          osh.toList.drop (nel.length - oel.length))) := rfl
theorem SVal.overlay_fixed {E : Ty} {n : Nat} (oel nel : SVec E n) :
    (SVal.fixed oel).overlay (.fixed nel) = .fixed (oel.overlay nel) := rfl
theorem SVal.overlay_map {K U : Ty} (oe ne : SMap U) (od nd : SVal U) :
    (SVal.map (K := K) oe od).overlay (.map ne nd) = .map oe od := rfl
theorem SFields.overlay_nil : SFields.overlay .nil .nil = .nil := rfl
theorem SFields.overlay_cons {f : Name} {T : Ty} {fs : List (Name × Ty)} (o v : SVal T)
    (os rest : SFields fs) :
    SFields.overlay (.cons (f := f) o os) (.cons v rest) = .cons (o.overlay v) (os.overlay rest) :=
  rfl
theorem SList.overlayOn_nil {E : Ty} (os : List (SVal E)) : SList.overlayOn os .nil = .nil := rfl
theorem SList.overlayOn_nil_cons {E : Ty} (v : SVal E) (rest : SList E) :
    SList.overlayOn [] (.cons v rest) = .cons v.strip rest.strip := rfl
theorem SList.overlayOn_cons_cons {E : Ty} (o : SVal E) (os : List (SVal E)) (v : SVal E)
    (rest : SList E) :
    SList.overlayOn (o :: os) (.cons v rest) = .cons (o.overlay v) (SList.overlayOn os rest) := rfl
theorem SVec.overlay_nil {E : Ty} : SVec.overlay (E := E) .nil .nil = .nil := rfl
theorem SVec.overlay_cons {E : Ty} {n : Nat} (o v : SVal E) (os rest : SVec E n) :
    SVec.overlay (.cons o os) (.cons v rest) = .cons (o.overlay v) (os.overlay rest) := rfl

attribute [irreducible] SVal.overlay SFields.overlay SList.overlayOn SVec.overlay
attribute [eqns SVal.overlay_prim SVal.overlay_struct SVal.overlay_array SVal.overlay_fixed
  SVal.overlay_map] SVal.overlay
attribute [eqns SFields.overlay_nil SFields.overlay_cons] SFields.overlay
attribute [eqns SList.overlayOn_nil SList.overlayOn_nil_cons SList.overlayOn_cons_cons]
  SList.overlayOn
attribute [eqns SVec.overlay_nil SVec.overlay_cons] SVec.overlay

/-- `SList.overlayOn` over no old slots: the new elements as nothing wrote
them. -/
theorem SList.overlayOn_nil_left {E : Ty} : (l : SList E) → SList.overlayOn [] l = l.strip
  | .nil => by rw [overlayOn_nil, strip_nil]
  | .cons v rest => by rw [overlayOn_nil_cons, strip_cons]

/-- A primitive value: a write stores it, where a reference is copied over.
Read off the type. -/
def SVal.isPrim {T : Ty} (_ : SVal T) : Bool := T.isPrimitive

/-! ## Equality

Decided by a fold (`SVal.beq`), the second value read through the views, so
`decide +kernel` reduces it where the derived `match` would cast at every
step. -/

/-- Equality of two values of one type. -/
def beqFold : Fold where
  V T := SVal T → Bool
  F fs := SFields fs → Bool
  L E := SList E → Bool
  W E n := SVec E n → Bool
  M U := SMap U → Bool
  prim := fun {p} x w => decide (x = (SVal.view w : p.Denote))
  struct := fun _ ih w => ih (SVal.view w)
  array := fun _ _ ie ish w =>
    let x : SList _ × SList _ := SVal.view w
    ie x.1 && ish x.2
  fixed := fun _ ie w => ie (SVal.view w)
  map := fun _ _ im id w =>
    let x : SMap _ × SVal _ := SVal.view w
    im x.1 && id x.2
  fnil := fun _ => true
  fcons := fun _ _ iv ir w =>
    let x := SFields.view w
    iv x.1 && ir x.2
  lnil := fun w => (SList.uncons w).isNone
  lcons := fun _ _ iv ir w =>
    match SList.uncons w with
    | some x => iv x.1 && ir x.2
    | none => false
  wnil := fun _ => true
  wcons := fun _ _ iv ir w =>
    let x := SVec.view w
    iv x.1 && ir x.2
  mnil := fun w => (SMap.uncons w).isNone
  mcons := fun k _ _ iv ir w =>
    match SMap.uncons w with
    | some x => decide (k = x.1) && iv x.2.1 && ir x.2.2
    | none => false

def SVal.beq {T : Ty} (v w : SVal T) : Bool := v.fold beqFold w
def SFields.beq {fs : List (Name × Ty)} (x y : SFields fs) : Bool := x.fold beqFold y
def SList.beq {E : Ty} (l l' : SList E) : Bool := l.fold beqFold l'
def SVec.beq {E : Ty} {n : Nat} (l l' : SVec E n) : Bool := l.fold beqFold l'
def SMap.beq {U : Ty} (m m' : SMap U) : Bool := m.fold beqFold m'

theorem SVal.beq_prim {p : PrimTy} (x y : p.Denote) :
    (SVal.prim x).beq (.prim y) = decide (x = y) := rfl
theorem SVal.beq_struct {s : Name} (fs gs : SFields (structDef s)) :
    (SVal.struct fs).beq (.struct gs) = fs.beq gs := rfl
theorem SVal.beq_array {E : Ty} (e sh e' sh' : SList E) :
    (SVal.array e sh).beq (.array e' sh') = (e.beq e' && sh.beq sh') := rfl
theorem SVal.beq_fixed {E : Ty} {n : Nat} (e e' : SVec E n) :
    (SVal.fixed e).beq (.fixed e') = e.beq e' := rfl
theorem SVal.beq_map {K U : Ty} (m m' : SMap U) (d d' : SVal U) :
    (SVal.map (K := K) m d).beq (.map m' d') = (m.beq m' && d.beq d') := rfl
theorem SFields.beq_nil : SFields.beq .nil .nil = true := rfl
theorem SFields.beq_cons {f : Name} {T : Ty} {fs : List (Name × Ty)} (v w : SVal T)
    (rest rest' : SFields fs) :
    SFields.beq (.cons (f := f) v rest) (.cons w rest') = (v.beq w && rest.beq rest') := rfl
theorem SList.beq_nil_nil {E : Ty} : SList.beq (E := E) .nil .nil = true := rfl
theorem SList.beq_nil_cons {E : Ty} (w : SVal E) (rest' : SList E) :
    SList.beq .nil (.cons w rest') = false := rfl
theorem SList.beq_cons_nil {E : Ty} (v : SVal E) (rest : SList E) :
    SList.beq (.cons v rest) .nil = false := rfl
theorem SList.beq_cons_cons {E : Ty} (v w : SVal E) (rest rest' : SList E) :
    SList.beq (.cons v rest) (.cons w rest') = (v.beq w && rest.beq rest') := rfl
theorem SVec.beq_nil {E : Ty} : SVec.beq (E := E) .nil .nil = true := rfl
theorem SVec.beq_cons {E : Ty} {n : Nat} (v w : SVal E) (rest rest' : SVec E n) :
    SVec.beq (.cons v rest) (.cons w rest') = (v.beq w && rest.beq rest') := rfl
theorem SMap.beq_nil_nil {U : Ty} : SMap.beq (U := U) .nil .nil = true := rfl
theorem SMap.beq_nil_cons {U : Ty} (k : Int) (w : SVal U) (rest' : SMap U) :
    SMap.beq .nil (.cons k w rest') = false := rfl
theorem SMap.beq_cons_nil {U : Ty} (k : Int) (v : SVal U) (rest : SMap U) :
    SMap.beq (.cons k v rest) .nil = false := rfl
theorem SMap.beq_cons_cons {U : Ty} (k k' : Int) (v w : SVal U) (rest rest' : SMap U) :
    SMap.beq (.cons k v rest) (.cons k' w rest') = (decide (k = k') && v.beq w && rest.beq rest') :=
  rfl

attribute [irreducible] SVal.beq SFields.beq SList.beq SVec.beq SMap.beq
attribute [eqns SVal.beq_prim SVal.beq_struct SVal.beq_array SVal.beq_fixed SVal.beq_map]
  SVal.beq
attribute [eqns SFields.beq_nil SFields.beq_cons] SFields.beq
attribute [eqns SList.beq_nil_nil SList.beq_nil_cons SList.beq_cons_nil SList.beq_cons_cons]
  SList.beq
attribute [eqns SVec.beq_nil SVec.beq_cons] SVec.beq
attribute [eqns SMap.beq_nil_nil SMap.beq_nil_cons SMap.beq_cons_nil SMap.beq_cons_cons] SMap.beq

mutual
theorem SVal.eq_of_beq : {T : Ty} → (v w : SVal T) → v.beq w = true → v = w
  | _, .prim x, .prim y, h => by
    simp only [SVal.beq, decide_eq_true_eq] at h
    rw [h]
  | _, .struct fs, .struct gs, h => by
    simp only [SVal.beq] at h
    rw [SFields.eq_of_beq fs gs h]
  | _, .array e sh, .array e' sh', h => by
    simp only [SVal.beq, Bool.and_eq_true] at h
    rw [SList.eq_of_beq e e' h.1, SList.eq_of_beq sh sh' h.2]
  | _, .fixed e, .fixed e', h => by
    simp only [SVal.beq] at h
    rw [SVec.eq_of_beq e e' h]
  | _, .map m d, .map m' d', h => by
    simp only [SVal.beq, Bool.and_eq_true] at h
    rw [SMap.eq_of_beq m m' h.1, SVal.eq_of_beq d d' h.2]
termination_by structural _ v => v

theorem SFields.eq_of_beq : {fs : List (Name × Ty)} → (x y : SFields fs) → x.beq y = true → x = y
  | _, .nil, .nil, _ => rfl
  | _, .cons v rest, .cons w rest', h => by
    simp only [SFields.beq, Bool.and_eq_true] at h
    rw [SVal.eq_of_beq v w h.1, SFields.eq_of_beq rest rest' h.2]
termination_by structural _ x => x

theorem SList.eq_of_beq : {E : Ty} → (l l' : SList E) → l.beq l' = true → l = l'
  | _, .nil, .nil, _ => rfl
  | _, .nil, .cons _ _, h => by simp only [SList.beq, Bool.false_eq_true] at h
  | _, .cons _ _, .nil, h => by simp only [SList.beq, Bool.false_eq_true] at h
  | _, .cons v rest, .cons w rest', h => by
    simp only [SList.beq, Bool.and_eq_true] at h
    rw [SVal.eq_of_beq v w h.1, SList.eq_of_beq rest rest' h.2]
termination_by structural _ l => l

theorem SVec.eq_of_beq : {E : Ty} → {n : Nat} → (l l' : SVec E n) → l.beq l' = true → l = l'
  | _, _, .nil, .nil, _ => rfl
  | _, _, .cons v rest, .cons w rest', h => by
    simp only [SVec.beq, Bool.and_eq_true] at h
    rw [SVal.eq_of_beq v w h.1, SVec.eq_of_beq rest rest' h.2]
termination_by structural _ _ l => l

theorem SMap.eq_of_beq : {U : Ty} → (m m' : SMap U) → m.beq m' = true → m = m'
  | _, .nil, .nil, _ => rfl
  | _, .nil, .cons _ _ _, h => by simp only [SMap.beq, Bool.false_eq_true] at h
  | _, .cons _ _ _, .nil, h => by simp only [SMap.beq, Bool.false_eq_true] at h
  | _, .cons k v rest, .cons k' w rest', h => by
    simp only [SMap.beq, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1.1, SVal.eq_of_beq v w h.1.2, SMap.eq_of_beq rest rest' h.2]
termination_by structural _ m => m
end

mutual
theorem SVal.beq_self : {T : Ty} → (v : SVal T) → v.beq v = true
  | _, .prim x => by simp only [SVal.beq, decide_true]
  | _, .struct fs => by simp only [SVal.beq, SFields.beq_self fs]
  | _, .array e sh => by simp only [SVal.beq, SList.beq_self e, SList.beq_self sh, Bool.and_self]
  | _, .fixed e => by simp only [SVal.beq, SVec.beq_self e]
  | _, .map m d => by simp only [SVal.beq, SMap.beq_self m, SVal.beq_self d, Bool.and_self]

theorem SFields.beq_self : {fs : List (Name × Ty)} → (x : SFields fs) → x.beq x = true
  | _, .nil => by simp only [SFields.beq]
  | _, .cons v rest => by simp only [SFields.beq, SVal.beq_self v, SFields.beq_self rest,
      Bool.and_self]

theorem SList.beq_self : {E : Ty} → (l : SList E) → l.beq l = true
  | _, .nil => by simp only [SList.beq]
  | _, .cons v rest => by simp only [SList.beq, SVal.beq_self v, SList.beq_self rest,
      Bool.and_self]

theorem SVec.beq_self : {E : Ty} → {n : Nat} → (l : SVec E n) → l.beq l = true
  | _, _, .nil => by simp only [SVec.beq]
  | _, _, .cons v rest => by simp only [SVec.beq, SVal.beq_self v, SVec.beq_self rest,
      Bool.and_self]

theorem SMap.beq_self : {U : Ty} → (m : SMap U) → m.beq m = true
  | _, .nil => by simp only [SMap.beq]
  | _, .cons k v rest => by simp only [SMap.beq, decide_true, SVal.beq_self v,
      SMap.beq_self rest, Bool.and_self]
end

theorem SVal.beq_iff {T : Ty} {v w : SVal T} : v.beq w = true ↔ v = w :=
  ⟨SVal.eq_of_beq v w, fun h => h ▸ SVal.beq_self v⟩

theorem SFields.beq_iff {fs : List (Name × Ty)} {x y : SFields fs} : x.beq y = true ↔ x = y :=
  ⟨SFields.eq_of_beq x y, fun h => h ▸ SFields.beq_self x⟩

/-- Equality of storage values, by `SVal.beq`: `decide +kernel` evaluates it. -/
instance SVal.decEq {T : Ty} : DecidableEq (SVal T) := fun _ _ => decidable_of_iff _ SVal.beq_iff

/-- Equality of members, so of storages, by `SFields.beq`. -/
instance SFields.decEq {fs : List (Name × Ty)} : DecidableEq (SFields fs) :=
  fun _ _ => decidable_of_iff _ SFields.beq_iff

/-- The slot `push` lands on (`Semantics.pushSlot`), and the slots left. -/
def pushSlot (E : Ty) : List (SVal E) → SVal E × List (SVal E)
  | [] => (SVal.dflt E, [])
  | c :: rest => (if E.isPrimitive then SVal.dflt E else c, rest)

/-! ## Storage -/

/-- A contract's storage: one value per state variable, of its type. -/
abbrev Storage (C : Contract) := SFields C.vars

/-- A storage reference: a state variable and a path into it. -/
structure SRef (C : Contract) (U : Ty) where
  root : Name
  {ty : Ty}
  hroot : C.rootType root = some ty
  path : Path ty U

namespace SRef

variable {C : Contract}

/-- The state variable itself. -/
def ofRoot (r : Name) {T : Ty} (h : C.rootType r = some T) : SRef C T := ⟨r, h, .nil⟩

/-- A reference further along a path. -/
def append {U W : Ty} (r : SRef C U) (q : Path U W) : SRef C W := ⟨r.root, r.hroot, r.path.append q⟩

/-- `b.f`. -/
def field {s f : Name} {T : Ty} (r : SRef C (.ref (.struct s))) (h : C.fieldType s f = some T) :
    SRef C T :=
  r.append (.field h .nil)

/-- `b[i]`. -/
def index {R : RefTy} {k : PrimTy} {V : Ty} (r : SRef C (.ref R)) (it : IndexTy R k V) (i : Int) :
    SRef C V :=
  r.append (Path.index it i)

/-- `b[k]` for the program's index value: a mapping's key as it is hashed
(`PrimTy.key`, a `bool` as `0`/`1`), an array's index as the number. -/
def atKey {R : RefTy} {k : PrimTy} {V : Ty} (r : SRef C (.ref R)) (it : IndexTy R k V)
    (i : k.Denote) : SRef C V :=
  r.index it (PrimTy.key i)

/-- The untyped reference: `(root, segs)`. -/
def erase {U : Ty} (r : SRef C U) : Name × List Semantics.Seg := (r.root, r.path.erase)

end SRef

namespace Storage

variable {C : Contract}

/-- The untyped storage. -/
def erase (st : Storage C) : List (Name × Semantics.SVal) := SFields.erase st

/-- The storage a contract starts with: every state variable at its default
(`Contract.initStorage`). -/
def init (C : Contract) : Storage C := SFields.dflt C.vars

/-- The value at a reference (`State.findStorage`). -/
def find {U : Ty} (st : Storage C) (r : SRef C U) : Option (SVal U) :=
  (st.get r.hroot).find r.path

/-- `SVal.findLive` at a reference (`State.findLive`). -/
def findLive {U : Ty} (st : Storage C) (r : SRef C U) : Option (SVal U) :=
  (st.get r.hroot).findLive r.path

/-- The storage with the value at a reference replaced (`State.saveStorage`). -/
def save {U : Ty} (st : Storage C) (r : SRef C U) (new : SVal U) : Option (Storage C) := do
  let v ← (st.get r.hroot).save r.path new
  some (st.set r.hroot v)

/-- `checkIndex`'s test on the value at `b`: every key of a mapping, an index
below an array's live length.  By `casesOn`, so the kernel casts nothing. -/
def inBounds {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) (i : Int) :
    SVal (.ref R) → Option Unit :=
  @IndexTy.casesOn (fun R _ _ _ => SVal (.ref R) → Option Unit) R k V it
    (fun {_} {_} _ => some ())
    (fun {_} {_} a => @ArrTy.casesOn (fun R _ _ => SVal (.ref R) → Option Unit) _ _ a
      (fun {_} v =>
        let w : SList _ × SList _ := SVal.view v
        if 0 ≤ i ∧ i.toNat < w.1.length then some () else none)
      (fun {_} {n} _ => if 0 ≤ i ∧ i.toNat < n then some () else none))

/-- `b[i]`'s index in bounds where the program takes it (`State.checkIndex`):
a mapping takes every key, an array an index below its live length. -/
def checkIndex {R : RefTy} {k : PrimTy} {V : Ty} (st : Storage C) (r : SRef C (.ref R))
    (it : IndexTy R k V) (i : Int) : Option Unit := do
  inBounds it i (← st.find r)

/-- The live length of a dynamic array (`arrayLen`). -/
def len {E : Ty} (st : Storage C) (r : SRef C (.ref (.array E))) : Option Nat := do
  let w : SList E × SList E := SVal.view (← st.find r)
  some w.1.length

/-- `b.push(…)` (`pushAt`): the element `val` makes of the slot it lands on,
appended. -/
def push {E : Ty} (st : Storage C) (r : SRef C (.ref (.array E)))
    (val : SVal E → Option (SVal E)) : Option (Storage C) := do
  let w : SList E × SList E := SVal.view (← st.find r)
  let (slot, sh') := pushSlot E w.2.toList
  let x ← val slot
  st.save r (.array (.ofList (w.1.toList ++ [x])) (.ofList sh'))

/-- `b.push()` as a place (`pushPlaceAt`): the slot appended, and its index. -/
def pushPlace {E : Ty} (st : Storage C) (r : SRef C (.ref (.array E))) :
    Option (Storage C × Nat) := do
  let w : SList E × SList E := SVal.view (← st.find r)
  let (slot, sh') := pushSlot E w.2.toList
  let st' ← st.save r (.array (.ofList (w.1.toList ++ [slot])) (.ofList sh'))
  some (st', w.1.length)

/-- `b.pop()` (`popAt`): the last element cleared into the slots past the
end, or moved there as it is when `keep`; an empty array reverts. -/
def pop {E : Ty} (st : Storage C) (keep : Bool) (r : SRef C (.ref (.array E))) :
    Option (Storage C) := do
  let w : SList E × SList E := SVal.view (← st.find r)
  match w.1.toList.reverse with
  | [] => none
  | last :: restRev =>
    st.save r (.array (.ofList restRev.reverse)
      (.ofList ((if keep then last else last.defaultOf) :: w.2.toList)))

/-- `delete b` on storage: its value reset in place (`SVal.defaultOf`). -/
def delete {T : Ty} (st : Storage C) (r : SRef C T) : Option (Storage C) := do
  st.save r (← st.find r).defaultOf

/-- An assignment's write (`State.writeStorage`): a word stored, a struct or
an array copied over what is there. -/
def write {T : Ty} (st : Storage C) (r : SRef C T) (new : SVal T) : Option (Storage C) :=
  if new.isPrim then st.save r new
  else do st.save r ((← st.find r).overlay new)

end Storage

end Solidity.Core
