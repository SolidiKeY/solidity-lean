import Solidity.Semantics.Value
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
bounds: they return an `Option`, `none` for that revert (`TRes.ofOpt`).

The shapes are solkey's storage trees (`structRules.key`): an array keeps
the slots past its end (`shadow`), a mapping its default.  A fixed-size
array keeps none (no operation puts one there).  (The untyped storage this
mirrored went at W10.5.6.)

Defaults (`SVal.dflt`) are structural on the rank `structDef_rank_lt`
certifies, so the kernel can reduce them; their fuel is `rankBound`, which
reads no struct name.

Nothing the kernel evaluates `match`es on the indexed families (Gate G0,
conditions 1 and 2): `find`, `findLive`, `save`, `SFields.get`/`set` and
`Path.append` are written with the recursors (`Path.rec` over `SVal.view`,
`SFields.rec`), `Path.index` and `inBounds` with `casesOn`, the functions on
a whole value are folds (`SVal.fold`), and the array operations read their
array through `SVal.view`.  Each recursor form has a `match` twin as its
compiled form (`implemented_by`) and a theorem that they are equal
(`SVal.fold_eq_foldM`, `SVal.defaultOf_eq_defaultOfM`, …); `defaultOf`,
`strip`, `overlay` and the `toList`s have their own twins rather than
`SVal.foldM`, which is strict and would walk a mapping's entries.  These
state their equations and are irreducible, so a proof rewrites them as it
would a `match` (`Solidity/Eqns.lean`).
-/

namespace Solidity

open Semantics (structDef lookupBy setBy tyRank fieldsRank structRank)

mutual
/-- A storage value of type `T`. -/
inductive SVal : Ty → Type where
  | prim {p : PrimTy} (v : p.Denote) : SVal (.prim p)
  | struct {s : Name} (fs : SFields (structDef s)) : SVal (.ref (.struct s))
  /-- The live elements, fewer than `2^256` (a length is a `uint`; a push at
  the bound is out of gas, `Storage.full`), and the slots past the end. -/
  | array {E : Ty} {n : Nat} (elems : SVec E n) (shadow : SList E) (hn : n < 2 ^ 256) :
      SVal (.ref (.array E))
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

Every function the kernel evaluates on a whole value (`SVal.dflt`,
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
  array : {E : Ty} → {n : Nat} → SVec E n → SList E → n < 2 ^ 256 → W E n → L E →
    V (.ref (.array E))
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
  | _, .array e sh h => a.array e sh h (SVec.foldM a e) (SList.foldM a sh)
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
  | _, .array e sh h => by
    show a.array e sh h (e.fold a) (sh.fold a) = _
    rw [SVec.fold_eq_foldM a e, SList.fold_eq_foldM a sh, SVal.foldM]
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

/-- What a dynamic array holds: its live elements, their number below
`2^256`, and the slots past the end. -/
structure ArrView (E : Ty) where
  {n : Nat}
  elems : SVec E n
  shadow : SList E
  hn : n < 2 ^ 256

/-- What a value of type `T` holds, by `T`. -/
def Shape : Ty → Type
  | .prim p => p.Denote
  | .ref (.struct s) => SFields (structDef s)
  | .ref (.array E) => ArrView E
  | .ref (.fixed E n) => SVec E n
  | .ref (.mapping _ V) => SMap V × SVal V

/-- A value's contents, at the type its type computes. -/
def SVal.view {T : Ty} (v : SVal T) : Shape T :=
  @SVal.casesOn (fun T _ => Shape T) T v (fun {_} x => x) (fun {_} fs => fs)
    (fun {_} {_} e sh h => ⟨e, sh, h⟩) (fun {_} {_} e => e) (fun {_} {_} m d => (m, d))

theorem SVal.view_prim {p : PrimTy} (x : p.Denote) : (SVal.prim x).view = x := rfl
theorem SVal.view_struct {s : Name} (fs : SFields (structDef s)) : (SVal.struct fs).view = fs := rfl
theorem SVal.view_array {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E) (h : n < 2 ^ 256) :
    (SVal.array e sh h).view = ⟨e, sh, h⟩ := rfl
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
  array := fun _ _ _ _ _ => ()
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

theorem toList_eq_toListM {E : Ty} : (l : SList E) → l.toList = l.toListM
  | .nil => by rw [toList_nil, toListM]
  | .cons v rest => by rw [toList_cons, toListM, toList_eq_toListM rest]

def ofList {E : Ty} : List (SVal E) → SList E
  | [] => .nil
  | v :: rest => .cons v (ofList rest)

@[simp] theorem toList_ofList {E : Ty} : (l : List (SVal E)) → (ofList l).toList = l
  | [] => by rw [ofList, toList_nil]
  | v :: rest => by rw [ofList, toList_cons, toList_ofList rest]

@[simp] theorem ofList_toList {E : Ty} : (l : SList E) → ofList l.toList = l
  | .nil => by rw [toList_nil, ofList]
  | .cons v rest => by rw [toList_cons, ofList, ofList_toList rest]


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

theorem toList_eq_toListM {E : Ty} : {n : Nat} → (l : SVec E n) → l.toList = l.toListM
  | _, .nil => by rw [toList_nil, toListM]
  | _, .cons v rest => by rw [toList_cons, toListM, toList_eq_toListM rest]

theorem length_toList {E : Ty} : {n : Nat} → (v : SVec E n) → v.toList.length = n
  | _, .nil => by rw [toList_nil, List.length_nil]
  | _, .cons _ rest => by rw [toList_cons, List.length_cons, length_toList rest]


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
  array := fun _ _ _ _ _ => ()
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

theorem set_eq_setM {E : Ty} : {n : Nat} → (l : SVec E n) → (i : Nat) → (x : SVal E) →
    l.set i x = l.setM i x
  | _, .nil, _, _ => by rw [set_nil, setM]
  | _, .cons _ _, 0, _ => by rw [set_cons_zero, setM]
  | _, .cons v rest, i + 1, x => by rw [set_cons_succ, setM, set_eq_setM rest i x]

/-- A list as a vector of its length. -/
def ofList {E : Ty} : (l : List (SVal E)) → SVec E l.length
  | [] => .nil
  | v :: rest => .cons v (ofList rest)

@[simp] theorem toList_ofList {E : Ty} : (l : List (SVal E)) → (ofList l).toList = l
  | [] => by rw [ofList, toList_nil]
  | v :: rest => by rw [ofList, toList_cons, toList_ofList rest]

/-- Two vectors with the same elements are the same. -/
theorem eq_of_toList_eq {E : Ty} : {n : Nat} → (l l' : SVec E n) → l.toList = l'.toList → l = l'
  | _, .nil, .nil, _ => rfl
  | _, .cons v rest, .cons v' rest', h => by
    rw [toList_cons, toList_cons, List.cons.injEq] at h
    rw [h.1, eq_of_toList_eq rest rest' h.2]

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

theorem toList_eq_toListM {V : Ty} : (m : SMap V) → m.toList = m.toListM
  | .nil => by rw [toList_nil, toListM]
  | .cons k v rest => by rw [toList_cons, toListM, toList_eq_toListM rest]

def ofList {V : Ty} : List (Int × SVal V) → SMap V
  | [] => .nil
  | (k, v) :: rest => .cons k v (ofList rest)

@[simp] theorem toList_ofList {V : Ty} : (l : List (Int × SVal V)) → (ofList l).toList = l
  | [] => by rw [ofList, toList_nil]
  | (k, v) :: rest => by rw [ofList, toList_cons, toList_ofList rest]


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
    (fun {_} _ => ()) (fun {_} _ _ => ()) (fun {_} {_} _ _ _ _ _ => ()) (fun {_} {_} _ _ => ())
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
    (fun {_} _ => ()) (fun {_} _ _ => ()) (fun {_} {_} _ _ _ _ _ => ()) (fun {_} {_} _ _ => ())
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

/-- An empty array is within the bound. -/
theorem SVal.zero_lt_bound : 0 < 2 ^ 256 := by decide

/-! ## Defaults

`SVal.dflt T` is `T`'s default: by recursion on a bound `k` of the rank,
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
  | .array _, _ => .array .nil .nil SVal.zero_lt_bound
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

/-- The default of `T`. -/
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

/-- The segments, as the side conditions read them (`Theory/Segs.lean`). -/
def erase : {T U : Ty} → Path T U → List Semantics.Seg
  | _, _, .nil => []
  | _, _, @Path.field _ f _ _ _ p => .field f :: p.erase
  | _, _, .at i p => .at i :: p.erase
  | _, _, .atF i p => .at i :: p.erase
  | _, _, .key k p => .at k :: p.erase

/-- `append` by `match`, its compiled form. -/
def appendM : {T U W : Ty} → Path T U → Path U W → Path T W
  | _, _, _, .nil, q => q
  | _, _, _, .field h p, q => .field h (p.appendM q)
  | _, _, _, .at i p, q => .at i (p.appendM q)
  | _, _, _, .atF i p, q => .atF i (p.appendM q)
  | _, _, _, .key k p, q => .key k (p.appendM q)

/-- A path followed by another, by the recursor (the typed run reduces it at
every `SRef.field`/`index` step). -/
@[implemented_by appendM]
def append {T U W : Ty} (p : Path T U) (q : Path U W) : Path T W :=
  @Path.rec (fun T U _ => Path U W → Path T W) (fun {_} q => q)
    (fun {_} {_} {_} {_} h _ ih q => .field h (ih q)) (fun {_} {_} i _ ih q => .at i (ih q))
    (fun {_} {_} {_} i _ ih q => .atF i (ih q)) (fun {_} {_} {_} k _ ih q => .key k (ih q)) T U p q

theorem append_nil {T W : Ty} (q : Path T W) : (Path.nil (T := T)).append q = q := rfl
theorem append_field {s f : Name} {T U W : Ty} (h : lookupBy f (structDef s) = some T)
    (p : Path T U) (q : Path U W) : (Path.field h p).append q = .field h (p.append q) := rfl
theorem append_at {E U W : Ty} (i : Int) (p : Path E U) (q : Path U W) :
    (Path.at i p).append q = .at i (p.append q) := rfl
theorem append_atF {E U W : Ty} {n : Nat} (i : Int) (p : Path E U) (q : Path U W) :
    (Path.atF (n := n) i p).append q = .atF i (p.append q) := rfl
theorem append_key {K V U W : Ty} (k : Int) (p : Path V U) (q : Path U W) :
    (Path.key (K := K) k p).append q = .key k (p.append q) := rfl

attribute [irreducible] append
attribute [eqns append_nil append_field append_at append_atF append_key] append

theorem append_eq_appendM : {T U W : Ty} → (p : Path T U) → (q : Path U W) →
    p.append q = p.appendM q
  | _, _, _, .nil, q => by rw [append_nil, appendM]
  | _, _, _, .field h p, q => by rw [append_field, appendM, append_eq_appendM p q]
  | _, _, _, .at i p, q => by rw [append_at, appendM, append_eq_appendM p q]
  | _, _, _, .atF i p, q => by rw [append_atF, appendM, append_eq_appendM p q]
  | _, _, _, .key k p, q => by rw [append_key, appendM, append_eq_appendM p q]

theorem erase_append : {T U W : Ty} → (p : Path T U) → (q : Path U W) →
    (p.append q).erase = p.erase ++ q.erase
  | _, _, _, .nil, _ => by rw [append_nil]; rfl
  | _, _, _, .field _ p, q => by rw [append_field]; exact congrArg (_ :: ·) (erase_append p q)
  | _, _, _, .at _ p, q => by rw [append_at]; exact congrArg (_ :: ·) (erase_append p q)
  | _, _, _, .atF _ p, q => by rw [append_atF]; exact congrArg (_ :: ·) (erase_append p q)
  | _, _, _, .key _ p, q => by rw [append_key]; exact congrArg (_ :: ·) (erase_append p q)

/-- The one step `b[i]` takes, by how `R` is indexed.  By `casesOn`, so the
kernel casts nothing. -/
def index {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) (i : Int) : Path (.ref R) V :=
  @IndexTy.casesOn (fun R _ V _ => Path (.ref R) V) R k V it (fun {_} {_} => .key i .nil)
    (fun {_} {_} a => @ArrTy.casesOn (fun R E _ => Path (.ref R) E) _ _ a
      (fun {_} => .at i .nil) (fun {_} {_} => .atF i .nil))

theorem index_map {k : PrimTy} {V : Ty} (i : Int) :
    index (IndexTy.map (k := k) (V := V)) i = .key i .nil := rfl
theorem index_dyn {E : Ty} (i : Int) : index (IndexTy.arr (ArrTy.dyn (E := E))) i = .at i .nil :=
  rfl
theorem index_fixed {E : Ty} {n : Nat} (i : Int) :
    index (IndexTy.arr (ArrTy.fixed (E := E) (n := n))) i = .atF i .nil := rfl

attribute [irreducible] index
attribute [eqns index_map index_dyn index_fixed] index

theorem erase_index : {R : RefTy} → {k : PrimTy} → {V : Ty} → (it : IndexTy R k V) → (i : Int) →
    (index it i).erase = [.at i]
  | _, _, _, .map, _ => by rw [index_map]; rfl
  | _, _, _, .arr .dyn, _ => by rw [index_dyn]; rfl
  | _, _, _, .arr .fixed, _ => by rw [index_fixed]; rfl

end Path

/-! ## Find and save

The kernel evaluates these (`decide +kernel`, the symbolic execution's
`Eq.refl`), so they are written with the recursor of `Path` and read a value
through `SVal.view`, whose type `Shape T` is computed from `T`: no `match` on
an indexed family, whose casts cost the kernel a factor of 40 here
(`docs/intrinsic.md`, "M4 lane", and Gate G0, condition 2).  The compiler
cannot compile a recursor, so each has a `match` twin (`SVal.findM`, …) as
its `implemented_by`, and a theorem that they are equal
(`SVal.find_eq_findM`, …). -/

/-- What `save` keeps live is within the bound. -/
theorem SVal.take_lt_bound {α : Type} {n : Nat} (l : List α) (h : n < 2 ^ 256) :
    (l.take n).length < 2 ^ 256 :=
  Nat.lt_of_le_of_lt (List.length_take_le n l) h

/-- `SVal.find` by `match`, its compiled form. -/
def SVal.findM : {T U : Ty} → SVal T → Path T U → Option (SVal U)
  | _, _, v, .nil => some v
  | _, _, .struct fs, .field h p => (fs.get h).findM p
  | _, _, .array e sh _, .at i p =>
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
  | _, _, .array e _ _, .at i p =>
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
  | _, _, @SVal.array _ n e sh h, .at i p, new =>
    if 0 ≤ i then
      match (e.toList ++ sh.toList)[i.toNat]? with
      | some x => do
        let x' ← x.saveM p new
        let slots := (e.toList ++ sh.toList).set i.toNat x'
        some (.array (SVec.ofList (slots.take n)) (.ofList (slots.drop n))
          (SVal.take_lt_bound slots h))
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

/-- The value at a path (solkey's `find`): `none` where an index is past
the slots. -/
@[implemented_by SVal.findM]
def SVal.find {T U : Ty} (v : SVal T) (p : Path T U) : Option (SVal U) :=
  @Path.rec (fun T U _ => SVal T → Option (SVal U))
    (fun {_} v => some v)
    (fun {_} {_} {_} {_} h _ ih v => ih (SFields.get (SVal.view v) h))
    (fun {_} {_} i _ ih v =>
      let w : ArrView _ := SVal.view v
      if 0 ≤ i then
        match (w.elems.toList ++ w.shadow.toList)[i.toNat]? with
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
(`findLive`): `find` past an array's end is `none`. -/
@[implemented_by SVal.findLiveM]
def SVal.findLive {T U : Ty} (v : SVal T) (p : Path T U) : Option (SVal U) :=
  @Path.rec (fun T U _ => SVal T → Option (SVal U))
    (fun {_} v => some v)
    (fun {_} {_} {_} {_} h _ ih v => ih (SFields.get (SVal.view v) h))
    (fun {_} {_} i _ ih v =>
      let w : ArrView _ := SVal.view v
      if 0 ≤ i then
        match w.elems.toList[i.toNat]? with
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

/-- The value with the one at a path replaced (solkey's `save`). -/
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
      let w : ArrView _ := SVal.view v
      if 0 ≤ i then
        match (w.elems.toList ++ w.shadow.toList)[i.toNat]? with
        | some x => do
          let x' ← ih x new
          let slots := (w.elems.toList ++ w.shadow.toList).set i.toNat x'
          some (.array (SVec.ofList (slots.take w.n)) (.ofList (slots.drop w.n))
            (SVal.take_lt_bound slots w.hn))
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

/-! The compiled forms of `defaultOf`, `strip` and `overlay` are the `match`
twins below, not `SVal.foldM`: the fold is strict in every argument of a
step, so it would walk a mapping's entries to throw them away. -/

mutual
/-- `SVal.defaultOf` by `match`, its compiled form. -/
def SVal.defaultOfM : {T : Ty} → SVal T → SVal T
  | _, @SVal.prim p _ => .prim (PrimTy.dflt p)
  | _, .struct fs => .struct (SFields.defaultOfM fs)
  | _, .array e sh _ => .array .nil (.ofList ((SVec.defaultOfM e).toList ++ sh.toList))
    SVal.zero_lt_bound
  | _, .fixed e => .fixed (SVec.defaultOfM e)
  | _, .map m d => .map m d

def SFields.defaultOfM : {fs : List (Name × Ty)} → SFields fs → SFields fs
  | _, .nil => .nil
  | _, .cons v rest => .cons (SVal.defaultOfM v) (SFields.defaultOfM rest)

def SList.defaultOfM : {E : Ty} → SList E → SList E
  | _, .nil => .nil
  | _, .cons v rest => .cons (SVal.defaultOfM v) (SList.defaultOfM rest)

def SVec.defaultOfM : {E : Ty} → {n : Nat} → SVec E n → SVec E n
  | _, _, .nil => .nil
  | _, _, .cons v rest => .cons (SVal.defaultOfM v) (SVec.defaultOfM rest)
end

/-- `delete`'s value. -/
def defaultOfFold : Fold where
  V T := SVal T
  F fs := SFields fs
  L E := SList E
  W E n := SVec E n
  M U := SMap U
  prim := fun {p} _ => .prim (PrimTy.dflt p)
  struct := fun _ ih => .struct ih
  array := fun _ sh _ ie _ => .array .nil (.ofList (SVec.toList ie ++ sh.toList)) SVal.zero_lt_bound
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

/-- `delete`'s value (solkey's `delAt`): primitives reset, members
and elements recursively, a dynamic array emptied into the slots past its
end, a mapping left as it is. -/
@[implemented_by SVal.defaultOfM]
def SVal.defaultOf {T : Ty} (v : SVal T) : SVal T := v.fold defaultOfFold
@[implemented_by SFields.defaultOfM]
def SFields.defaultOf {fs : List (Name × Ty)} (x : SFields fs) : SFields fs := x.fold defaultOfFold
@[implemented_by SList.defaultOfM]
def SList.defaultOf {E : Ty} (l : SList E) : SList E := l.fold defaultOfFold
@[implemented_by SVec.defaultOfM]
def SVec.defaultOf {E : Ty} {n : Nat} (l : SVec E n) : SVec E n := l.fold defaultOfFold

theorem SVal.defaultOf_prim {p : PrimTy} (v : p.Denote) :
    (SVal.prim v).defaultOf = .prim (PrimTy.dflt p) := rfl
theorem SVal.defaultOf_struct {s : Name} (fs : SFields (structDef s)) :
    (SVal.struct fs).defaultOf = .struct fs.defaultOf := rfl
theorem SVal.defaultOf_array {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E) (h : n < 2 ^ 256) :
    (SVal.array e sh h).defaultOf =
      .array .nil (.ofList (e.defaultOf.toList ++ sh.toList)) SVal.zero_lt_bound := rfl
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

mutual
theorem SVal.defaultOf_eq_defaultOfM : {T : Ty} → (v : SVal T) → v.defaultOf = v.defaultOfM
  | _, .prim _ => by rw [SVal.defaultOf_prim, SVal.defaultOfM]
  | _, .struct fs => by
    rw [SVal.defaultOf_struct, SVal.defaultOfM, SFields.defaultOf_eq_defaultOfM fs]
  | _, .array e sh _ => by
    rw [SVal.defaultOf_array, SVal.defaultOfM, SVec.defaultOf_eq_defaultOfM e]
  | _, .fixed e => by rw [SVal.defaultOf_fixed, SVal.defaultOfM, SVec.defaultOf_eq_defaultOfM e]
  | _, .map _ _ => by rw [SVal.defaultOf_map, SVal.defaultOfM]

theorem SFields.defaultOf_eq_defaultOfM : {fs : List (Name × Ty)} → (x : SFields fs) →
    x.defaultOf = x.defaultOfM
  | _, .nil => by rw [SFields.defaultOf_nil, SFields.defaultOfM]
  | _, .cons v rest => by
    rw [SFields.defaultOf_cons, SFields.defaultOfM, SVal.defaultOf_eq_defaultOfM v,
      SFields.defaultOf_eq_defaultOfM rest]

theorem SList.defaultOf_eq_defaultOfM : {E : Ty} → (l : SList E) → l.defaultOf = l.defaultOfM
  | _, .nil => by rw [SList.defaultOf_nil, SList.defaultOfM]
  | _, .cons v rest => by
    rw [SList.defaultOf_cons, SList.defaultOfM, SVal.defaultOf_eq_defaultOfM v,
      SList.defaultOf_eq_defaultOfM rest]

theorem SVec.defaultOf_eq_defaultOfM : {E : Ty} → {n : Nat} → (l : SVec E n) →
    l.defaultOf = l.defaultOfM
  | _, _, .nil => by rw [SVec.defaultOf_nil, SVec.defaultOfM]
  | _, _, .cons v rest => by
    rw [SVec.defaultOf_cons, SVec.defaultOfM, SVal.defaultOf_eq_defaultOfM v,
      SVec.defaultOf_eq_defaultOfM rest]
end

mutual
/-- `SVal.strip` by `match`, its compiled form. -/
def SVal.stripM : {T : Ty} → SVal T → SVal T
  | _, .prim v => .prim v
  | _, .struct fs => .struct (SFields.stripM fs)
  | _, .array e _ h => .array (SVec.stripM e) .nil h
  | _, .fixed e => .fixed (SVec.stripM e)
  | _, .map m d => .map m d

def SFields.stripM : {fs : List (Name × Ty)} → SFields fs → SFields fs
  | _, .nil => .nil
  | _, .cons v rest => .cons (SVal.stripM v) (SFields.stripM rest)

def SList.stripM : {E : Ty} → SList E → SList E
  | _, .nil => .nil
  | _, .cons v rest => .cons (SVal.stripM v) (SList.stripM rest)

def SVec.stripM : {E : Ty} → {n : Nat} → SVec E n → SVec E n
  | _, _, .nil => .nil
  | _, _, .cons v rest => .cons (SVal.stripM v) (SVec.stripM rest)
end

/-- A value as nothing has written it. -/
def stripFold : Fold where
  V T := SVal T
  F fs := SFields fs
  L E := SList E
  W E n := SVec E n
  M U := SMap U
  prim := fun v => .prim v
  struct := fun _ ih => .struct ih
  array := fun _ _ h ie _ => .array ie .nil h
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

/-- A value as written to slots nothing has written (`strip`):
no slots past an array's end. -/
@[implemented_by SVal.stripM]
def SVal.strip {T : Ty} (v : SVal T) : SVal T := v.fold stripFold
@[implemented_by SFields.stripM]
def SFields.strip {fs : List (Name × Ty)} (x : SFields fs) : SFields fs := x.fold stripFold
@[implemented_by SList.stripM]
def SList.strip {E : Ty} (l : SList E) : SList E := l.fold stripFold
@[implemented_by SVec.stripM]
def SVec.strip {E : Ty} {n : Nat} (l : SVec E n) : SVec E n := l.fold stripFold

theorem SVal.strip_prim {p : PrimTy} (v : p.Denote) : (SVal.prim v).strip = .prim v := rfl
theorem SVal.strip_struct {s : Name} (fs : SFields (structDef s)) :
    (SVal.struct fs).strip = .struct fs.strip := rfl
theorem SVal.strip_array {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E) (h : n < 2 ^ 256) :
    (SVal.array e sh h).strip = .array e.strip .nil h := rfl
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

mutual
theorem SVal.strip_eq_stripM : {T : Ty} → (v : SVal T) → v.strip = v.stripM
  | _, .prim _ => by rw [SVal.strip_prim, SVal.stripM]
  | _, .struct fs => by rw [SVal.strip_struct, SVal.stripM, SFields.strip_eq_stripM fs]
  | _, .array e _ _ => by rw [SVal.strip_array, SVal.stripM, SVec.strip_eq_stripM e]
  | _, .fixed e => by rw [SVal.strip_fixed, SVal.stripM, SVec.strip_eq_stripM e]
  | _, .map _ _ => by rw [SVal.strip_map, SVal.stripM]

theorem SFields.strip_eq_stripM : {fs : List (Name × Ty)} → (x : SFields fs) →
    x.strip = x.stripM
  | _, .nil => by rw [SFields.strip_nil, SFields.stripM]
  | _, .cons v rest => by
    rw [SFields.strip_cons, SFields.stripM, SVal.strip_eq_stripM v, SFields.strip_eq_stripM rest]

theorem SList.strip_eq_stripM : {E : Ty} → (l : SList E) → l.strip = l.stripM
  | _, .nil => by rw [SList.strip_nil, SList.stripM]
  | _, .cons v rest => by
    rw [SList.strip_cons, SList.stripM, SVal.strip_eq_stripM v, SList.strip_eq_stripM rest]

theorem SVec.strip_eq_stripM : {E : Ty} → {n : Nat} → (l : SVec E n) → l.strip = l.stripM
  | _, _, .nil => by rw [SVec.strip_nil, SVec.stripM]
  | _, _, .cons v rest => by
    rw [SVec.strip_cons, SVec.stripM, SVal.strip_eq_stripM v, SVec.strip_eq_stripM rest]
end

mutual
/-- `SVal.overlay` by `match`, its compiled form. -/
def SVal.overlayM : {T : Ty} → SVal T → SVal T → SVal T
  | _, _, .prim v => .prim v
  | _, .struct ofs, .struct nfs => .struct (SFields.overlayM ofs nfs)
  | _, @SVal.array _ m oel osh _, @SVal.array _ n nel _ h =>
    .array (SVec.overlayOnM (oel.toList ++ osh.toList) nel)
      (.ofList ((oel.toList.drop n).map SVal.defaultOf ++ osh.toList.drop (n - m))) h
  | _, .fixed oel, .fixed nel => .fixed (SVec.overlayOnM oel.toList nel)
  | _, .map oe od, .map _ _ => .map oe od

def SFields.overlayM : {fs : List (Name × Ty)} → SFields fs → SFields fs → SFields fs
  | _, .nil, .nil => .nil
  | _, .cons o os, .cons v rest => .cons (SVal.overlayM o v) (SFields.overlayM os rest)

def SVec.overlayOnM : {E : Ty} → {n : Nat} → List (SVal E) → SVec E n → SVec E n
  | _, _, [], rest => SVec.strip rest
  | _, _, o :: os, .cons v rest => .cons (SVal.overlayM o v) (SVec.overlayOnM os rest)
  | _, _, _ :: _, .nil => .nil
end

/-- A copy written over an old value: by recursion on the new one, the old
one read through the views. -/
def overlayFold : Fold where
  V T := SVal T → SVal T
  F fs := SFields fs → SFields fs
  L _ := Unit
  W E n := List (SVal E) → SVec E n
  M _ := Unit
  prim := fun v _ => .prim v
  struct := fun _ ih o => .struct (ih (SVal.view o))
  array := fun {_} {n} _ _ h ie _ o =>
    let w : ArrView _ := SVal.view o
    .array (ie (w.elems.toList ++ w.shadow.toList))
      (.ofList ((w.elems.toList.drop n).map SVal.defaultOf ++ w.shadow.toList.drop (n - w.n))) h
  fixed := fun _ ie o => .fixed (ie (SVal.view o : SVec _ _).toList)
  map := fun _ _ _ _ o => o
  fnil := fun _ => .nil
  fcons := fun _ _ iv ir os =>
    let w := SFields.view os
    .cons (iv w.1) (ir w.2)
  lnil := ()
  lcons := fun _ _ _ _ => ()
  wnil := fun _ => .nil
  wcons := fun v rest iv ir os =>
    match os with
    | [] => .cons v.strip rest.strip
    | o :: os => .cons (iv o) (ir os)
  mnil := ()
  mcons := fun _ _ _ _ _ => ()

/-- A copy of `new` written over `old` (`overlay`): member by
member in their order, as solc copies, element by element over the slots
it lands on, the old elements past the new length cleared, a mapping kept. -/
@[implemented_by SVal.overlayM]
def SVal.overlay {T : Ty} (old new : SVal T) : SVal T := new.fold overlayFold old
@[implemented_by SFields.overlayM]
def SFields.overlay {fs : List (Name × Ty)} (old new : SFields fs) : SFields fs :=
  new.fold overlayFold old
/-- The new elements over the old slots, as far as there are old slots. -/
@[implemented_by SVec.overlayOnM]
def SVec.overlayOn {E : Ty} {n : Nat} (old : List (SVal E)) (new : SVec E n) : SVec E n :=
  new.fold overlayFold old

theorem SVal.overlay_prim {p : PrimTy} (o : SVal (.prim p)) (v : p.Denote) :
    o.overlay (.prim v) = .prim v := rfl
theorem SVal.overlay_struct {s : Name} (ofs nfs : SFields (structDef s)) :
    (SVal.struct ofs).overlay (.struct nfs) = .struct (ofs.overlay nfs) := rfl
theorem SVal.overlay_array {E : Ty} {m n : Nat} (oel : SVec E m) (osh : SList E)
    (h₁ : m < 2 ^ 256) (nel : SVec E n) (nsh : SList E) (h₂ : n < 2 ^ 256) :
    (SVal.array oel osh h₁).overlay (.array nel nsh h₂) =
      .array (SVec.overlayOn (oel.toList ++ osh.toList) nel)
        (.ofList ((oel.toList.drop n).map SVal.defaultOf ++ osh.toList.drop (n - m))) h₂ := rfl
theorem SVal.overlay_fixed {E : Ty} {n : Nat} (oel nel : SVec E n) :
    (SVal.fixed oel).overlay (.fixed nel) = .fixed (SVec.overlayOn oel.toList nel) := rfl
theorem SVal.overlay_map {K U : Ty} (oe ne : SMap U) (od nd : SVal U) :
    (SVal.map (K := K) oe od).overlay (.map ne nd) = .map oe od := rfl
theorem SFields.overlay_nil : SFields.overlay .nil .nil = .nil := rfl
theorem SFields.overlay_cons {f : Name} {T : Ty} {fs : List (Name × Ty)} (o v : SVal T)
    (os rest : SFields fs) :
    SFields.overlay (.cons (f := f) o os) (.cons v rest) = .cons (o.overlay v) (os.overlay rest) :=
  rfl
theorem SVec.overlayOn_nil {E : Ty} (os : List (SVal E)) : SVec.overlayOn os (.nil (E := E)) = .nil :=
  rfl
theorem SVec.overlayOn_nil_cons {E : Ty} {n : Nat} (v : SVal E) (rest : SVec E n) :
    SVec.overlayOn [] (.cons v rest) = .cons v.strip rest.strip := rfl
theorem SVec.overlayOn_cons_cons {E : Ty} {n : Nat} (o : SVal E) (os : List (SVal E)) (v : SVal E)
    (rest : SVec E n) :
    SVec.overlayOn (o :: os) (.cons v rest) = .cons (o.overlay v) (SVec.overlayOn os rest) := rfl

attribute [irreducible] SVal.overlay SFields.overlay SVec.overlayOn
attribute [eqns SVal.overlay_prim SVal.overlay_struct SVal.overlay_array SVal.overlay_fixed
  SVal.overlay_map] SVal.overlay
attribute [eqns SFields.overlay_nil SFields.overlay_cons] SFields.overlay
attribute [eqns SVec.overlayOn_nil SVec.overlayOn_nil_cons SVec.overlayOn_cons_cons]
  SVec.overlayOn

/-- `SVec.overlayOn` over no old slots: the new elements as nothing wrote
them. -/
theorem SVec.overlayOn_nil_left {E : Ty} : {n : Nat} → (l : SVec E n) →
    SVec.overlayOn [] l = l.strip
  | _, .nil => by rw [overlayOn_nil, strip_nil]
  | _, .cons v rest => by rw [overlayOn_nil_cons, strip_cons]

mutual
theorem SVal.overlay_eq_overlayM : {T : Ty} → (o v : SVal T) → o.overlay v = o.overlayM v
  | _, _, .prim _ => by rw [SVal.overlay_prim, SVal.overlayM]
  | _, .struct ofs, .struct nfs => by
    rw [SVal.overlay_struct, SVal.overlayM, SFields.overlay_eq_overlayM ofs nfs]
  | _, .array oel osh _, .array nel _ _ => by
    rw [SVal.overlay_array, SVal.overlayM, SVec.overlayOn_eq_overlayOnM _ nel]
  | _, .fixed oel, .fixed nel => by
    rw [SVal.overlay_fixed, SVal.overlayM, SVec.overlayOn_eq_overlayOnM _ nel]
  | _, .map _ _, .map _ _ => by rw [SVal.overlay_map, SVal.overlayM]

theorem SFields.overlay_eq_overlayM : {fs : List (Name × Ty)} → (os x : SFields fs) →
    os.overlay x = os.overlayM x
  | _, .nil, .nil => by rw [SFields.overlay_nil, SFields.overlayM]
  | _, .cons o os, .cons v rest => by
    rw [SFields.overlay_cons, SFields.overlayM, SVal.overlay_eq_overlayM o v,
      SFields.overlay_eq_overlayM os rest]

theorem SVec.overlayOn_eq_overlayOnM : {E : Ty} → {n : Nat} → (os : List (SVal E)) →
    (l : SVec E n) → SVec.overlayOn os l = SVec.overlayOnM os l
  | _, _, [], l => by rw [SVec.overlayOn_nil_left, SVec.overlayOnM]
  | _, _, o :: os, .cons v rest => by
    rw [SVec.overlayOn_cons_cons, SVec.overlayOnM, SVal.overlay_eq_overlayM o v,
      SVec.overlayOn_eq_overlayOnM os rest]
  | _, _, _ :: _, .nil => by rw [SVec.overlayOn_nil, SVec.overlayOnM]
end

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
  W E _ := List (SVal E) → Bool
  M U := SMap U → Bool
  prim := fun {p} x w => decide (x = (SVal.view w : p.Denote))
  struct := fun _ ih w => ih (SVal.view w)
  array := fun _ _ _ ie ish w =>
    let x : ArrView _ := SVal.view w
    ie x.elems.toList && ish x.shadow
  fixed := fun _ ie w => ie (SVal.view w : SVec _ _).toList
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
  wnil := fun l => l.isEmpty
  wcons := fun _ _ iv ir l =>
    match l with
    | [] => false
    | x :: xs => iv x && ir xs
  mnil := fun w => (SMap.uncons w).isNone
  mcons := fun k _ _ iv ir w =>
    match SMap.uncons w with
    | some x => decide (k = x.1) && iv x.2.1 && ir x.2.2
    | none => false

def SVal.beq {T : Ty} (v w : SVal T) : Bool := v.fold beqFold w
def SFields.beq {fs : List (Name × Ty)} (x y : SFields fs) : Bool := x.fold beqFold y
def SList.beq {E : Ty} (l l' : SList E) : Bool := l.fold beqFold l'
/-- A vector against a list: the same elements, as many. -/
def SVec.beqL {E : Ty} {n : Nat} (l : SVec E n) (l' : List (SVal E)) : Bool := l.fold beqFold l'
def SMap.beq {U : Ty} (m m' : SMap U) : Bool := m.fold beqFold m'

theorem SVal.beq_prim {p : PrimTy} (x y : p.Denote) :
    (SVal.prim x).beq (.prim y) = decide (x = y) := rfl
theorem SVal.beq_struct {s : Name} (fs gs : SFields (structDef s)) :
    (SVal.struct fs).beq (.struct gs) = fs.beq gs := rfl
theorem SVal.beq_array {E : Ty} {n m : Nat} (e : SVec E n) (sh : SList E) (h : n < 2 ^ 256)
    (e' : SVec E m) (sh' : SList E) (h' : m < 2 ^ 256) :
    (SVal.array e sh h).beq (.array e' sh' h') = (e.beqL e'.toList && sh.beq sh') := rfl
theorem SVal.beq_fixed {E : Ty} {n : Nat} (e e' : SVec E n) :
    (SVal.fixed e).beq (.fixed e') = e.beqL e'.toList := rfl
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
theorem SVec.beqL_nil_nil {E : Ty} : SVec.beqL (E := E) .nil [] = true := rfl
theorem SVec.beqL_nil_cons {E : Ty} (w : SVal E) (rest' : List (SVal E)) :
    SVec.beqL .nil (w :: rest') = false := rfl
theorem SVec.beqL_cons_nil {E : Ty} {n : Nat} (v : SVal E) (rest : SVec E n) :
    SVec.beqL (.cons v rest) [] = false := rfl
theorem SVec.beqL_cons_cons {E : Ty} {n : Nat} (v w : SVal E) (rest : SVec E n)
    (rest' : List (SVal E)) :
    SVec.beqL (.cons v rest) (w :: rest') = (v.beq w && rest.beqL rest') := rfl
theorem SMap.beq_nil_nil {U : Ty} : SMap.beq (U := U) .nil .nil = true := rfl
theorem SMap.beq_nil_cons {U : Ty} (k : Int) (w : SVal U) (rest' : SMap U) :
    SMap.beq .nil (.cons k w rest') = false := rfl
theorem SMap.beq_cons_nil {U : Ty} (k : Int) (v : SVal U) (rest : SMap U) :
    SMap.beq (.cons k v rest) .nil = false := rfl
theorem SMap.beq_cons_cons {U : Ty} (k k' : Int) (v w : SVal U) (rest rest' : SMap U) :
    SMap.beq (.cons k v rest) (.cons k' w rest') = (decide (k = k') && v.beq w && rest.beq rest') :=
  rfl

attribute [irreducible] SVal.beq SFields.beq SList.beq SVec.beqL SMap.beq
attribute [eqns SVal.beq_prim SVal.beq_struct SVal.beq_array SVal.beq_fixed SVal.beq_map]
  SVal.beq
attribute [eqns SFields.beq_nil SFields.beq_cons] SFields.beq
attribute [eqns SList.beq_nil_nil SList.beq_nil_cons SList.beq_cons_nil SList.beq_cons_cons]
  SList.beq
attribute [eqns SVec.beqL_nil_nil SVec.beqL_nil_cons SVec.beqL_cons_nil SVec.beqL_cons_cons]
  SVec.beqL
attribute [eqns SMap.beq_nil_nil SMap.beq_nil_cons SMap.beq_cons_nil SMap.beq_cons_cons] SMap.beq

mutual
theorem SVal.eq_of_beq : {T : Ty} → (v w : SVal T) → v.beq w = true → v = w
  | _, .prim x, .prim y, h => by
    simp only [SVal.beq, decide_eq_true_eq] at h
    rw [h]
  | _, .struct fs, .struct gs, h => by
    simp only [SVal.beq] at h
    rw [SFields.eq_of_beq fs gs h]
  | _, @SVal.array _ n e sh _, @SVal.array _ m e' sh' _, h => by
    simp only [SVal.beq, Bool.and_eq_true] at h
    have hl := SVec.toList_eq_of_beqL e e'.toList h.1
    have hnm : n = m := by rw [← SVec.length_toList e, hl, SVec.length_toList]
    subst hnm
    rw [SVec.eq_of_toList_eq e e' hl, SList.eq_of_beq sh sh' h.2]
  | _, .fixed e, .fixed e', h => by
    simp only [SVal.beq] at h
    rw [SVec.eq_of_toList_eq e e' (SVec.toList_eq_of_beqL e e'.toList h)]
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

theorem SVec.toList_eq_of_beqL : {E : Ty} → {n : Nat} → (l : SVec E n) → (l' : List (SVal E)) →
    l.beqL l' = true → l.toList = l'
  | _, _, .nil, [], _ => by rw [SVec.toList_nil]
  | _, _, .nil, _ :: _, h => by simp only [SVec.beqL, Bool.false_eq_true] at h
  | _, _, .cons _ _, [], h => by simp only [SVec.beqL, Bool.false_eq_true] at h
  | _, _, .cons v rest, w :: rest', h => by
    simp only [SVec.beqL, Bool.and_eq_true] at h
    rw [SVec.toList_cons, SVal.eq_of_beq v w h.1, SVec.toList_eq_of_beqL rest rest' h.2]
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
  | _, .array e sh _ => by
    simp only [SVal.beq, SVec.beqL_self e, SList.beq_self sh, Bool.and_self]
  | _, .fixed e => by simp only [SVal.beq, SVec.beqL_self e]
  | _, .map m d => by simp only [SVal.beq, SMap.beq_self m, SVal.beq_self d, Bool.and_self]

theorem SFields.beq_self : {fs : List (Name × Ty)} → (x : SFields fs) → x.beq x = true
  | _, .nil => by simp only [SFields.beq]
  | _, .cons v rest => by simp only [SFields.beq, SVal.beq_self v, SFields.beq_self rest,
      Bool.and_self]

theorem SList.beq_self : {E : Ty} → (l : SList E) → l.beq l = true
  | _, .nil => by simp only [SList.beq]
  | _, .cons v rest => by simp only [SList.beq, SVal.beq_self v, SList.beq_self rest,
      Bool.and_self]

theorem SVec.beqL_self : {E : Ty} → {n : Nat} → (l : SVec E n) → l.beqL l.toList = true
  | _, _, .nil => by rw [SVec.toList_nil]; simp only [SVec.beqL]
  | _, _, .cons v rest => by
    rw [SVec.toList_cons]
    simp only [SVec.beqL, SVal.beq_self v, SVec.beqL_self rest, Bool.and_self]

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

/-- The slot `push` lands on, and the slots left. -/
def pushSlot (E : Ty) : List (SVal E) → SVal E × List (SVal E)
  | [] => (SVal.dflt E, [])
  | c :: rest => (if E.isPrimitive then SVal.dflt E else c, rest)

/-- A length below `2^256` is a `uint`. -/
theorem lenU_inRange {n : Nat} (h : n < 2 ^ 256) : PrimTy.uint.inRange (n : Int) = true := by
  simp only [PrimTy.inRange, decide_eq_true_eq]
  omega

/-- A length as a `uint`. -/
def lenU (n : Nat) (h : n < 2 ^ 256) : PrimTy.uint.Denote :=
  (⟨n, lenU_inRange h⟩ : {n : Int // PrimTy.uint.inRange n = true})

/-- One more element, below the bound. -/
theorem SVec.snoc_lt_bound {E : Ty} {n : Nat} (e : SVec E n) (x : SVal E) (h : n + 1 < 2 ^ 256) :
    (e.toList ++ [x]).length < 2 ^ 256 := by
  rw [List.length_append, SVec.length_toList, List.length_singleton]; exact h

/-- One element fewer, below the bound. -/
theorem SVec.dropLast_lt_bound {E : Ty} {n : Nat} (e : SVec E n) (h : n < 2 ^ 256) :
    e.toList.dropLast.length < 2 ^ 256 := by
  rw [List.length_dropLast, SVec.length_toList]; omega

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


end SRef

namespace Storage

variable {C : Contract}


/-- The storage a contract starts with: every state variable at its
default. -/
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
        let w : ArrView _ := SVal.view v
        if 0 ≤ i ∧ i.toNat < w.n then some () else none)
      (fun {_} {n} _ => if 0 ≤ i ∧ i.toNat < n then some () else none))

/-- `b[i]`'s index in bounds where the program takes it (`State.checkIndex`):
a mapping takes every key, an array an index below its live length. -/
def checkIndex {R : RefTy} {k : PrimTy} {V : Ty} (st : Storage C) (r : SRef C (.ref R))
    (it : IndexTy R k V) (i : Int) : Option Unit := do
  inBounds it i (← st.find r)

/-- The live length of a dynamic array (`arrayLen`), a `uint`: it is below
`2^256`. -/
def len {E : Ty} (st : Storage C) (r : SRef C (.ref (.array E))) :
    Option PrimTy.uint.Denote := do
  let w : ArrView E := SVal.view (← st.find r)
  some (lenU w.n w.hn)

/-- The array at `r` has `2^256 - 1` live elements: one more is past a
`uint` length.  The typed run treats a push there as out of gas
(`TRun.push`, `docs/solc-alignment.md`). -/
def full {E : Ty} (st : Storage C) (r : SRef C (.ref (.array E))) : Bool :=
  match st.find r with
  | some v => !decide ((SVal.view v : ArrView E).n + 1 < 2 ^ 256)
  | none => false

/-- `b.push(…)` (`pushAt`): the element `val` makes of the slot it lands on,
appended; `none` past the bound (`full`). -/
def push {E : Ty} (st : Storage C) (r : SRef C (.ref (.array E)))
    (val : SVal E → Option (SVal E)) : Option (Storage C) := do
  let w : ArrView E := SVal.view (← st.find r)
  let (slot, sh') := pushSlot E w.shadow.toList
  let x ← val slot
  if h : w.n + 1 < 2 ^ 256 then
    st.save r (.array (SVec.ofList (w.elems.toList ++ [x])) (.ofList sh')
      (SVec.snoc_lt_bound w.elems x h))
  else none

/-- `b.push()` as a place (`pushPlaceAt`): the slot appended, and its index. -/
def pushPlace {E : Ty} (st : Storage C) (r : SRef C (.ref (.array E))) :
    Option (Storage C × Nat) := do
  let w : ArrView E := SVal.view (← st.find r)
  let (slot, sh') := pushSlot E w.shadow.toList
  if h : w.n + 1 < 2 ^ 256 then
    let st' ← st.save r (.array (SVec.ofList (w.elems.toList ++ [slot])) (.ofList sh')
      (SVec.snoc_lt_bound w.elems slot h))
    some (st', w.n)
  else none

/-- `b.pop()` (`popAt`): the last element cleared into the slots past the
end, or moved there as it is when `keep`; an empty array reverts. -/
def pop {E : Ty} (st : Storage C) (keep : Bool) (r : SRef C (.ref (.array E))) :
    Option (Storage C) := do
  let w : ArrView E := SVal.view (← st.find r)
  match w.elems.toList.reverse with
  | [] => none
  | last :: _ =>
    st.save r (.array (SVec.ofList w.elems.toList.dropLast)
      (.ofList ((if keep then last else last.defaultOf) :: w.shadow.toList))
      (SVec.dropLast_lt_bound w.elems w.hn))

/-- `delete b` on storage: its value reset in place (`SVal.defaultOf`). -/
def delete {T : Ty} (st : Storage C) (r : SRef C T) : Option (Storage C) := do
  st.save r (← st.find r).defaultOf

/-- An assignment's write (`State.writeStorage`): a word stored, a struct or
an array copied over what is there. -/
def write {T : Ty} (st : Storage C) (r : SRef C T) (new : SVal T) : Option (Storage C) :=
  if new.isPrim then st.save r new
  else do st.save r ((← st.find r).overlay new)

end Storage

/-! ## A save read back

`findOnSave` and `findOnSaveFrame` on the compiled forms: a save reads back
at its path (`SVal.findM_saveM`), and leaves a path that parts from it
(`Path.Diverges`, `SVal.findM_saveM_diverges`). -/

private theorem lookupBy_setBy_self' {κ α : Type} [DecidableEq κ] (k : κ) (v : α)
    (l : List (κ × α)) : lookupBy k (setBy k v l) = some v := by
  induction l with
  | nil => simp only [setBy, lookupBy, ↓reduceIte]
  | cons hd tl ih =>
    obtain ⟨k', v'⟩ := hd
    by_cases h : k = k' <;> simp only [h, setBy, ↓reduceIte, lookupBy, ih]

private theorem lookupBy_setBy_ne' {κ α : Type} [DecidableEq κ] {k k' : κ} (h : k ≠ k') (v : α)
    (l : List (κ × α)) : lookupBy k (setBy k' v l) = lookupBy k l := by
  induction l with
  | nil => simp only [setBy, lookupBy, h, ↓reduceIte]
  | cons hd tl ih =>
    obtain ⟨k'', v''⟩ := hd
    by_cases h₂ : k' = k''
    · subst h₂; simp only [setBy, ↓reduceIte, lookupBy, h]
    · simp only [setBy, h₂, ↓reduceIte, lookupBy, ih]

theorem SFields.get_set_same {f : Name} : {fs : List (Name × Ty)} → {T : Ty} → (x : SFields fs) →
    (h : lookupBy f fs = some T) → (y : SVal T) → (x.set h y).get h = y
  | [], _, .nil, h, _ => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, T, .cons v rest, h, y => by
    rw [SFields.set_cons]
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      simp only [e, dite_true, SFields.get_cons]
    · simp only [e, dite_false, SFields.get_cons]
      exact SFields.get_set_same rest _ y

theorem SFields.get_set_ne {f g : Name} : {fs : List (Name × Ty)} → {T U : Ty} → (x : SFields fs) →
    (h : lookupBy f fs = some T) → (hg : lookupBy g fs = some U) → f ≠ g → (y : SVal T) →
    (x.set h y).get hg = x.get hg
  | [], _, _, .nil, h, _, _, _ => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, T, U, .cons v rest, h, hg, hfg, y => by
    rw [SFields.set_cons]
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      have eg : ¬ g = f' := fun h' => hfg (e.trans h'.symm)
      simp only [e, dite_true, SFields.get_cons, eg, dite_false]
    · simp only [e, dite_false, SFields.get_cons]
      by_cases eg : g = f'
      · simp only [eg, dite_true]
      · simp only [eg, dite_false]
        exact SFields.get_set_ne rest _ _ hfg y

theorem SVal.findM_saveM : {T U : Ty} → (x : SVal T) → (p : Path T U) → (v : SVal U) →
    {x' : SVal T} → x.saveM p v = some x' → x'.findM p = some v
  | _, _, x, .nil, v, x', h => by
    cases x <;> (simp only [SVal.saveM, Option.some.injEq] at h; subst h; cases v <;> rfl)
  | _, _, .struct fs, .field hf p, v, x', h => by
    simp only [SVal.saveM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨y, hy, rfl⟩ := h
    simp only [SVal.findM, SFields.get_set_same]
    exact SVal.findM_saveM _ p v hy
  | _, _, .array e sh hn, .at i p, v, x', h => by
    simp only [SVal.saveM] at h
    split at h
    · rename_i hi
      split at h
      · rename_i x hx
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨y, hy, rfl⟩ := h
        have hl : i.toNat < (e.toList ++ sh.toList).length := (List.getElem?_eq_some_iff.mp hx).1
        simp only [SVal.findM, hi, if_true, SVec.toList_ofList, SList.toList_ofList,
          List.take_append_drop, List.getElem?_set_self hl]
        exact SVal.findM_saveM _ p v hy
      · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h
  | _, _, .fixed e, .atF i p, v, x', h => by
    simp only [SVal.saveM] at h
    split at h
    · rename_i hi
      split at h
      · rename_i x hx
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨y, hy, rfl⟩ := h
        have hl : i.toNat < e.toList.length := (List.getElem?_eq_some_iff.mp hx).1
        simp only [SVal.findM, hi, if_true, SVec.toList_set, List.getElem?_set_self hl]
        exact SVal.findM_saveM _ p v hy
      · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h
  | _, _, .map m d, .key k p, v, x', h => by
    simp only [SVal.saveM] at h
    split at h <;>
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨y, hy, rfl⟩ := h
      simp only [SVal.findM, SMap.toList_ofList, lookupBy_setBy_self']
      exact SVal.findM_saveM _ p v hy

/-- Two paths from one value that part: at two members, two slots or two
keys, somewhere along them (the `a1 ≠ a2` of solkey's `selectOnSaveCons`,
across the types the two paths reach). -/
inductive Path.Diverges : {T U W : Ty} → Path T U → Path T W → Prop
  | field {s f f' : Name} {T T' U W : Ty} (h : lookupBy f (structDef s) = some T)
      (h' : lookupBy f' (structDef s) = some T') (p : Path T U) (q : Path T' W) (hne : f ≠ f') :
      Diverges (.field h p) (.field h' q)
  | fieldIn {s f : Name} {T U W : Ty} (h : lookupBy f (structDef s) = some T) {p : Path T U}
      {q : Path T W} : Diverges p q → Diverges (.field h p) (.field h q)
  | at {E U W : Ty} {i j : Int} (p : Path E U) (q : Path E W) (hne : i ≠ j) :
      Diverges (.at i p) (.at j q)
  | atIn {E U W : Ty} (i : Int) {p : Path E U} {q : Path E W} :
      Diverges p q → Diverges (.at i p) (.at i q)
  | atF {E U W : Ty} {n : Nat} {i j : Int} (p : Path E U) (q : Path E W) (hne : i ≠ j) :
      Diverges (.atF (n := n) i p) (.atF j q)
  | atFIn {E U W : Ty} {n : Nat} (i : Int) {p : Path E U} {q : Path E W} :
      Diverges p q → Diverges (.atF (n := n) i p) (.atF i q)
  | key {K V U W : Ty} {k k' : Int} (p : Path V U) (q : Path V W) (hne : k ≠ k') :
      Diverges (.key (K := K) k p) (.key k' q)
  | keyIn {K V U W : Ty} (k : Int) {p : Path V U} {q : Path V W} :
      Diverges p q → Diverges (.key (K := K) k p) (.key k q)

theorem SVal.findM_saveM_diverges {T U W : Ty} {p : Path T U} {q : Path T W}
    (hd : Path.Diverges p q) : (x : SVal T) → (v : SVal U) → {x' : SVal T} →
    x.saveM p v = some x' → x'.findM q = x.findM q := by
  induction hd with
  | field h h' p q hne =>
    intro x v x' hs
    cases x with
    | struct fs =>
      simp only [SVal.saveM, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at hs
      obtain ⟨y, _, rfl⟩ := hs
      simp only [SVal.findM, SFields.get_set_ne fs h h' hne]
  | fieldIn h _ ih =>
    intro x v x' hs
    cases x with
    | struct fs =>
      simp only [SVal.saveM, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at hs
      obtain ⟨y, hy, rfl⟩ := hs
      simp only [SVal.findM, SFields.get_set_same]
      exact ih _ v hy
  | @«at» E U W i j p q hne =>
    intro x v x' hs
    cases x with
    | array e sh hn =>
      simp only [SVal.saveM] at hs
      split at hs
      · rename_i hi
        split at hs
        · rename_i x0 hx
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hs
          obtain ⟨y, _, rfl⟩ := hs
          simp only [SVal.findM, SVec.toList_ofList, SList.toList_ofList, List.take_append_drop]
          by_cases hj : 0 ≤ j
          · have hn' : i.toNat ≠ j.toNat := by omega
            simp only [hj, if_true, List.getElem?_set_ne hn']
          · simp only [hj, if_false]
        · simp only [reduceCtorEq] at hs
      · simp only [reduceCtorEq] at hs
  | atIn i _ ih =>
    intro x v x' hs
    cases x with
    | array e sh hn =>
      simp only [SVal.saveM] at hs
      split at hs
      · rename_i hi
        split at hs
        · rename_i x0 hx
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hs
          obtain ⟨y, hy, rfl⟩ := hs
          have hl : i.toNat < (e.toList ++ sh.toList).length :=
            (List.getElem?_eq_some_iff.mp hx).1
          simp only [SVal.findM, hi, if_true, SVec.toList_ofList, SList.toList_ofList,
            List.take_append_drop, List.getElem?_set_self hl, hx]
          exact ih _ v hy
        · simp only [reduceCtorEq] at hs
      · simp only [reduceCtorEq] at hs
  | @atF E U W n i j p q hne =>
    intro x v x' hs
    cases x with
    | fixed e =>
      simp only [SVal.saveM] at hs
      split at hs
      · rename_i hi
        split at hs
        · rename_i x0 hx
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hs
          obtain ⟨y, _, rfl⟩ := hs
          simp only [SVal.findM, SVec.toList_set]
          by_cases hj : 0 ≤ j
          · have hn' : i.toNat ≠ j.toNat := by omega
            simp only [hj, if_true, List.getElem?_set_ne hn']
          · simp only [hj, if_false]
        · simp only [reduceCtorEq] at hs
      · simp only [reduceCtorEq] at hs
  | atFIn i _ ih =>
    intro x v x' hs
    cases x with
    | fixed e =>
      simp only [SVal.saveM] at hs
      split at hs
      · rename_i hi
        split at hs
        · rename_i x0 hx
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hs
          obtain ⟨y, hy, rfl⟩ := hs
          have hl : i.toNat < e.toList.length := (List.getElem?_eq_some_iff.mp hx).1
          simp only [SVal.findM, hi, if_true, SVec.toList_set, List.getElem?_set_self hl, hx]
          exact ih _ v hy
        · simp only [reduceCtorEq] at hs
      · simp only [reduceCtorEq] at hs
  | @key K V U W k k' p q hne =>
    intro x v x' hs
    cases x with
    | map m d =>
      simp only [SVal.saveM] at hs
      split at hs <;>
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hs
        obtain ⟨y, _, rfl⟩ := hs
        simp only [SVal.findM, SMap.toList_ofList,
          lookupBy_setBy_ne' (Ne.symm hne)]
  | keyIn k _ ih =>
    intro x v x' hs
    cases x with
    | map m d =>
      simp only [SVal.saveM] at hs
      split at hs
      · rename_i x0 hx
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hs
        obtain ⟨y, hy, rfl⟩ := hs
        simp only [SVal.findM, SMap.toList_ofList, lookupBy_setBy_self', hx]
        exact ih _ v hy
      · rename_i hx
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hs
        obtain ⟨y, hy, rfl⟩ := hs
        simp only [SVal.findM, SMap.toList_ofList, lookupBy_setBy_self', hx]
        exact ih _ v hy

/-! ### The recursor forms are their `match` twins

`SVal.find`, `findLive` and `save` are written with `Path.rec` for the
kernel; these equations are their `match` twins' arms, by `rfl`, and the
twins agree. -/

namespace SVal

theorem find_nil {T : Ty} (v : SVal T) : v.find .nil = some v := rfl

theorem find_field {s f : Name} {T U : Ty} (fs : SFields (structDef s))
    (h : lookupBy f (structDef s) = some T) (p : Path T U) :
    (SVal.struct fs).find (.field h p) = (fs.get h).find p := rfl

theorem find_at {E U : Ty} {n : Nat} (e : SVec E n) (sh : SList E) (h : n < 2 ^ 256) (i : Int)
    (p : Path E U) :
    (SVal.array e sh h).find (.at i p) =
      if 0 ≤ i then
        match (e.toList ++ sh.toList)[i.toNat]? with
        | some x => x.find p
        | none => none
      else none := rfl

theorem find_atF {E U : Ty} {n : Nat} (e : SVec E n) (i : Int) (p : Path E U) :
    (SVal.fixed e).find (.atF i p) =
      if 0 ≤ i then
        match e.toList[i.toNat]? with
        | some x => x.find p
        | none => none
      else none := rfl

theorem find_key {K V U : Ty} (m : SMap V) (d : SVal V) (k : Int) (p : Path V U) :
    (SVal.map (K := K) m d).find (.key k p) =
      match lookupBy k m.toList with
      | some x => x.find p
      | none => d.find p := rfl

theorem find_eq_findM : {T U : Ty} → (v : SVal T) → (p : Path T U) → v.find p = v.findM p
  | _, _, v, .nil => by cases v <;> rfl
  | _, _, .struct fs, .field h p => by
    rw [find_field, find_eq_findM _ p]
    simp only [findM]
  | _, _, .array e sh _, .at i p => by
    rw [find_at]
    simp only [find_eq_findM _ p, findM]
  | _, _, .fixed e, .atF i p => by
    rw [find_atF]
    simp only [find_eq_findM _ p, findM]
  | _, _, .map m d, .key k p => by
    rw [find_key]
    simp only [find_eq_findM _ p, findM]

theorem findLive_eq_findLiveM : {T U : Ty} → (v : SVal T) → (p : Path T U) →
    v.findLive p = v.findLiveM p
  | _, _, v, .nil => by cases v <;> rfl
  | _, _, .struct fs, .field h p => by
    show (fs.get h).findLive p = _
    rw [findLive_eq_findLiveM _ p]
    simp only [findLiveM]
  | _, _, .array e sh _, .at i p => by
    show (if 0 ≤ i then
        match e.toList[i.toNat]? with
        | some x => x.findLive p
        | none => none
      else none) = _
    simp only [findLive_eq_findLiveM _ p, findLiveM]
  | _, _, .fixed e, .atF i p => by
    show (if 0 ≤ i then
        match e.toList[i.toNat]? with
        | some x => x.findLive p
        | none => none
      else none) = _
    simp only [findLive_eq_findLiveM _ p, findLiveM]
  | _, _, .map m d, .key k p => by
    show (match lookupBy k m.toList with
      | some x => x.findLive p
      | none => d.findLive p) = _
    simp only [findLive_eq_findLiveM _ p, findLiveM]

theorem save_eq_saveM : {T U : Ty} → (v : SVal T) → (p : Path T U) → (new : SVal U) →
    v.save p new = v.saveM p new
  | _, _, v, .nil, _ => by cases v <;> rfl
  | _, _, @SVal.struct s fs, .field h p, new => by
    show (do
        let x ← (fs.get h).save p new
        some (SVal.struct (fs.set h x)) : Option (SVal (.ref (.struct s)))) = _
    simp only [save_eq_saveM _ p, saveM]
  | _, _, @SVal.array E n e sh h, .at i p, new => by
    show (if 0 ≤ i then
        match (e.toList ++ sh.toList)[i.toNat]? with
        | some x => do
          let x' ← x.save p new
          let slots := (e.toList ++ sh.toList).set i.toNat x'
          some (SVal.array (SVec.ofList (slots.take n)) (.ofList (slots.drop n))
            (SVal.take_lt_bound slots h))
        | none => none
      else none : Option (SVal (.ref (.array E)))) = _
    simp only [save_eq_saveM _ p, saveM]
  | _, _, @SVal.fixed E n e, .atF i p, new => by
    show (if 0 ≤ i then
        match e.toList[i.toNat]? with
        | some x => do
          let x' ← x.save p new
          some (SVal.fixed (e.set i.toNat x'))
        | none => none
      else none : Option (SVal (.ref (.fixed E n)))) = _
    simp only [save_eq_saveM _ p, saveM]
  | _, _, @SVal.map K V m d, .key k p, new => by
    show (match lookupBy k m.toList with
      | some x => do
        let x' ← x.save p new
        some (SVal.map (.ofList (setBy k x' m.toList)) d)
      | none => do
        let x' ← d.save p new
        some (SVal.map (.ofList (setBy k x' m.toList)) d) : Option (SVal (.ref (.mapping K V)))) = _
    simp only [save_eq_saveM _ p, saveM]

end SVal

/-- A save that lands reads back (`findOnSave` below a root). -/
theorem SVal.find_save_same {T U : Ty} (x : SVal T) (p : Path T U) (v : SVal U)
    {x' : SVal T} (h : x.save p v = some x') : x'.find p = some v := by
  rw [SVal.save_eq_saveM] at h
  rw [SVal.find_eq_findM]
  exact SVal.findM_saveM x p v h

/-- The members of a struct without mappings are without mappings too. -/
theorem mapFree_structDef : ∀ s ∈ mapFreeStructs, ∀ fT ∈ structDef s, fT.2.mapFree = true := by
  decide

/-! ## The stores

The ported contracts' stores, typed: each a named constant, so a proof about
one unfolds it only where it reads it. -/

namespace Storage

/-- `StandardExample`'s storage at deployment. -/
def standardExample : Storage StandardExample := Storage.init StandardExample

/-- `TestSuite`'s storage at deployment. -/
def testSuite : Storage TestSuite := Storage.init TestSuite

/-- Storage equality is decided by the kernel (`SFields.beq`): a store is
itself, and not itself with `alice.age` saved as `7`. -/
example : (testSuite = testSuite) ∧
    (testSuite.save ⟨"alice", rfl, .field (f := "age") rfl .nil⟩
      (.prim (⟨7, rfl⟩ : {n : Int // PrimTy.uint.inRange n = true}))).map
      (fun st => decide (st = testSuite)) = some false := by
  decide +kernel

end Storage

end Solidity
