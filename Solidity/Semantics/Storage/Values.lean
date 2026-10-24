import Solidity.Semantics.Value
import Solidity.Eqns

/-!
# Typed storage: values and paths

Storage values, folds and views, lists, vectors and maps as Lean lists,
members by name, defaults, paths.

A piece of `Semantics/Storage.lean`, whose docstring describes the whole.
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
  | map {K : PrimTy} {V : Ty} (entries : SMap K V) (dflt : SVal V) : SVal (.ref (.mapping K V))

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

/-- A mapping's entries, by key: each key a value of the key type. -/
inductive SMap : PrimTy → Ty → Type where
  | nil {K : PrimTy} {V : Ty} : SMap K V
  | cons {K : PrimTy} {V : Ty} (k : K.Denote) (v : SVal V) (rest : SMap K V) : SMap K V
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
  M : PrimTy → Ty → Type
  prim : {p : PrimTy} → p.Denote → V (.prim p)
  struct : {s : Name} → SFields (structDef s) → F (structDef s) → V (.ref (.struct s))
  array : {E : Ty} → {n : Nat} → SVec E n → SList E → n < 2 ^ 256 → W E n → L E →
    V (.ref (.array E))
  fixed : {E : Ty} → {n : Nat} → SVec E n → W E n → V (.ref (.fixed E n))
  map : {K : PrimTy} → {U : Ty} → SMap K U → SVal U → M K U → V U → V (.ref (.mapping K U))
  fnil : F []
  fcons : {f : Name} → {T : Ty} → {fs : List (Name × Ty)} → SVal T → SFields fs → V T → F fs →
    F ((f, T) :: fs)
  lnil : {E : Ty} → L E
  lcons : {E : Ty} → SVal E → SList E → V E → L E → L E
  wnil : {E : Ty} → W E 0
  wcons : {E : Ty} → {n : Nat} → SVal E → SVec E n → V E → W E n → W E (n + 1)
  mnil : {K : PrimTy} → {U : Ty} → M K U
  mcons : {K : PrimTy} → {U : Ty} → K.Denote → SVal U → SMap K U → V U → M K U → M K U

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

def SMap.foldM (a : Fold) : {K : PrimTy} → {U : Ty} → SMap K U → a.M K U
  | _, _, .nil => a.mnil
  | _, _, .cons k v rest => a.mcons k v rest (SVal.foldM a v) (SMap.foldM a rest)
end

/-- A fold of a value, by the recursor. -/
@[implemented_by SVal.foldM]
def SVal.fold (a : Fold) {T : Ty} (v : SVal T) : a.V T :=
  @SVal.rec (fun T _ => a.V T) (fun fs _ => a.F fs) (fun E _ => a.L E) (fun E n _ => a.W E n)
    (fun K U _ => a.M K U) a.prim a.struct a.array a.fixed a.map a.fnil a.fcons a.lnil a.lcons
    a.wnil a.wcons a.mnil a.mcons T v

@[implemented_by SFields.foldM]
def SFields.fold (a : Fold) {fs : List (Name × Ty)} (x : SFields fs) : a.F fs :=
  @SFields.rec (fun T _ => a.V T) (fun fs _ => a.F fs) (fun E _ => a.L E) (fun E n _ => a.W E n)
    (fun K U _ => a.M K U) a.prim a.struct a.array a.fixed a.map a.fnil a.fcons a.lnil a.lcons
    a.wnil a.wcons a.mnil a.mcons fs x

@[implemented_by SList.foldM]
def SList.fold (a : Fold) {E : Ty} (l : SList E) : a.L E :=
  @SList.rec (fun T _ => a.V T) (fun fs _ => a.F fs) (fun E _ => a.L E) (fun E n _ => a.W E n)
    (fun K U _ => a.M K U) a.prim a.struct a.array a.fixed a.map a.fnil a.fcons a.lnil a.lcons
    a.wnil a.wcons a.mnil a.mcons E l

@[implemented_by SVec.foldM]
def SVec.fold (a : Fold) {E : Ty} {n : Nat} (l : SVec E n) : a.W E n :=
  @SVec.rec (fun T _ => a.V T) (fun fs _ => a.F fs) (fun E _ => a.L E) (fun E n _ => a.W E n)
    (fun K U _ => a.M K U) a.prim a.struct a.array a.fixed a.map a.fnil a.fcons a.lnil a.lcons
    a.wnil a.wcons a.mnil a.mcons E n l

@[implemented_by SMap.foldM]
def SMap.fold (a : Fold) {K : PrimTy} {U : Ty} (m : SMap K U) : a.M K U :=
  @SMap.rec (fun T _ => a.V T) (fun fs _ => a.F fs) (fun E _ => a.L E) (fun E n _ => a.W E n)
    (fun K U _ => a.M K U) a.prim a.struct a.array a.fixed a.map a.fnil a.fcons a.lnil a.lcons
    a.wnil a.wcons a.mnil a.mcons K U m

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

theorem SMap.fold_eq_foldM (a : Fold) : {K : PrimTy} → {U : Ty} → (m : SMap K U) →
    m.fold a = m.foldM a
  | _, _, .nil => rfl
  | _, _, .cons k v rest => by
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
  | .ref (.mapping K V) => SMap K V × SVal V

/-- A value's contents, at the type its type computes. -/
def SVal.view {T : Ty} (v : SVal T) : Shape T :=
  @SVal.casesOn (fun T _ => Shape T) T v (fun {_} x => x) (fun {_} fs => fs)
    (fun {_} {_} e sh h => ⟨e, sh, h⟩) (fun {_} {_} e => e) (fun {_} {_} m d => (m, d))

theorem SVal.view_prim {p : PrimTy} (x : p.Denote) : (SVal.prim x).view = x := rfl
theorem SVal.view_struct {s : Name} (fs : SFields (structDef s)) : (SVal.struct fs).view = fs := rfl
theorem SVal.view_array {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E) (h : n < 2 ^ 256) :
    (SVal.array e sh h).view = ⟨e, sh, h⟩ := rfl

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
def SMap.uncons {K : PrimTy} {U : Ty} (m : SMap K U) : Option (K.Denote × SVal U × SMap K U) :=
  @SMap.casesOn (fun K U _ => Option (K.Denote × SVal U × SMap K U)) K U m none
    (fun {_} {_} k v rest => some (k, v, rest))


/-! ## Lists, vectors and maps as Lean lists -/

/-- The values of lists, vectors and mappings. -/
def toListFold : Fold where
  V _ := Unit
  F _ := Unit
  L E := List (SVal E)
  W E _ := List (SVal E)
  M K U := List (K.Denote × SVal U)
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
attribute [sol_eqns toList_nil toList_cons] toList

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
attribute [sol_eqns toList_nil toList_cons] toList

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
  M _ _ := Unit
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
attribute [sol_eqns set_nil set_cons_zero set_cons_succ] set

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
def toListM {K : PrimTy} {V : Ty} : SMap K V → List (K.Denote × SVal V)
  | .nil => []
  | .cons k v rest => (k, v) :: rest.toListM

@[implemented_by toListM]
def toList {K : PrimTy} {V : Ty} (m : SMap K V) : List (K.Denote × SVal V) := m.fold toListFold

theorem toList_nil {K : PrimTy} {V : Ty} : (SMap.nil (K := K) (V := V)).toList = [] := rfl
theorem toList_cons {K : PrimTy} {V : Ty} (k : K.Denote) (v : SVal V) (rest : SMap K V) :
    (SMap.cons k v rest).toList = (k, v) :: rest.toList := rfl

attribute [irreducible] toList
attribute [sol_eqns toList_nil toList_cons] toList

theorem toList_eq_toListM {K : PrimTy} {V : Ty} : (m : SMap K V) → m.toList = m.toListM
  | .nil => by rw [toList_nil, toListM]
  | .cons k v rest => by rw [toList_cons, toListM, toList_eq_toListM rest]

def ofList {K : PrimTy} {V : Ty} : List (K.Denote × SVal V) → SMap K V
  | [] => .nil
  | (k, v) :: rest => .cons k v (ofList rest)

@[simp] theorem toList_ofList {K : PrimTy} {V : Ty} :
    (l : List (K.Denote × SVal V)) → (ofList l).toList = l
  | [] => by rw [ofList, toList_nil]
  | (k, v) :: rest => by rw [ofList, toList_cons, toList_ofList rest]

theorem ofList_toList {K : PrimTy} {V : Ty} : (m : SMap K V) → ofList m.toList = m
  | .nil => by rw [toList_nil]; rfl
  | .cons k v rest => by rw [toList_cons, ofList, ofList_toList rest]

/-- The entries at the words their keys hash to (`PrimTy.key`): what the
EVM's slots observe. -/
def hashed {K : PrimTy} {V : Ty} (m : SMap K V) : List (Int × SVal V) :=
  m.toList.map fun e => (PrimTy.key e.1, e.2)

theorem lookupBy_hashed_aux {K : PrimTy} {V : Ty} (k : K.Denote) :
    (l : List (K.Denote × SVal V)) →
      lookupBy (PrimTy.key k) (l.map fun e => (PrimTy.key e.1, e.2)) = lookupBy k l
  | [] => rfl
  | (k', v) :: rest => by
    simp only [List.map_cons, lookupBy]
    by_cases h : k = k'
    · subst h; simp only [↓reduceIte]
    · have h' : PrimTy.key k ≠ PrimTy.key k' := fun e => h (PrimTy.key_inj e)
      simp only [h, h', ↓reduceIte, lookupBy_hashed_aux k rest]

/-- A key's entry is the one at its hash. -/
theorem lookupBy_hashed {K : PrimTy} {V : Ty} (m : SMap K V) (k : K.Denote) :
    lookupBy (PrimTy.key k) m.hashed = lookupBy k m.toList :=
  lookupBy_hashed_aux k m.toList

theorem hashed_ofList_setBy {K : PrimTy} {V : Ty} (k : K.Denote) (x : SVal V) :
    (l : List (K.Denote × SVal V)) →
      (ofList (setBy k x l)).hashed = setBy (PrimTy.key k) x ((ofList l).hashed)
  | [] => by simp only [setBy, hashed, toList_ofList, List.map_cons, List.map_nil]
  | (k', v) :: rest => by
    have ih := hashed_ofList_setBy k x rest
    simp only [hashed, toList_ofList] at ih ⊢
    by_cases h : k = k'
    · subst h; simp only [setBy, ↓reduceIte, List.map_cons]
    · have h' : PrimTy.key k ≠ PrimTy.key k' := fun e => h (PrimTy.key_inj e)
      simp only [setBy, h, h', ↓reduceIte, List.map_cons, ih]


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
    (fun _ _ => Unit) (fun _ _ _ => Unit) (fun _ _ _ => Unit)
    (fun {_} _ => ()) (fun {_} _ _ => ()) (fun {_} {_} _ _ _ _ _ => ()) (fun {_} {_} _ _ => ())
    (fun {_} {_} _ _ _ _ => ())
    (fun _ h => absurd h (by simp only [lookupBy, reduceCtorEq, not_false_eq_true]))
    (fun {f'} {_} {_} v _ _ ih _ h =>
      if e : f = f' then lookupBy_cons_pos e h ▸ v else ih _ (lookupBy_cons_neg e h))
    (fun {_} => ()) (fun {_} _ _ _ _ => ()) (fun {_} => ()) (fun {_} {_} _ _ _ _ => ())
    (fun {_} {_} => ()) (fun {_} {_} _ _ _ _ _ => ()) fs x T h

/-- The first member named `f` replaced.  By the recursor; `setM` is its
compiled form. -/
@[implemented_by setM]
def set {f : Name} {fs : List (Name × Ty)} {T : Ty} (x : SFields fs)
    (h : lookupBy f fs = some T) (y : SVal T) : SFields fs :=
  @SFields.rec (fun _ _ => Unit) (fun fs _ => ∀ T, lookupBy f fs = some T → SVal T → SFields fs)
    (fun _ _ => Unit) (fun _ _ _ => Unit) (fun _ _ _ => Unit)
    (fun {_} _ => ()) (fun {_} _ _ => ()) (fun {_} {_} _ _ _ _ _ => ()) (fun {_} {_} _ _ => ())
    (fun {_} {_} _ _ _ _ => ())
    (fun _ _ _ => .nil)
    (fun {f'} {_} {_} v rest _ ih _ h y =>
      if e : f = f' then .cons ((lookupBy_cons_pos e h).symm ▸ y) rest
      else .cons v (ih _ (lookupBy_cons_neg e h) y))
    (fun {_} => ()) (fun {_} _ _ _ _ => ()) (fun {_} => ()) (fun {_} {_} _ _ _ _ => ())
    (fun {_} {_} => ()) (fun {_} {_} _ _ _ _ _ => ()) fs x T h y

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

theorem get_eq_getM {f : Name} : {fs : List (Name × Ty)} → {T : Ty} → (st : SFields fs) →
    (h : lookupBy f fs = some T) → st.get h = st.getM h
  | _, _, .nil, h => by simp only [lookupBy, reduceCtorEq] at h
  | _, _, @SFields.cons f' T' _ v rest, h => by
    rw [get_cons]
    by_cases e : f = f'
    · simp only [e, ↓reduceDIte, getM]
    · simp only [e, ↓reduceDIte, getM, get_eq_getM rest]

theorem set_eq_setM {f : Name} : {fs : List (Name × Ty)} → {T : Ty} → (st : SFields fs) →
    (h : lookupBy f fs = some T) → (x : SVal T) → st.set h x = st.setM h x
  | _, _, .nil, _, _ => rfl
  | _, _, @SFields.cons f' T' _ v rest, h, x => by
    rw [set_cons]
    by_cases e : f = f'
    · simp only [e, ↓reduceDIte, setM]
    · simp only [e, ↓reduceDIte, setM, set_eq_setM rest]

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
most `structRankCap`), so the kernel computes the fuel of `SVal.dflt` without matching a
string: `tyRank` itself costs a `structRank` lookup per default. -/
def rankBound : Ty → Nat
  | .prim _ => 0
  | .ref (.struct _) => Semantics.structRankCap
  | .ref (.array E) => rankBound E
  | .ref (.fixed E _) => rankBound E + 1
  | .ref (.mapping _ V) => rankBound V

theorem structRank_le_cap (s : Name) : structRank s ≤ Semantics.structRankCap := by
  unfold structRank
  split <;> first | decide | exact Nat.min_le_right _ _

theorem tyRank_le_rankBound : (T : Ty) → tyRank T ≤ rankBound T
  | .prim _ => Nat.le_refl _
  | .ref (.struct s) => structRank_le_cap s
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
  | at {E U : Ty} (i : PrimTy.uint.Denote) (p : Path E U) : Path (.ref (.array E)) U
  | atF {E U : Ty} {n : Nat} (i : PrimTy.uint.Denote) (p : Path E U) : Path (.ref (.fixed E n)) U
  | key {K : PrimTy} {V U : Ty} (k : K.Denote) (p : Path V U) : Path (.ref (.mapping K V)) U

/-- One segment knows the type it leaves and the type it reaches.
A field carries its lookup proof; array and mapping steps cannot be exchanged. -/
inductive Semantics.Seg : Ty → Ty → Type where
  | field {s f : Name} {T : Ty} (h : lookupBy f (structDef s) = some T) :
      Seg (.ref (.struct s)) T
  | at {E : Ty} (i : PrimTy.uint.Denote) : Seg (.ref (.array E)) E
  | atF {E : Ty} {n : Nat} (i : PrimTy.uint.Denote) : Seg (.ref (.fixed E n)) E
  | key {K : PrimTy} {V : Ty} (k : K.Denote) : Seg (.ref (.mapping K V)) V

/-- A sequence composes only when adjacent segment types agree. -/
inductive Semantics.Segs : Ty → Ty → Type where
  | nil {T : Ty} : Segs T T
  | cons {T U V : Ty} (head : Seg T U) (tail : Segs U V) : Segs T V

/-- The comparable label of a typed segment. Labels support location comparison and schema analysis; they cannot
be followed to read or write storage. -/
def Semantics.Seg.label : {T U : Ty} → Seg T U → Selector
  | _, _, @Seg.field _ f _ _ => .field f
  | _, _, .at i => .idx i
  | _, _, .atF i => .idx i
  | _, _, @Seg.key K _ k => .key ⟨K, k⟩

/-- The comparison observations of a typed segment sequence. -/
def Semantics.Segs.labelsM : {T U : Ty} → Semantics.Segs T U → List Semantics.Selector
  | _, _, .nil => []
  | _, _, .cons h t => h.label :: t.labelsM

@[implemented_by Semantics.Segs.labelsM]
def Semantics.Segs.labels {T U : Ty} (p : Semantics.Segs T U) : List Semantics.Selector :=
  @Semantics.Segs.rec (fun _ _ _ => List Semantics.Selector) (fun {_} => [])
    (fun {_ _ _} h _ ih => h.label :: ih) T U p

theorem Semantics.Segs.labels_eq_labelsM : {T U : Ty} → (p : Semantics.Segs T U) →
    p.labels = p.labelsM
  | _, _, .nil => rfl
  | _, _, .cons h t => by exact congrArg (h.label :: ·) (t.labels_eq_labelsM)

namespace Path

/-- The compiled segment view. -/
def segmentsM : {T U : Ty} → Path T U → Semantics.Segs T U
  | _, _, .nil => .nil
  | _, _, .field h p => .cons (.field h) p.segmentsM
  | _, _, .at i p => .cons (.at i) p.segmentsM
  | _, _, .atF i p => .cons (.atF i) p.segmentsM
  | _, _, .key k p => .cons (.key k) p.segmentsM

/-- A path's segment sequence retains both endpoints and every intermediate type.
The recursor avoids dependent pattern-match casts in kernel reductions. -/
@[implemented_by segmentsM]
def segments {T U : Ty} (p : Path T U) : Semantics.Segs T U :=
  @Path.rec (fun T U _ => Semantics.Segs T U) (fun {_} => .nil)
    (fun {_ _ _ _} h _ ih => .cons (.field h) ih)
    (fun {_ _} i _ ih => .cons (.at i) ih)
    (fun {_ _ _} i _ ih => .cons (.atF i) ih)
    (fun {_ _ _} k _ ih => .cons (.key k) ih) T U p

theorem segments_eq_segmentsM : {T U : Ty} → (p : Path T U) → p.segments = p.segmentsM
  | _, _, .nil => rfl
  | _, _, .field h p => by exact congrArg (Semantics.Segs.cons (.field h)) (segments_eq_segmentsM p)
  | _, _, .at i p => by exact congrArg (Semantics.Segs.cons (.at i)) (segments_eq_segmentsM p)
  | _, _, .atF i p => by exact congrArg (Semantics.Segs.cons (.atF i)) (segments_eq_segmentsM p)
  | _, _, .key k p => by exact congrArg (Semantics.Segs.cons (.key k)) (segments_eq_segmentsM p)

/-- The labels the side conditions observe from the typed segment sequence. -/
def labels {T U : Ty} (p : Path T U) : List Semantics.Selector := p.segments.labels

theorem labels_nil {T : Ty} : (Path.nil (T := T)).labels = [] := rfl
theorem labels_field {s f : Name} {T U : Ty} (h : lookupBy f (structDef s) = some T)
    (p : Path T U) : (Path.field h p).labels = .field f :: p.labels := rfl
theorem labels_at {E U : Ty} (i : PrimTy.uint.Denote) (p : Path E U) :
    (Path.at i p).labels = .idx i :: p.labels := rfl
theorem labels_atF {E U : Ty} {n : Nat} (i : PrimTy.uint.Denote) (p : Path E U) :
    (Path.atF (n := n) i p).labels = .idx i :: p.labels := rfl
theorem labels_key {K : PrimTy} {V U : Ty} (k : K.Denote) (p : Path V U) :
    (Path.key (K := K) k p).labels = .key ⟨K, k⟩ :: p.labels := rfl

attribute [irreducible] labels
attribute [sol_eqns labels_nil labels_field labels_at labels_atF labels_key] labels

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
theorem append_at {E U W : Ty} (i : PrimTy.uint.Denote) (p : Path E U) (q : Path U W) :
    (Path.at i p).append q = .at i (p.append q) := rfl
theorem append_atF {E U W : Ty} {n : Nat} (i : PrimTy.uint.Denote) (p : Path E U) (q : Path U W) :
    (Path.atF (n := n) i p).append q = .atF i (p.append q) := rfl
theorem append_key {K : PrimTy} {V U W : Ty} (k : K.Denote) (p : Path V U) (q : Path U W) :
    (Path.key (K := K) k p).append q = .key k (p.append q) := rfl

attribute [irreducible] append
attribute [sol_eqns append_nil append_field append_at append_atF append_key] append

theorem append_eq_appendM : {T U W : Ty} → (p : Path T U) → (q : Path U W) →
    p.append q = p.appendM q
  | _, _, _, .nil, q => by rw [append_nil, appendM]
  | _, _, _, .field h p, q => by rw [append_field, appendM, append_eq_appendM p q]
  | _, _, _, .at i p, q => by rw [append_at, appendM, append_eq_appendM p q]
  | _, _, _, .atF i p, q => by rw [append_atF, appendM, append_eq_appendM p q]
  | _, _, _, .key k p, q => by rw [append_key, appendM, append_eq_appendM p q]

theorem labels_append : {T U W : Ty} → (p : Path T U) → (q : Path U W) →
    (p.append q).labels = p.labels ++ q.labels
  | _, _, _, .nil, _ => by rw [append_nil, labels_nil, List.nil_append]
  | _, _, _, .field _ p, q => by
    rw [append_field, labels_field, labels_field, List.cons_append, labels_append p q]
  | _, _, _, .at _ p, q => by
    rw [append_at, labels_at, labels_at, List.cons_append, labels_append p q]
  | _, _, _, .atF _ p, q => by
    rw [append_atF, labels_atF, labels_atF, List.cons_append, labels_append p q]
  | _, _, _, .key _ p, q => by
    rw [append_key, labels_key, labels_key, List.cons_append, labels_append p q]

/-- The one step `b[i]` takes, by how `R` is indexed.  By `casesOn`, so the
kernel casts nothing. -/
def index {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) (i : k.Denote) :
    Path (.ref R) V :=
  @IndexTy.casesOn (fun R k V _ => k.Denote → Path (.ref R) V) R k V it
    (fun {_} {_} i => .key i .nil)
    (fun {_} {_} a i => @ArrTy.casesOn (fun R E _ => Path (.ref R) E) _ _ a
      (fun {_} => .at i .nil)
      (fun {_} {_} => .atF i .nil)) i

theorem index_map {k : PrimTy} {V : Ty} (i : k.Denote) :
    index (IndexTy.map (k := k) (V := V)) i = .key i .nil := rfl
theorem index_dyn {E : Ty} (i : PrimTy.uint.Denote) :
    index (IndexTy.arr (ArrTy.dyn (E := E))) i = .at i .nil := rfl
theorem index_fixed {E : Ty} {n : Nat} (i : PrimTy.uint.Denote) :
    index (IndexTy.arr (ArrTy.fixed (E := E) (n := n))) i = .atF i .nil := rfl

attribute [irreducible] index
attribute [sol_eqns index_map index_dyn index_fixed] index

/-- The label of an index: a mapping's key, an array's index. -/
def _root_.Solidity.IndexTy.label {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V)
    (i : k.Denote) : Semantics.Selector :=
  @IndexTy.casesOn (fun _ k _ _ => k.Denote → Semantics.Selector) R k V it
    (fun {k} {_} i => .key ⟨k, i⟩) (fun {_} {_} _ i => .idx i) i

theorem labels_index : {R : RefTy} → {k : PrimTy} → {V : Ty} → (it : IndexTy R k V) →
    (i : k.Denote) → (index it i).labels = [it.label i]
  | _, _, _, .map, _ => by rw [index_map, labels_key, labels_nil]; rfl
  | _, _, _, .arr .dyn, _ => by rw [index_dyn, labels_at, labels_nil]; rfl
  | _, _, _, .arr .fixed, _ => by rw [index_fixed, labels_atF, labels_nil]; rfl

end Path

end Solidity
