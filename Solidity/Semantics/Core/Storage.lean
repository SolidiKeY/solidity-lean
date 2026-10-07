import Solidity.Semantics.Core.Value

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

`find`, `findLive` and `save`, which the kernel evaluates on every storage
access, are written with `Path.rec` over `SVal.view` (Gate G0, conditions 1
and 2), each with a `match` twin as its compiled form; the other functions
still `match` on the indexed families.
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

/-! ## Erasure -/

mutual
/-- The untyped value. -/
def SVal.erase : {T : Ty} → SVal T → Semantics.SVal
  | _, .prim v => .prim (PrimTy.erase v)
  | _, .struct fs => .struct (SFields.erase fs)
  | _, .array e sh => .array (SList.erase e) (SList.erase sh) false
  | _, .fixed e => .array (SVec.erase e) [] true
  | _, .map m d => .map (SMap.erase m) (SVal.erase d)

def SFields.erase : {fs : List (Name × Ty)} → SFields fs → List (Name × Semantics.SVal)
  | _, .nil => []
  | _, @SFields.cons f _ _ v rest => (f, SVal.erase v) :: SFields.erase rest

def SList.erase : {E : Ty} → SList E → List Semantics.SVal
  | _, .nil => []
  | _, .cons v rest => SVal.erase v :: SList.erase rest

def SVec.erase : {E : Ty} → {n : Nat} → SVec E n → List Semantics.SVal
  | _, _, .nil => []
  | _, _, .cons v rest => SVal.erase v :: SVec.erase rest

def SMap.erase : {V : Ty} → SMap V → List (Int × Semantics.SVal)
  | _, .nil => []
  | _, .cons k v rest => (k, SVal.erase v) :: SMap.erase rest
end

/-! ## Lists, vectors and maps as Lean lists -/

namespace SList

def toList {E : Ty} : SList E → List (SVal E)
  | .nil => []
  | .cons v rest => v :: rest.toList

def ofList {E : Ty} : List (SVal E) → SList E
  | [] => .nil
  | v :: rest => .cons v (ofList rest)

@[simp] theorem toList_ofList {E : Ty} : (l : List (SVal E)) → (ofList l).toList = l
  | [] => rfl
  | v :: rest => congrArg (v :: ·) (toList_ofList rest)

@[simp] theorem ofList_toList {E : Ty} : (l : SList E) → ofList l.toList = l
  | .nil => rfl
  | .cons v rest => congrArg (SList.cons v) (ofList_toList rest)

theorem erase_eq {E : Ty} : (l : SList E) → l.erase = l.toList.map SVal.erase
  | .nil => by simp only [SList.erase, toList, List.map_nil]
  | .cons v rest => by simp only [SList.erase, toList, List.map_cons, erase_eq rest]

/-- The number of values. -/
def length {E : Ty} (l : SList E) : Nat := l.toList.length

end SList

namespace SVec

def toList {E : Ty} : {n : Nat} → SVec E n → List (SVal E)
  | _, .nil => []
  | _, .cons v rest => v :: rest.toList

theorem length_toList {E : Ty} : {n : Nat} → (v : SVec E n) → v.toList.length = n
  | _, .nil => rfl
  | _, .cons _ rest => congrArg (· + 1) (length_toList rest)

theorem erase_eq {E : Ty} : {n : Nat} → (l : SVec E n) → l.erase = l.toList.map SVal.erase
  | _, .nil => by simp only [SVec.erase, toList, List.map_nil]
  | _, .cons v rest => by simp only [SVec.erase, toList, List.map_cons, erase_eq rest]

/-- `n` copies of a value. -/
def replicate {E : Ty} (v : SVal E) : (n : Nat) → SVec E n
  | 0 => .nil
  | n + 1 => .cons v (replicate v n)

theorem toList_replicate {E : Ty} (v : SVal E) :
    (n : Nat) → (replicate v n).toList = List.replicate n v
  | 0 => rfl
  | n + 1 => congrArg (v :: ·) (toList_replicate v n)

/-- The vector with the value at `i` replaced, as `List.set`. -/
def set {E : Ty} : {n : Nat} → SVec E n → Nat → SVal E → SVec E n
  | _, .nil, _, _ => .nil
  | _, .cons _ rest, 0, x => .cons x rest
  | _, .cons v rest, i + 1, x => .cons v (rest.set i x)

theorem toList_set {E : Ty} : {n : Nat} → (l : SVec E n) → (i : Nat) → (x : SVal E) →
    (l.set i x).toList = l.toList.set i x
  | _, .nil, _, _ => rfl
  | _, .cons _ _, 0, _ => rfl
  | _, .cons v rest, i + 1, x => congrArg (v :: ·) (toList_set rest i x)

/-- A function applied to every value. -/
def map {E : Ty} (f : SVal E → SVal E) : {n : Nat} → SVec E n → SVec E n
  | _, .nil => .nil
  | _, .cons v rest => .cons (f v) (rest.map f)

theorem toList_map {E : Ty} (f : SVal E → SVal E) : {n : Nat} → (l : SVec E n) →
    (l.map f).toList = l.toList.map f
  | _, .nil => rfl
  | _, .cons v rest => congrArg (f v :: ·) (toList_map f rest)

/-- Two vectors combined value by value. -/
def zipWith {E : Ty} (f : SVal E → SVal E → SVal E) : {n : Nat} → SVec E n → SVec E n → SVec E n
  | _, .nil, .nil => .nil
  | _, .cons a as, .cons b bs => .cons (f a b) (zipWith f as bs)

end SVec

namespace SMap

def toList {V : Ty} : SMap V → List (Int × SVal V)
  | .nil => []
  | .cons k v rest => (k, v) :: rest.toList

def ofList {V : Ty} : List (Int × SVal V) → SMap V
  | [] => .nil
  | (k, v) :: rest => .cons k v (ofList rest)

@[simp] theorem toList_ofList {V : Ty} : (l : List (Int × SVal V)) → (ofList l).toList = l
  | [] => rfl
  | (k, v) :: rest => congrArg ((k, v) :: ·) (toList_ofList rest)

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

/-- The value of the first member named `f`. -/
def get {f : Name} : {fs : List (Name × Ty)} → {T : Ty} → SFields fs →
    lookupBy f fs = some T → SVal T
  | _, _, .nil, h => absurd h (by simp only [lookupBy, reduceCtorEq, not_false_eq_true])
  | _, _, @SFields.cons f' _ _ v rest, h =>
    if e : f = f' then lookupBy_cons_pos e h ▸ v
    else rest.get (lookupBy_cons_neg e h)

/-- The first member named `f` replaced. -/
def set {f : Name} : {fs : List (Name × Ty)} → {T : Ty} → SFields fs →
    lookupBy f fs = some T → SVal T → SFields fs
  | _, _, .nil, _, _ => .nil
  | _, _, @SFields.cons f' _ _ v rest, h, x =>
    if e : f = f' then .cons ((lookupBy_cons_pos e h).symm ▸ x) rest
    else .cons v (rest.set (lookupBy_cons_neg e h) x)

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

mutual
/-- `delete`'s value (`Semantics.SVal.defaultOf`): primitives reset, members
and elements recursively, a dynamic array emptied into the slots past its
end, a mapping left as it is. -/
def SVal.defaultOf : {T : Ty} → SVal T → SVal T
  | _, @SVal.prim p _ => .prim (PrimTy.dflt p)
  | _, .struct fs => .struct (SFields.defaultOf fs)
  | _, .array e sh => .array .nil (.ofList ((SList.defaultOf e).toList ++ sh.toList))
  | _, .fixed e => .fixed (SVec.defaultOf e)
  | _, .map m d => .map m d

def SFields.defaultOf : {fs : List (Name × Ty)} → SFields fs → SFields fs
  | _, .nil => .nil
  | _, .cons v rest => .cons (SVal.defaultOf v) (SFields.defaultOf rest)

def SList.defaultOf : {E : Ty} → SList E → SList E
  | _, .nil => .nil
  | _, .cons v rest => .cons (SVal.defaultOf v) (SList.defaultOf rest)

def SVec.defaultOf : {E : Ty} → {n : Nat} → SVec E n → SVec E n
  | _, _, .nil => .nil
  | _, _, .cons v rest => .cons (SVal.defaultOf v) (SVec.defaultOf rest)
end

mutual
/-- A value as written to slots nothing has written (`Semantics.SVal.strip`):
no slots past an array's end. -/
def SVal.strip : {T : Ty} → SVal T → SVal T
  | _, .prim v => .prim v
  | _, .struct fs => .struct (SFields.strip fs)
  | _, .array e _ => .array (SList.strip e) .nil
  | _, .fixed e => .fixed (SVec.strip e)
  | _, .map m d => .map m d

def SFields.strip : {fs : List (Name × Ty)} → SFields fs → SFields fs
  | _, .nil => .nil
  | _, .cons v rest => .cons (SVal.strip v) (SFields.strip rest)

def SList.strip : {E : Ty} → SList E → SList E
  | _, .nil => .nil
  | _, .cons v rest => .cons (SVal.strip v) (SList.strip rest)

def SVec.strip : {E : Ty} → {n : Nat} → SVec E n → SVec E n
  | _, _, .nil => .nil
  | _, _, .cons v rest => .cons (SVal.strip v) (SVec.strip rest)
end

mutual
/-- A copy of `new` written over `old` (`Semantics.SVal.overlay`): member by
member in their order, as solc copies, element by element over the slots
it lands on, the old elements past the new length cleared, a mapping kept. -/
def SVal.overlay : {T : Ty} → SVal T → SVal T → SVal T
  | _, _, .prim v => .prim v
  | _, .struct ofs, .struct nfs => .struct (SFields.overlay ofs nfs)
  | _, .array oel osh, .array nel _ =>
    .array (SList.overlayOn (oel.toList ++ osh.toList) nel)
      (.ofList ((oel.toList.drop nel.length).map SVal.defaultOf ++
        osh.toList.drop (nel.length - oel.length)))
  | _, .fixed oel, .fixed nel => .fixed (SVec.overlay oel nel)
  | _, .map oe od, .map _ _ => .map oe od

def SFields.overlay : {fs : List (Name × Ty)} → SFields fs → SFields fs → SFields fs
  | _, .nil, .nil => .nil
  | _, .cons o os, .cons v rest => .cons (SVal.overlay o v) (SFields.overlay os rest)

/-- The new elements over the old slots, as far as there are old slots. -/
def SList.overlayOn : {E : Ty} → List (SVal E) → SList E → SList E
  | _, [], rest => SList.strip rest
  | _, o :: os, .cons v rest => .cons (SVal.overlay o v) (SList.overlayOn os rest)
  | _, _ :: _, .nil => .nil

def SVec.overlay : {E : Ty} → {n : Nat} → SVec E n → SVec E n → SVec E n
  | _, _, .nil, .nil => .nil
  | _, _, .cons o os, .cons v rest => .cons (SVal.overlay o v) (SVec.overlay os rest)
end

/-- A primitive value: a write stores it, where a reference is copied over. -/
def SVal.isPrim : {T : Ty} → SVal T → Bool
  | _, .prim _ => true
  | _, _ => false

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

/-- `b[i]`'s index in bounds where the program takes it (`State.checkIndex`):
a mapping takes every key, an array an index below its live length. -/
def checkIndex {R : RefTy} {k : PrimTy} {V : Ty} (st : Storage C) (r : SRef C (.ref R))
    (it : IndexTy R k V) (i : Int) : Option Unit := do
  let v ← st.find r
  match it, v with
  | .map, _ => some ()
  | .arr .dyn, .array e _ => if 0 ≤ i ∧ i.toNat < e.length then some () else none
  | .arr .fixed, @SVal.fixed _ n _ => if 0 ≤ i ∧ i.toNat < n then some () else none

/-- The live length of a dynamic array (`arrayLen`). -/
def len {E : Ty} (st : Storage C) (r : SRef C (.ref (.array E))) : Option Nat := do
  match ← st.find r with
  | .array e _ => some e.length

/-- `b.push(…)` (`pushAt`): the element `val` makes of the slot it lands on,
appended. -/
def push {E : Ty} (st : Storage C) (r : SRef C (.ref (.array E)))
    (val : SVal E → Option (SVal E)) : Option (Storage C) := do
  match ← st.find r with
  | .array e sh =>
    let (slot, sh') := pushSlot E sh.toList
    let x ← val slot
    st.save r (.array (.ofList (e.toList ++ [x])) (.ofList sh'))

/-- `b.push()` as a place (`pushPlaceAt`): the slot appended, and its index. -/
def pushPlace {E : Ty} (st : Storage C) (r : SRef C (.ref (.array E))) :
    Option (Storage C × Nat) := do
  match ← st.find r with
  | .array e sh =>
    let (slot, sh') := pushSlot E sh.toList
    let st' ← st.save r (.array (.ofList (e.toList ++ [slot])) (.ofList sh'))
    some (st', e.length)

/-- `b.pop()` (`popAt`): the last element cleared into the slots past the
end, or moved there as it is when `keep`; an empty array reverts. -/
def pop {E : Ty} (st : Storage C) (keep : Bool) (r : SRef C (.ref (.array E))) :
    Option (Storage C) := do
  match ← st.find r with
  | .array e sh =>
    match e.toList.reverse with
    | [] => none
    | last :: restRev =>
      st.save r (.array (.ofList restRev.reverse)
        (.ofList ((if keep then last else last.defaultOf) :: sh.toList)))

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
