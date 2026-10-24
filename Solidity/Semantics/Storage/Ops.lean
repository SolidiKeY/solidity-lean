import Solidity.Semantics.Storage.Values

/-!
# Typed storage: find, save and the stores

Find and save with their `match` twins (one module, so the twins' matchers
are the definitions' own), delete and copy over, equality, the storage, a
save read back, the stores.

A piece of `Semantics/Storage.lean`, whose docstring describes the whole.
-/

namespace Solidity

open Semantics (structDef lookupBy setBy tyRank fieldsRank structRank)

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
    match (e.toList ++ sh.toList)[i.1.toNat]? with
    | some x => x.findM p
    | none => none
  | _, _, .fixed e, .atF i p =>
    match e.toList[i.1.toNat]? with
    | some x => x.findM p
    | none => none
  | _, _, .map m d, .key k p =>
    match lookupBy k m.toList with
    | some x => x.findM p
    | none => d.findM p

/-- `SVal.findLive` by `match`, its compiled form. -/
def SVal.findLiveM : {T U : Ty} → SVal T → Path T U → Option (SVal U)
  | _, _, v, .nil => some v
  | _, _, .struct fs, .field h p => (fs.get h).findLiveM p
  | _, _, .array e _ _, .at i p =>
    match e.toList[i.1.toNat]? with
    | some x => x.findLiveM p
    | none => none
  | _, _, .fixed e, .atF i p =>
    match e.toList[i.1.toNat]? with
    | some x => x.findLiveM p
    | none => none
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
    match (e.toList ++ sh.toList)[i.1.toNat]? with
    | some x => do
      let x' ← x.saveM p new
      let slots := (e.toList ++ sh.toList).set i.1.toNat x'
      some (.array (SVec.ofList (slots.take n)) (.ofList (slots.drop n))
        (SVal.take_lt_bound slots h))
    | none => none
  | _, _, .fixed e, .atF i p, new =>
    match e.toList[i.1.toNat]? with
    | some x => do
      let x' ← x.saveM p new
      some (.fixed (e.set i.1.toNat x'))
    | none => none
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
      match (w.elems.toList ++ w.shadow.toList)[i.1.toNat]? with
      | some x => ih x
      | none => none)
    (fun {_} {_} {_} i _ ih v =>
      match (SVal.view v : SVec _ _).toList[i.1.toNat]? with
      | some x => ih x
      | none => none)
    (fun {_} {_} {_} k _ ih v =>
      let w : SMap _ _ × SVal _ := SVal.view v
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
      match w.elems.toList[i.1.toNat]? with
      | some x => ih x
      | none => none)
    (fun {_} {_} {_} i _ ih v =>
      match (SVal.view v : SVec _ _).toList[i.1.toNat]? with
      | some x => ih x
      | none => none)
    (fun {_} {_} {_} k _ ih v =>
      let w : SMap _ _ × SVal _ := SVal.view v
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
      match (w.elems.toList ++ w.shadow.toList)[i.1.toNat]? with
      | some x => do
        let x' ← ih x new
        let slots := (w.elems.toList ++ w.shadow.toList).set i.1.toNat x'
        some (.array (SVec.ofList (slots.take w.n)) (.ofList (slots.drop w.n))
          (SVal.take_lt_bound slots w.hn))
      | none => none)
    (fun {_} {_} {_} i _ ih v new =>
      let e : SVec _ _ := SVal.view v
      match e.toList[i.1.toNat]? with
      | some x => do
        let x' ← ih x new
        some (.fixed (e.set i.1.toNat x'))
      | none => none)
    (fun {_} {_} {_} k _ ih v new =>
      let w : SMap _ _ × SVal _ := SVal.view v
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
  M K U := SMap K U
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
theorem SVal.defaultOf_map {K : PrimTy} {U : Ty} (m : SMap K U) (d : SVal U) :
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
attribute [sol_eqns SVal.defaultOf_prim SVal.defaultOf_struct SVal.defaultOf_array
  SVal.defaultOf_fixed SVal.defaultOf_map] SVal.defaultOf
attribute [sol_eqns SFields.defaultOf_nil SFields.defaultOf_cons] SFields.defaultOf
attribute [sol_eqns SList.defaultOf_nil SList.defaultOf_cons] SList.defaultOf
attribute [sol_eqns SVec.defaultOf_nil SVec.defaultOf_cons] SVec.defaultOf

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
  M K U := SMap K U
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
theorem SVal.strip_map {K : PrimTy} {U : Ty} (m : SMap K U) (d : SVal U) :
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
attribute [sol_eqns SVal.strip_prim SVal.strip_struct SVal.strip_array SVal.strip_fixed
  SVal.strip_map] SVal.strip
attribute [sol_eqns SFields.strip_nil SFields.strip_cons] SFields.strip
attribute [sol_eqns SList.strip_nil SList.strip_cons] SList.strip
attribute [sol_eqns SVec.strip_nil SVec.strip_cons] SVec.strip

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

/-- Pad a vector on the right with `d`, to the requested length. The copy
witness below admits only lengths that retain the whole source. -/
def SVec.padRight {E : Ty} (d : SVal E) : {n : Nat} → SVec E n → (m : Nat) → SVec E m
  | _, _, 0 => .nil
  | 0, .nil, m + 1 => .cons d (SVec.padRight d .nil m)
  | _ + 1, .cons v vs, m + 1 => .cons v (SVec.padRight d vs m)

/-- A slot of `[a,b]` padded to four slots reads `a,b,d,d`; outside four
slots it is absent. -/
theorem SVec.getElem?_padRight {E : Ty} (d : SVal E) : {n : Nat} → (vs : SVec E n) →
    (m i : Nat) → (vs.padRight d m).toList[i]? =
      if i < m then (if i < n then vs.toList[i]? else some d) else none
  | _, _, 0, i => by simp only [SVec.padRight, SVec.toList_nil, List.getElem?_nil, Nat.not_lt_zero, ↓reduceIte]
  | 0, .nil, m + 1, i => by
    cases i with
    | zero => simp only [SVec.padRight, SVec.toList_cons, List.getElem?_cons_zero,
        Nat.zero_lt_succ, Nat.not_lt_zero, ↓reduceIte]
    | succ i =>
      simp only [SVec.padRight, SVec.toList_cons, List.getElem?_cons_succ, Nat.succ_lt_succ_iff,
        Nat.not_lt_zero, ↓reduceIte]
      exact SVec.getElem?_padRight d .nil m i
  | n + 1, .cons v vs, m + 1, i => by
    cases i with
    | zero => simp only [SVec.padRight, SVec.toList_cons, List.getElem?_cons_zero,
        Nat.zero_lt_succ, ↓reduceIte]
    | succ i =>
      simp only [SVec.padRight, SVec.toList_cons, List.getElem?_cons_succ, Nat.succ_lt_succ_iff]
      exact SVec.getElem?_padRight d vs m i

/-- The source snapshot of `uint[2] -> uint[]` or `uint[2] -> uint[4]`,
at the destination type. Copying subsequently uses `Storage.write` and
`overlay`, which retain the destination's own shadow histories. -/
def FixedCopy.apply {E : Ty} {n : Nat} : {R : RefTy} → FixedCopy E n R →
    SVal (.ref (.fixed E n)) → SVal (.ref R)
  | _, .dynamic bound, .fixed vs => .array vs.strip .nil bound
  | _, .fixed m _, .fixed vs => .fixed (vs.strip.padRight (SVal.dflt E).strip m)

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
  M _ _ := Unit
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
theorem SVal.overlay_map {K : PrimTy} {U : Ty} (oe ne : SMap K U) (od nd : SVal U) :
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
attribute [sol_eqns SVal.overlay_prim SVal.overlay_struct SVal.overlay_array SVal.overlay_fixed
  SVal.overlay_map] SVal.overlay
attribute [sol_eqns SFields.overlay_nil SFields.overlay_cons] SFields.overlay
attribute [sol_eqns SVec.overlayOn_nil SVec.overlayOn_nil_cons SVec.overlayOn_cons_cons]
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
  M K U := SMap K U → Bool
  prim := fun {p} x w => decide (x = (SVal.view w : p.Denote))
  struct := fun _ ih w => ih (SVal.view w)
  array := fun _ _ _ ie ish w =>
    let x : ArrView _ := SVal.view w
    ie x.elems.toList && ish x.shadow
  fixed := fun _ ie w => ie (SVal.view w : SVec _ _).toList
  map := fun _ _ im id w =>
    let x : SMap _ _ × SVal _ := SVal.view w
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
def SMap.beq {K : PrimTy} {U : Ty} (m m' : SMap K U) : Bool := m.fold beqFold m'

theorem SVal.beq_prim {p : PrimTy} (x y : p.Denote) :
    (SVal.prim x).beq (.prim y) = decide (x = y) := rfl
theorem SVal.beq_struct {s : Name} (fs gs : SFields (structDef s)) :
    (SVal.struct fs).beq (.struct gs) = fs.beq gs := rfl
theorem SVal.beq_array {E : Ty} {n m : Nat} (e : SVec E n) (sh : SList E) (h : n < 2 ^ 256)
    (e' : SVec E m) (sh' : SList E) (h' : m < 2 ^ 256) :
    (SVal.array e sh h).beq (.array e' sh' h') = (e.beqL e'.toList && sh.beq sh') := rfl
theorem SVal.beq_fixed {E : Ty} {n : Nat} (e e' : SVec E n) :
    (SVal.fixed e).beq (.fixed e') = e.beqL e'.toList := rfl
theorem SVal.beq_map {K : PrimTy} {U : Ty} (m m' : SMap K U) (d d' : SVal U) :
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
theorem SMap.beq_nil_nil {K : PrimTy} {U : Ty} : SMap.beq (K := K) (U := U) .nil .nil = true := rfl
theorem SMap.beq_nil_cons {K : PrimTy} {U : Ty} (k : K.Denote) (w : SVal U) (rest' : SMap K U) :
    SMap.beq .nil (.cons k w rest') = false := rfl
theorem SMap.beq_cons_nil {K : PrimTy} {U : Ty} (k : K.Denote) (v : SVal U) (rest : SMap K U) :
    SMap.beq (.cons k v rest) .nil = false := rfl
theorem SMap.beq_cons_cons {K : PrimTy} {U : Ty} (k k' : K.Denote) (v w : SVal U)
    (rest rest' : SMap K U) :
    SMap.beq (.cons k v rest) (.cons k' w rest') = (decide (k = k') && v.beq w && rest.beq rest') :=
  rfl

attribute [irreducible] SVal.beq SFields.beq SList.beq SVec.beqL SMap.beq
attribute [sol_eqns SVal.beq_prim SVal.beq_struct SVal.beq_array SVal.beq_fixed SVal.beq_map]
  SVal.beq
attribute [sol_eqns SFields.beq_nil SFields.beq_cons] SFields.beq
attribute [sol_eqns SList.beq_nil_nil SList.beq_nil_cons SList.beq_cons_nil SList.beq_cons_cons]
  SList.beq
attribute [sol_eqns SVec.beqL_nil_nil SVec.beqL_nil_cons SVec.beqL_cons_nil SVec.beqL_cons_cons]
  SVec.beqL
attribute [sol_eqns SMap.beq_nil_nil SMap.beq_nil_cons SMap.beq_cons_nil SMap.beq_cons_cons] SMap.beq

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

theorem SMap.eq_of_beq : {K : PrimTy} → {U : Ty} → (m m' : SMap K U) → m.beq m' = true →
    m = m'
  | _, _, .nil, .nil, _ => rfl
  | _, _, .nil, .cons _ _ _, h => by simp only [SMap.beq, Bool.false_eq_true] at h
  | _, _, .cons _ _ _, .nil, h => by simp only [SMap.beq, Bool.false_eq_true] at h
  | _, _, .cons k v rest, .cons k' w rest', h => by
    simp only [SMap.beq, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1.1, SVal.eq_of_beq v w h.1.2, SMap.eq_of_beq rest rest' h.2]
termination_by structural _ _ m => m
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

theorem SMap.beq_self : {K : PrimTy} → {U : Ty} → (m : SMap K U) → m.beq m = true
  | _, _, .nil => by simp only [SMap.beq]
  | _, _, .cons k v rest => by simp only [SMap.beq, decide_true, SVal.beq_self v,
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

/-- The slot `push` lands on, as it is, and the slots left: an empty push
saves only the length (solkey's `storagePushLengthSave`), so a recycled
reference slot is exposed with what a dangling alias wrote there, as solc
leaves it.  A primitive slot past the end holds its default on every
reachable storage (`tightH`), so it starts at its default. -/
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

/-- A length as a `uint`, the default past the bound (no storage has an
array that long: `SVal.array`'s `hn`). -/
def uintOfNat (n : Nat) : PrimTy.uint.Denote :=
  if h : n < 2 ^ 256 then lenU n h else PrimTy.dflt .uint

theorem uintOfNat_val {n : Nat} (h : n < 2 ^ 256) : (uintOfNat n).1 = n := by
  simp only [uintOfNat, dif_pos h, lenU]

theorem uintOfNat_eq_lenU {n : Nat} (h : n < 2 ^ 256) : uintOfNat n = lenU n h := dif_pos h

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

/-- A root followed by typed segments: the contract types the root and
adjacent segment endpoints agree all the way to the selected value. -/
structure RefSegments (C : Contract) (U : Ty) where
  root : Name
  {ty : Ty}
  hroot : C.rootType root = some ty
  tail : Semantics.Segs ty U

/-- The typed segment view of a storage reference. -/
def SRef.segments {C : Contract} {U : Ty} (r : SRef C U) : RefSegments C U :=
  ⟨r.root, r.hroot, r.path.segments⟩

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
def index {R : RefTy} {k : PrimTy} {V : Ty} (r : SRef C (.ref R)) (it : IndexTy R k V)
    (i : k.Denote) : SRef C V :=
  r.append (Path.index it i)


end SRef

namespace Storage

variable {C : Contract}


/-- The storage a contract starts with: every state variable at its
default. -/
def init (C : Contract) : Storage C := SFields.dflt C.vars

/-- The value at a reference (solkey's `find`). -/
def find {U : Ty} (st : Storage C) (r : SRef C U) : Option (SVal U) :=
  (st.get r.hroot).find r.path

/-- `SVal.findLive` at a reference. -/
def findLive {U : Ty} (st : Storage C) (r : SRef C U) : Option (SVal U) :=
  (st.get r.hroot).findLive r.path

/-- The storage with the value at a reference replaced (solkey's `save`). -/
def save {U : Ty} (st : Storage C) (r : SRef C U) (new : SVal U) : Option (Storage C) := do
  let v ← (st.get r.hroot).save r.path new
  some (st.set r.hroot v)

/-- `checkIndex`'s test on the value at `b`: every key of a mapping, an index
below an array's live length.  By `casesOn`, so the kernel casts nothing. -/
def inBounds {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) (i : k.Denote) :
    SVal (.ref R) → Option Unit :=
  @IndexTy.casesOn (fun R k _ _ => k.Denote → SVal (.ref R) → Option Unit) R k V it
    (fun {_} {_} _ _ => some ())
    (fun {_} {_} a i => @ArrTy.casesOn (fun R _ _ => SVal (.ref R) → Option Unit) _ _ a
      (fun {_} v =>
        let w : ArrView _ := SVal.view v
        if (i : PrimTy.uint.Denote).1.toNat < w.n then some () else none)
      (fun {_} {n} _ =>
        if (i : PrimTy.uint.Denote).1.toNat < n then some () else none)) i

/-- `b[i]`'s index in bounds where the program takes it:
a mapping takes every key, an array an index below its live length. -/
def checkIndex {R : RefTy} {k : PrimTy} {V : Ty} (st : Storage C) (r : SRef C (.ref R))
    (it : IndexTy R k V) (i : k.Denote) : Option Unit := do
  inBounds it i (← st.find r)

/-- The live length of a dynamic array, a `uint`: it is below
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

/-- `b.push(…)`: the element `val` makes of the slot it lands on,
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

/-- `b.push()` as a place: the slot appended, and its index. -/
def pushPlace {E : Ty} (st : Storage C) (r : SRef C (.ref (.array E))) :
    Option (Storage C × PrimTy.uint.Denote) := do
  let w : ArrView E := SVal.view (← st.find r)
  let (slot, sh') := pushSlot E w.shadow.toList
  if h : w.n + 1 < 2 ^ 256 then
    let st' ← st.save r (.array (SVec.ofList (w.elems.toList ++ [slot])) (.ofList sh')
      (SVec.snoc_lt_bound w.elems slot h))
    some (st', lenU w.n (Nat.lt_of_succ_lt h))
  else none

theorem pushPlace_fst {E : Ty} (st : Storage C) (r : SRef C (.ref (.array E))) :
    (st.pushPlace r).map (·.1) = st.push r some := by
  unfold Storage.pushPlace Storage.push
  cases st.find r with
  | none => rfl
  | some v =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    split
    · cases st.save r _ <;> rfl
    · rfl

theorem push_of_pushPlace {E : Ty} {st st' : Storage C} {r : SRef C (.ref (.array E))}
    {k : PrimTy.uint.Denote} (h : st.pushPlace r = some (st', k)) : st.push r some = some st' := by
  rw [← pushPlace_fst, h]; rfl

/-- `b.pop()`: the last element cleared into the slots past the
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

/-- An assignment's write: a word stored, a struct or
an array copied over what is there. -/
def write {T : Ty} (st : Storage C) (r : SRef C T) (new : SVal T) : Option (Storage C) :=
  if new.isPrim then st.save r new
  else do st.save r ((← st.find r).overlay new)

end Storage

/-! ## A save read back

`findOnSave` and `findOnSaveFrame` on the compiled forms: a save reads back
at its path (`SVal.findM_saveM`), and leaves a path that parts from it
(`Path.Diverges`, `SVal.findM_saveM_diverges`). -/

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
    · rename_i x hx
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨y, hy, rfl⟩ := h
      have hl : i.1.toNat < (e.toList ++ sh.toList).length := (List.getElem?_eq_some_iff.mp hx).1
      simp only [SVal.findM, SVec.toList_ofList, SList.toList_ofList,
        List.take_append_drop, List.getElem?_set_self hl]
      exact SVal.findM_saveM _ p v hy
    · simp only [reduceCtorEq] at h
  | _, _, .fixed e, .atF i p, v, x', h => by
    simp only [SVal.saveM] at h
    split at h
    · rename_i x hx
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨y, hy, rfl⟩ := h
      have hl : i.1.toNat < e.toList.length := (List.getElem?_eq_some_iff.mp hx).1
      simp only [SVal.findM, SVec.toList_set, List.getElem?_set_self hl]
      exact SVal.findM_saveM _ p v hy
    · simp only [reduceCtorEq] at h
  | _, _, .map m d, .key k p, v, x', h => by
    simp only [SVal.saveM] at h
    split at h <;>
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨y, hy, rfl⟩ := h
      simp only [SVal.findM, SMap.toList_ofList, Semantics.lookupBy_setBy_self]
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
  | at {E U W : Ty} {i j : PrimTy.uint.Denote} (p : Path E U) (q : Path E W) (hne : i ≠ j) :
      Diverges (.at i p) (.at j q)
  | atIn {E U W : Ty} (i : PrimTy.uint.Denote) {p : Path E U} {q : Path E W} :
      Diverges p q → Diverges (.at i p) (.at i q)
  | atF {E U W : Ty} {n : Nat} {i j : PrimTy.uint.Denote} (p : Path E U) (q : Path E W) (hne : i ≠ j) :
      Diverges (.atF (n := n) i p) (.atF j q)
  | atFIn {E U W : Ty} {n : Nat} (i : PrimTy.uint.Denote) {p : Path E U} {q : Path E W} :
      Diverges p q → Diverges (.atF (n := n) i p) (.atF i q)
  | key {K : PrimTy} {V U W : Ty} {k k' : K.Denote} (p : Path V U) (q : Path V W) (hne : k ≠ k') :
      Diverges (.key (K := K) k p) (.key k' q)
  | keyIn {K : PrimTy} {V U W : Ty} (k : K.Denote) {p : Path V U} {q : Path V W} :
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
      · rename_i x0 hx
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hs
        obtain ⟨y, _, rfl⟩ := hs
        simp only [SVal.findM, SVec.toList_ofList, SList.toList_ofList, List.take_append_drop]
        have hne' : i.1 ≠ j.1 := fun e => hne (Subtype.ext e)
        have hn' : i.1.toNat ≠ j.1.toNat := by
          have := PrimTy.uint_nonneg i; have := PrimTy.uint_nonneg j; omega
        simp only [List.getElem?_set_ne hn']
      · simp only [reduceCtorEq] at hs
  | atIn i _ ih =>
    intro x v x' hs
    cases x with
    | array e sh hn =>
      simp only [SVal.saveM] at hs
      split at hs
      · rename_i x0 hx
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hs
        obtain ⟨y, hy, rfl⟩ := hs
        have hl : i.1.toNat < (e.toList ++ sh.toList).length :=
          (List.getElem?_eq_some_iff.mp hx).1
        simp only [SVal.findM, SVec.toList_ofList, SList.toList_ofList,
          List.take_append_drop, List.getElem?_set_self hl, hx]
        exact ih _ v hy
      · simp only [reduceCtorEq] at hs
  | @atF E U W n i j p q hne =>
    intro x v x' hs
    cases x with
    | fixed e =>
      simp only [SVal.saveM] at hs
      split at hs
      · rename_i x0 hx
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hs
        obtain ⟨y, _, rfl⟩ := hs
        simp only [SVal.findM, SVec.toList_set]
        have hne' : i.1 ≠ j.1 := fun e => hne (Subtype.ext e)
        have hn' : i.1.toNat ≠ j.1.toNat := by
          have := PrimTy.uint_nonneg i; have := PrimTy.uint_nonneg j; omega
        simp only [List.getElem?_set_ne hn']
      · simp only [reduceCtorEq] at hs
  | atFIn i _ ih =>
    intro x v x' hs
    cases x with
    | fixed e =>
      simp only [SVal.saveM] at hs
      split at hs
      · rename_i x0 hx
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hs
        obtain ⟨y, hy, rfl⟩ := hs
        have hl : i.1.toNat < e.toList.length := (List.getElem?_eq_some_iff.mp hx).1
        simp only [SVal.findM, SVec.toList_set, List.getElem?_set_self hl, hx]
        exact ih _ v hy
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
          Semantics.lookupBy_setBy_ne (Ne.symm hne)]
  | keyIn k _ ih =>
    intro x v x' hs
    cases x with
    | map m d =>
      simp only [SVal.saveM] at hs
      split at hs
      · rename_i x0 hx
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hs
        obtain ⟨y, hy, rfl⟩ := hs
        simp only [SVal.findM, SMap.toList_ofList, Semantics.lookupBy_setBy_self, hx]
        exact ih _ v hy
      · rename_i hx
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hs
        obtain ⟨y, hy, rfl⟩ := hs
        simp only [SVal.findM, SMap.toList_ofList, Semantics.lookupBy_setBy_self, hx]
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

theorem find_at {E U : Ty} {n : Nat} (e : SVec E n) (sh : SList E) (h : n < 2 ^ 256) (i : PrimTy.uint.Denote)
    (p : Path E U) :
    (SVal.array e sh h).find (.at i p) =
      match (e.toList ++ sh.toList)[i.1.toNat]? with
      | some x => x.find p
      | none => none := rfl

theorem find_atF {E U : Ty} {n : Nat} (e : SVec E n) (i : PrimTy.uint.Denote) (p : Path E U) :
    (SVal.fixed e).find (.atF i p) =
      match e.toList[i.1.toNat]? with
      | some x => x.find p
      | none => none := rfl

theorem find_key {K : PrimTy} {V U : Ty} (m : SMap K V) (d : SVal V) (k : K.Denote) (p : Path V U) :
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
    show (match e.toList[i.1.toNat]? with
      | some x => x.findLive p
      | none => none) = _
    simp only [findLive_eq_findLiveM _ p, findLiveM]
  | _, _, .fixed e, .atF i p => by
    show (match e.toList[i.1.toNat]? with
      | some x => x.findLive p
      | none => none) = _
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
    show (match (e.toList ++ sh.toList)[i.1.toNat]? with
      | some x => do
        let x' ← x.save p new
        let slots := (e.toList ++ sh.toList).set i.1.toNat x'
        some (SVal.array (SVec.ofList (slots.take n)) (.ofList (slots.drop n))
          (SVal.take_lt_bound slots h))
      | none => none : Option (SVal (.ref (.array E)))) = _
    simp only [save_eq_saveM _ p, saveM]
  | _, _, @SVal.fixed E n e, .atF i p, new => by
    show (match e.toList[i.1.toNat]? with
      | some x => do
        let x' ← x.save p new
        some (SVal.fixed (e.set i.1.toNat x'))
      | none => none : Option (SVal (.ref (.fixed E n)))) = _
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

/-- A successful `values[0] = v` reads back the complete typed value at
that reference, including reference values. -/
theorem Storage.find_save_same {C : Contract} {T : Ty} {st st' : Storage C}
    {r : SRef C T} {v : SVal T} (h : st.save r v = some st') : st'.find r = some v := by
  unfold Storage.save at h
  cases hs : (st.get r.hroot).save r.path v with
  | none => simp only [hs, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at h
  | some x =>
    simp only [hs, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
    subst st'
    rw [Storage.find, SFields.get_set_same]
    exact SVal.find_save_same _ _ _ hs

/-- `values.push()` appends the next slot and returns its old length,
for every typed storage, including a recycled shadow slot. -/
theorem Storage.pushPlace_shape {C : Contract} {E : Ty} {st st' : Storage C}
    {r : SRef C (.ref (.array E))} {k : PrimTy.uint.Denote}
    (h : st.pushPlace r = some (st', k)) :
    ∃ (n : Nat) (e : SVec E n) (sh : SList E) (hn : n < 2 ^ 256)
      (hcap : n + 1 < 2 ^ 256),
      k = lenU n hn ∧
      st'.find r = some (.array (SVec.ofList (e.toList ++ [(pushSlot E sh.toList).1]))
        (.ofList (pushSlot E sh.toList).2) (SVec.snoc_lt_bound e _ hcap)) := by
  unfold Storage.pushPlace at h
  cases hf : st.find r with
  | none => simp only [hf, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at h
  | some a =>
    cases a with
    | array e sh hn =>
      simp only [hf, Option.bind_eq_bind, Option.bind_some, SVal.view_array] at h
      split at h
      · rename_i hcap
        cases hs : st.save r (SVal.array (SVec.ofList (e.toList ++ [(pushSlot _ sh.toList).1]))
            (SList.ofList (pushSlot _ sh.toList).2) (SVec.snoc_lt_bound e _ hcap)) with
        | none => simp only [hs, Option.bind_none, reduceCtorEq] at h
        | some st₁ =>
          simp only [hs, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨_, e, sh, hn, hcap, rfl, Storage.find_save_same hs⟩
      · cases h

/-- After `values.push()`, its length is exactly one greater than the
index returned for the new slot. -/
theorem Storage.pushPlace_len {C : Contract} {E : Ty} {st st' : Storage C}
    {r : SRef C (.ref (.array E))} {k : PrimTy.uint.Denote}
    (h : st.pushPlace r = some (st', k)) :
    ∃ l : PrimTy.uint.Denote, st'.len r = some l ∧ l.1 = k.1 + 1 := by
  obtain ⟨n, e, sh, hn, hcap, rfl, hf⟩ := Storage.pushPlace_shape h
  refine ⟨lenU _ (SVec.snoc_lt_bound e (pushSlot E sh.toList).1 hcap), ?_, ?_⟩
  · simp only [Storage.len, hf, Option.bind_eq_bind, Option.bind_some, SVal.view_array]
  · simp only [lenU, List.length_append, List.length_singleton, SVec.length_toList]
    omega

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
