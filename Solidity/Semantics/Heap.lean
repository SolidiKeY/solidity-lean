import Solidity.Semantics.Storage

/-!
# Typed heap

Memory typed by the objects it holds (`docs/intrinsic.md`, M4c): a heap
typing `H : HTy` lists each object's type, oldest first, so an object's
identity is its position, and a memory value of type `T` (`MVal H T`) is a
word of `T` or a reference `HRef H R`, an identity `H` types at `R`.  An
object of type `R` (`MObj H R`) holds a struct's members in `structDef`'s
order, an array's elements, or exactly `n` elements of a `T[n]`; a mapping
type has none (`Empty`), so a heap holds no mapping.  These are computed from
the typing, as `TEnv` is from its context (Gate G0, condition 4): no indexed
family, no cast but the one at an object's own type.

Allocation appends, so it returns a heap over `H ++ [R]` and the reference,
and everything typed over `H` is weakened along the prefix (`H <+: H'`, the
returned extension that replaces `HeapTy.Extends`).  A weakening keeps every
identity.

The two copies allocate as solc does, members and elements first, then the
object itself: `SVal.copyStToM` (storage to memory, a fold
of `Semantics/Storage.lean`, so the kernel reduces it) needs a type
without mappings and cannot fail, and `MVal.copyMToSt` (memory to
storage) recurses on the type, by rank (fuel `rankBound`, which reads no
struct name) and inside one rank structurally, as `SVal.dflt` does: a reference's target has a smaller type, so there is no
cycle to guard against and no `undef` arm.
-/

namespace Solidity

open Semantics (structDef lookupBy setBy tyRank fieldsRank structRank)

/-- A heap typing: each memory object's type, by identity, oldest first. -/
abbrev HTy := List RefTy

/-- A reference to a memory object of type `R`: its identity. -/
structure HRef (H : HTy) (R : RefTy) where
  id : Nat
  get? : H[id]? = some R

theorem HTy.getElem?_of_prefix {H H' : HTy} {i : Nat} {R : RefTy} (e : H <+: H')
    (h : H[i]? = some R) : H'[i]? = some R := by
  obtain ⟨t, rfl⟩ := e
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

/-- A reference into a grown heap. -/
def HRef.wk {H H' : HTy} {R : RefTy} (e : H <+: H') (r : HRef H R) : HRef H' R :=
  ⟨r.id, HTy.getElem?_of_prefix e r.get?⟩

/-- A memory slot of type `T`: a word, or a reference to an object. -/
def MVal (H : HTy) : Ty → Type
  | .prim p => p.Denote
  | .ref R => HRef H R

/-- A struct object's members, one per member, in the members' order. -/
def MFields (H : HTy) : List (Name × Ty) → Type
  | [] => Unit
  | (_, T) :: fs => MVal H T × MFields H fs

/-- A memory object of type `R`: an array has fewer than `2^256` elements
(its length is a `uint`, `new T[](n)` takes one).  A mapping has none. -/
def MObj (H : HTy) : RefTy → Type
  | .struct s => MFields H (structDef s)
  | .array E => {l : List (MVal H E) // l.length < 2 ^ 256}
  | .fixed E n => {l : List (MVal H E) // l.length = n}
  | .mapping _ _ => Empty

/-- One object per type in `Rs`. -/
def Objs (H : HTy) : List RefTy → Type
  | [] => Unit
  | R :: Rs => MObj H R × Objs H Rs

/-- A heap: one object per identity its typing lists. -/
abbrev Heap (H : HTy) : Type := Objs H H

/-! ## Weakening -/

def MVal.wk {H H' : HTy} (e : H <+: H') : (T : Ty) → MVal H T → MVal H' T
  | .prim _, v => v
  | .ref _, r => HRef.wk e (r : HRef H _)

def MFields.wk {H H' : HTy} (e : H <+: H') : (fs : List (Name × Ty)) → MFields H fs → MFields H' fs
  | [], _ => ()
  | (_, T) :: fs, x => (MVal.wk e T x.1, MFields.wk e fs x.2)

def MObj.wk {H H' : HTy} (e : H <+: H') : (R : RefTy) → MObj H R → MObj H' R
  | .struct s, o => MFields.wk e (structDef s) o
  | .array E, o =>
    let o : {l : List (MVal H E) // l.length < 2 ^ 256} := o
    ⟨o.1.map (MVal.wk e E), by rw [List.length_map]; exact o.2⟩
  | .fixed E n, o =>
    let o : {l : List (MVal H E) // l.length = n} := o
    ⟨o.1.map (MVal.wk e E), by rw [List.length_map]; exact o.2⟩
  | .mapping _ _, o => (o : Empty).elim

def Objs.wk {H H' : HTy} (e : H <+: H') : (Rs : List RefTy) → Objs H Rs → Objs H' Rs
  | [], _ => ()
  | R :: Rs, os => (MObj.wk e R os.1, Objs.wk e Rs os.2)

/-! ## Objects by identity -/

/-- The object at position `i`. -/
def Objs.get {H : HTy} {R : RefTy} : (Rs : List RefTy) → Objs H Rs → (i : Nat) →
    Rs[i]? = some R → MObj H R
  | [], _, _, h => absurd h (by simp only [List.getElem?_nil, reduceCtorEq, not_false_eq_true])
  | R' :: _, os, 0, h =>
    (Option.some.inj (by simpa only [List.getElem?_cons_zero] using h) : R' = R) ▸ os.1
  | _ :: Rs, os, i + 1, h =>
    Objs.get Rs os.2 i (by simpa only [List.getElem?_cons_succ] using h)

/-- The object at position `i` replaced. -/
def Objs.set {H : HTy} {R : RefTy} : (Rs : List RefTy) → Objs H Rs → (i : Nat) →
    Rs[i]? = some R → MObj H R → Objs H Rs
  | [], os, _, _, _ => os
  | R' :: _, os, 0, h, o =>
    (((Option.some.inj (by simpa only [List.getElem?_cons_zero] using h) : R' = R).symm ▸ o),
      os.2)
  | _ :: Rs, os, i + 1, h, o =>
    (os.1, Objs.set Rs os.2 i (by simpa only [List.getElem?_cons_succ] using h) o)

/-- `o` appended after the objects of `Rs`. -/
def Objs.snoc {H : HTy} {R : RefTy} (o : MObj H R) : (Rs : List RefTy) → Objs H Rs →
    Objs H (Rs ++ [R])
  | [], _ => (o, ())
  | _ :: Rs, os => (os.1, Objs.snoc o Rs os.2)

namespace Heap

variable {H : HTy}

/-- The object a reference names. -/
def get {R : RefTy} (hp : Heap H) (r : HRef H R) : MObj H R := Objs.get H hp r.id r.get?

/-- The object a reference names replaced. -/
def set {R : RefTy} (hp : Heap H) (r : HRef H R) (o : MObj H R) : Heap H :=
  Objs.set H hp r.id r.get? o

/-- A fresh object (`State.alloc`): the heap grows by its type. -/
def alloc {R : RefTy} (hp : Heap H) (o : MObj H R) : Heap (H ++ [R]) × HRef (H ++ [R]) R :=
  let e := List.prefix_append H [R]
  (Objs.snoc (MObj.wk e R o) H (Objs.wk e H hp),
    ⟨H.length, by simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero]⟩)

end Heap

/-! ## Members and elements -/

/-- The value of the first member named `f` (`lookupBy`). -/
def MFields.get {H : HTy} {f : Name} : (fs : List (Name × Ty)) → {T : Ty} → MFields H fs →
    lookupBy f fs = some T → MVal H T
  | [], _, _, h => absurd h (by simp only [lookupBy, reduceCtorEq, not_false_eq_true])
  | (f', T') :: fs, T, x, h =>
    if e : f = f' then
      (SFields.lookupBy_cons_pos e h ▸ (x.1 : MVal H T') : MVal H T)
    else MFields.get fs x.2 (SFields.lookupBy_cons_neg e h)

/-- The first member named `f` replaced (`setBy`). -/
def MFields.set {H : HTy} {f : Name} : (fs : List (Name × Ty)) → {T : Ty} → MFields H fs →
    lookupBy f fs = some T → MVal H T → MFields H fs
  | [], _, x, _, _ => x
  | (f', T') :: fs, _, x, h, v =>
    if e : f = f' then
      (((SFields.lookupBy_cons_pos e h).symm ▸ v : MVal H T'), x.2)
    else (x.1, MFields.set fs x.2 (SFields.lookupBy_cons_neg e h) v)

/-- An array object's elements, either kind.  By `casesOn`, so the kernel
casts nothing (Gate G0, condition 1). -/
def MObj.elems {H : HTy} {R : RefTy} {E : Ty} (a : ArrTy R E) : MObj H R → List (MVal H E) :=
  @ArrTy.casesOn (fun R E _ => MObj H R → List (MVal H E)) R E a
    (fun {_} o => o.1) (fun {_} {_} o => o.1)

theorem MObj.elems_dyn {H : HTy} {E : Ty} (o : MObj H (.array E)) :
    MObj.elems .dyn o = (o : {l : List (MVal H E) // l.length < 2 ^ 256}).1 := rfl
theorem MObj.elems_fixed {H : HTy} {E : Ty} {n : Nat} (o : MObj H (.fixed E n)) :
    MObj.elems .fixed o = (o : {l : List (MVal H E) // l.length = n}).1 := rfl

attribute [irreducible] MObj.elems
attribute [eqns MObj.elems_dyn MObj.elems_fixed] MObj.elems

/-- An array object with element `i` replaced. -/
def MObj.setElem {H : HTy} {R : RefTy} {E : Ty} (a : ArrTy R E) :
    MObj H R → Nat → MVal H E → MObj H R :=
  @ArrTy.casesOn (fun R E _ => MObj H R → Nat → MVal H E → MObj H R) R E a
    (fun {E} o i v =>
      let o : {l : List (MVal H E) // l.length < 2 ^ 256} := o
      (⟨o.1.set i v, by rw [List.length_set]; exact o.2⟩ : MObj H (.array E)))
    (fun {E} {n} o i v =>
      let o : {l : List (MVal H E) // l.length = n} := o
      (⟨o.1.set i v, by rw [List.length_set]; exact o.2⟩ : MObj H (.fixed E n)))

theorem MObj.setElem_dyn {H : HTy} {E : Ty} (o : MObj H (.array E)) (i : Nat) (v : MVal H E) :
    MObj.setElem .dyn o i v =
      let o : {l : List (MVal H E) // l.length < 2 ^ 256} := o
      (⟨o.1.set i v, by rw [List.length_set]; exact o.2⟩ : MObj H (.array E)) := rfl
theorem MObj.setElem_fixed {H : HTy} {E : Ty} {n : Nat} (o : MObj H (.fixed E n)) (i : Nat)
    (v : MVal H E) :
    MObj.setElem .fixed o i v =
      let o : {l : List (MVal H E) // l.length = n} := o
      (⟨o.1.set i v, by rw [List.length_set]; exact o.2⟩ : MObj H (.fixed E n)) := rfl

attribute [irreducible] MObj.setElem
attribute [eqns MObj.setElem_dyn MObj.setElem_fixed] MObj.setElem

namespace Heap

variable {H : HTy}

/-- `mv.f` (`readAddr`'s member arm). -/
def field {s f : Name} {T : Ty} (hp : Heap H) (r : HRef H (.struct s))
    (h : lookupBy f (structDef s) = some T) : MVal H T :=
  MFields.get (structDef s) (hp.get r) h

/-- `mv.f = v`. -/
def setField {s f : Name} {T : Ty} (hp : Heap H) (r : HRef H (.struct s))
    (h : lookupBy f (structDef s) = some T) (v : MVal H T) : Heap H :=
  hp.set r (MFields.set (structDef s) (hp.get r) h v)

/-- `mv[i]` (`readAddr`'s index arm): `none`, a revert, out of bounds. -/
def index {R : RefTy} {E : Ty} (hp : Heap H) (r : HRef H R) (a : ArrTy R E) (i : Int) :
    Option (MVal H E) :=
  if 0 ≤ i then (MObj.elems a (hp.get r))[i.toNat]? else none

/-- `mv[i] = v`: `none`, a revert, out of bounds. -/
def setIndex {R : RefTy} {E : Ty} (hp : Heap H) (r : HRef H R) (a : ArrTy R E) (i : Int)
    (v : MVal H E) : Option (Heap H) :=
  if 0 ≤ i ∧ i.toNat < (MObj.elems a (hp.get r)).length then
    some (hp.set r (MObj.setElem a (hp.get r) i.toNat v))
  else none

/-- `mv.length`. -/
def len {R : RefTy} {E : Ty} (hp : Heap H) (r : HRef H R) (a : ArrTy R E) : Nat :=
  (MObj.elems a (hp.get r)).length

/-- A dynamic array's length is below `2^256`. -/
theorem len_dyn_lt {E : Ty} (hp : Heap H) (r : HRef H (.array E)) : hp.len r .dyn < 2 ^ 256 := by
  unfold len
  rw [MObj.elems_dyn]
  exact (hp.get r : {l : List (MVal H E) // l.length < 2 ^ 256}).2

/-- `mv.length` of a dynamic array, a `uint`. -/
def lenU {E : Ty} (hp : Heap H) (r : HRef H (.array E)) : PrimTy.uint.Denote :=
  Solidity.lenU (hp.len r .dyn) (hp.len_dyn_lt r)

end Heap

/-! ## Storage to memory (`copySt`) -/

/-- A heap grown by allocations, and a value over its typing. -/
structure Grown (H : HTy) (α : HTy → Type) where
  {H' : HTy}
  ext : H <+: H'
  heap : Heap H'
  val : α H'

/-- A grown heap with one more object, the value its reference. -/
def Grown.alloc {H : HTy} {R : RefTy} (g : Grown H (MObj · R)) : Grown H (MVal · (.ref R)) :=
  let a := g.heap.alloc g.val
  ⟨g.ext.trans (List.prefix_append _ _), a.1, a.2⟩

/-- A storage value deep-copied into fresh objects: at each type, from any
heap, given that the type has no mapping. -/
def copyStToMFold : Fold where
  V T := (H : HTy) → Heap H → T.mapFree = true → Grown H (MVal · T)
  F fs := (H : HTy) → Heap H → (∀ fT ∈ fs, fT.2.mapFree = true) → Grown H (MFields · fs)
  L E := (H : HTy) → Heap H → E.mapFree = true → Grown H (fun H' => List (MVal H' E))
  W E n := (H : HTy) → Heap H → E.mapFree = true →
    Grown H (fun H' => {l : List (MVal H' E) // l.length = n})
  M _ := Unit
  prim := fun v H hp _ => ⟨List.prefix_refl H, hp, v⟩
  struct := fun {s} _ ih H hp h =>
    Grown.alloc (R := .struct s)
      (ih H hp (mapFree_structDef s (by simpa only [Ty.mapFree, decide_eq_true_eq] using h)))
  array := fun {E} {_} _ _ hn ie _ H hp h =>
    let g := ie H hp (by simpa only [Ty.mapFree] using h)
    Grown.alloc (R := .array E) ⟨g.ext, g.heap, ⟨g.val.1, by rw [g.val.2]; exact hn⟩⟩
  fixed := fun {E n} _ ie H hp h =>
    Grown.alloc (R := .fixed E n) (ie H hp (by simpa only [Ty.mapFree] using h))
  map := fun _ _ _ _ _ _ h =>
    absurd h (by simp only [Ty.mapFree, Bool.false_eq_true, not_false_eq_true])
  fnil := fun H hp _ => ⟨List.prefix_refl H, hp, ()⟩
  fcons := fun {_} {T} {_} _ _ iv ir H hp h =>
    let g₁ := iv H hp (h _ List.mem_cons_self)
    let g₂ := ir g₁.H' g₁.heap (fun fT hm => h fT (List.mem_cons_of_mem _ hm))
    ⟨g₁.ext.trans g₂.ext, g₂.heap, (MVal.wk g₂.ext T g₁.val, g₂.val)⟩
  lnil := fun H hp _ => ⟨List.prefix_refl H, hp, []⟩
  lcons := fun {E} _ _ iv ir H hp h =>
    let g₁ := iv H hp h
    let g₂ := ir g₁.H' g₁.heap h
    ⟨g₁.ext.trans g₂.ext, g₂.heap, MVal.wk g₂.ext E g₁.val :: g₂.val⟩
  wnil := fun H hp _ => ⟨List.prefix_refl H, hp, ⟨[], rfl⟩⟩
  wcons := fun {E} {_} _ _ iv ir H hp h =>
    let g₁ := iv H hp h
    let g₂ := ir g₁.H' g₁.heap h
    ⟨g₁.ext.trans g₂.ext, g₂.heap,
      ⟨MVal.wk g₂.ext E g₁.val :: g₂.val.1, congrArg (· + 1) g₂.val.2⟩⟩
  mnil := ()
  mcons := fun _ _ _ _ _ => ()

/-- A storage value deep-copied into fresh objects (`copyStToM`), members and
elements first. -/
def SVal.copyStToM {H : HTy} (hp : Heap H) {T : Ty} (v : SVal T) (h : T.mapFree = true) :
    Grown H (MVal · T) :=
  (v.fold copyStToMFold : (H : HTy) → Heap H → T.mapFree = true → Grown H (MVal · T)) H hp h

def SFields.copyStToM {H : HTy} (hp : Heap H) {fs : List (Name × Ty)} (x : SFields fs)
    (h : ∀ fT ∈ fs, fT.2.mapFree = true) : Grown H (MFields · fs) :=
  (x.fold copyStToMFold :
    (H : HTy) → Heap H → (∀ fT ∈ fs, fT.2.mapFree = true) → Grown H (MFields · fs)) H hp h

def SList.copyStToM {H : HTy} (hp : Heap H) {E : Ty} (l : SList E) (h : E.mapFree = true) :
    Grown H (fun H' => List (MVal H' E)) :=
  (l.fold copyStToMFold :
    (H : HTy) → Heap H → E.mapFree = true → Grown H (fun H' => List (MVal H' E))) H hp h

def SVec.copyStToM {H : HTy} (hp : Heap H) {E : Ty} {n : Nat} (l : SVec E n)
    (h : E.mapFree = true) : Grown H (fun H' => {l : List (MVal H' E) // l.length = n}) :=
  (l.fold copyStToMFold : (H : HTy) → Heap H → E.mapFree = true →
    Grown H (fun H' => {l : List (MVal H' E) // l.length = n})) H hp h

theorem SVal.copyStToM_prim {H : HTy} (hp : Heap H) {p : PrimTy} (v : p.Denote)
    (h : (Ty.prim p).mapFree = true) :
    SVal.copyStToM hp (.prim v) h = ⟨List.prefix_refl H, hp, v⟩ := rfl
theorem SVal.copyStToM_struct {H : HTy} (hp : Heap H) {s : Name} (fs : SFields (structDef s))
    (h : (Ty.ref (.struct s)).mapFree = true) :
    SVal.copyStToM hp (.struct fs) h =
      Grown.alloc (R := .struct s) (SFields.copyStToM hp fs
        (mapFree_structDef s (by simpa only [Ty.mapFree, decide_eq_true_eq] using h))) := rfl
theorem SVal.copyStToM_array {H : HTy} (hp : Heap H) {E : Ty} {n : Nat} (e : SVec E n)
    (sh : SList E) (hn : n < 2 ^ 256) (h : (Ty.ref (.array E)).mapFree = true) :
    SVal.copyStToM hp (.array e sh hn) h =
      let g := SVec.copyStToM hp e (by simpa only [Ty.mapFree] using h)
      Grown.alloc (R := .array E) ⟨g.ext, g.heap, ⟨g.val.1, by rw [g.val.2]; exact hn⟩⟩ :=
  rfl
theorem SVal.copyStToM_fixed {H : HTy} (hp : Heap H) {E : Ty} {n : Nat} (e : SVec E n)
    (h : (Ty.ref (.fixed E n)).mapFree = true) :
    SVal.copyStToM hp (.fixed e) h =
      Grown.alloc (R := .fixed E n) (SVec.copyStToM hp e (by simpa only [Ty.mapFree] using h)) :=
  rfl
theorem SVal.copyStToM_map {H : HTy} (hp : Heap H) {K : PrimTy} {U : Ty} (m : SMap U) (d : SVal U)
    (h : (Ty.ref (.mapping K U)).mapFree = true) :
    SVal.copyStToM hp (.map m d) h =
      absurd h (by simp only [Ty.mapFree, Bool.false_eq_true, not_false_eq_true]) := rfl
theorem SFields.copyStToM_nil {H : HTy} (hp : Heap H) (h : ∀ fT ∈ ([] : List (Name × Ty)),
    fT.2.mapFree = true) : SFields.copyStToM hp .nil h = ⟨List.prefix_refl H, hp, ()⟩ := rfl
theorem SFields.copyStToM_cons {H : HTy} (hp : Heap H) {f : Name} {T : Ty}
    {fs : List (Name × Ty)} (v : SVal T) (rest : SFields fs)
    (h : ∀ fT ∈ (f, T) :: fs, fT.2.mapFree = true) :
    SFields.copyStToM hp (.cons v rest) h =
      let g₁ := SVal.copyStToM hp v (h _ List.mem_cons_self)
      let g₂ := SFields.copyStToM g₁.heap rest (fun fT hm => h fT (List.mem_cons_of_mem _ hm))
      ⟨g₁.ext.trans g₂.ext, g₂.heap, (MVal.wk g₂.ext T g₁.val, g₂.val)⟩ := rfl
theorem SList.copyStToM_nil {H : HTy} (hp : Heap H) {E : Ty} (h : E.mapFree = true) :
    SList.copyStToM hp .nil h = ⟨List.prefix_refl H, hp, []⟩ := rfl
theorem SList.copyStToM_cons {H : HTy} (hp : Heap H) {E : Ty} (v : SVal E) (rest : SList E)
    (h : E.mapFree = true) :
    SList.copyStToM hp (.cons v rest) h =
      let g₁ := SVal.copyStToM hp v h
      let g₂ := SList.copyStToM g₁.heap rest h
      ⟨g₁.ext.trans g₂.ext, g₂.heap, MVal.wk g₂.ext E g₁.val :: g₂.val⟩ := rfl
theorem SVec.copyStToM_nil {H : HTy} (hp : Heap H) {E : Ty} (h : E.mapFree = true) :
    SVec.copyStToM hp .nil h = ⟨List.prefix_refl H, hp, ⟨[], rfl⟩⟩ := rfl
theorem SVec.copyStToM_cons {H : HTy} (hp : Heap H) {E : Ty} {n : Nat} (v : SVal E)
    (rest : SVec E n) (h : E.mapFree = true) :
    SVec.copyStToM hp (.cons v rest) h =
      let g₁ := SVal.copyStToM hp v h
      let g₂ := SVec.copyStToM g₁.heap rest h
      ⟨g₁.ext.trans g₂.ext, g₂.heap,
        ⟨MVal.wk g₂.ext E g₁.val :: g₂.val.1, congrArg (· + 1) g₂.val.2⟩⟩ := rfl

attribute [irreducible] SVal.copyStToM SFields.copyStToM SList.copyStToM SVec.copyStToM
attribute [eqns SVal.copyStToM_prim SVal.copyStToM_struct SVal.copyStToM_array
  SVal.copyStToM_fixed SVal.copyStToM_map] SVal.copyStToM
attribute [eqns SFields.copyStToM_nil SFields.copyStToM_cons] SFields.copyStToM
attribute [eqns SList.copyStToM_nil SList.copyStToM_cons] SList.copyStToM
attribute [eqns SVec.copyStToM_nil SVec.copyStToM_cons] SVec.copyStToM

/-- A fresh default object (`allocDefault`). -/
def Heap.allocDefault {H : HTy} (hp : Heap H) (R : RefTy) (h : (Ty.ref R).mapFree = true) :
    Grown H (MVal · (.ref R)) :=
  (SVal.dflt (.ref R)).copyStToM hp h

/-! ## Memory to storage (`copyMem`) -/

/-- `n` values of a list of length `n`, mapped into a vector. -/
def SVec.ofLen {α : Type} {E : Ty} (f : α → SVal E) : (n : Nat) → (l : List α) → l.length = n →
    SVec E n
  | 0, [], _ => .nil
  | n + 1, x :: xs, h => .cons (f x) (SVec.ofLen f n xs (Nat.succ.inj h))
  | 0, _ :: _, h => absurd h (by simp only [List.length_cons, Nat.add_one_ne_zero,
      not_false_eq_true])
  | _ + 1, [], h => absurd h (by simp only [List.length_nil, Nat.zero_ne_add_one,
      not_false_eq_true])

section CopyMem

variable {H : HTy} (hp : Heap H)

/-- A struct object's members copied, given the copies below rank `k`. -/
def MFields.copyBelow (k : Nat) (ih : (T : Ty) → tyRank T < k → MVal H T → SVal T) :
    (fs : List (Name × Ty)) → fieldsRank fs < k → MFields H fs → SFields fs
  | [], _, _ => .nil
  | (_, T) :: fs, h, x =>
    .cons (ih T (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) h) x.1)
      (MFields.copyBelow k ih fs (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) h) x.2)

mutual
/-- The copies of rank at most `k`, given those below. -/
def MVal.copyAt (k : Nat) (ih : (T : Ty) → tyRank T < k → MVal H T → SVal T) :
    (T : Ty) → tyRank T < k + 1 → MVal H T → SVal T
  | .prim _, _, v => .prim v
  | .ref R, h, r => MVal.copyRefAt k ih R h r

def MVal.copyRefAt (k : Nat) (ih : (T : Ty) → tyRank T < k → MVal H T → SVal T) :
    (R : RefTy) → tyRank (.ref R) < k + 1 → HRef H R → SVal (.ref R)
  | .struct s, h, r =>
    .struct (MFields.copyBelow k ih (structDef s)
      (Nat.lt_of_lt_of_le (Semantics.structDef_rank_lt s) (Nat.le_of_lt_succ h)) (hp.get r))
  | .array E, h, r =>
    let o : {l : List (MVal H E) // l.length < 2 ^ 256} := hp.get r
    .array (SVec.ofList (o.1.map (MVal.copyAt k ih E (by simpa only [tyRank] using h)))) .nil
      (by rw [List.length_map]; exact o.2)
  | .fixed E n, h, r =>
    let o : {l : List (MVal H E) // l.length = n} := hp.get r
    .fixed (SVec.ofLen (MVal.copyAt k ih E (Nat.lt_of_succ_lt (by simpa only [tyRank] using h)))
      n o.1 o.2)
  | .mapping _ _, _, r => (hp.get r : Empty).elim
end

/-- The copies below rank `k`. -/
def MVal.copyBelow : (k : Nat) → (T : Ty) → tyRank T < k → MVal H T → SVal T
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | k + 1, T, h, v => MVal.copyAt hp k (MVal.copyBelow k) T h v

/-- A memory value deep-copied to storage (`copyMToSt`, `copyMem`). -/
def MVal.copyMToSt {T : Ty} (v : MVal H T) : SVal T :=
  MVal.copyBelow hp (rankBound T + 1) T (Nat.lt_succ_of_le (tyRank_le_rankBound T)) v

end CopyMem

/-- The empty heap. -/
def Heap.empty : Heap [] := ()

end Solidity
