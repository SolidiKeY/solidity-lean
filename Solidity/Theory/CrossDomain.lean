import Solidity.Theory.Storage
import Solidity.Theory.Memory

/-!
# `structMemoryRules.key` as a term algebra — the two copy views

`Theory/Storage.lean` is the storage algebra and `Theory/Memory.lean` the
memory one; neither mentions the other, which is why a copy *between* them has
had no term-level spelling (`docs/lean-key-rule-map.md`, "structMemoryRules.key
→ not modelled").  This module is that spelling.

## What the views are

A copy in either direction is lazy in KeY: nothing is walked at the moment of
the assignment.  Instead the copied-to side gets a **view** of the copied-from
one, and the reads resolve through it:

* `copyMem(mtSt, mem, id)` is a `Struct` that answers every `find` by a
  `readR` into `mem` from `id` (`sections/memory-to-storage.tex`);
* `copySt(mem, r, st)` is a `Memory` that answers every `read` below root `r`
  by a `find` into `st` (`sections/storage-to-memory.tex`).

## Why they are their own sorts

Putting `copyMem` into `Struct` and `copySt` into `Memory` would make the two
inductives mutually recursive, and so the two files one file: every function
and every proof in both would gain an arm for a constructor that is not part of
either theory.  The views are not part of either theory — upstream they are a
third `.key` file, loaded on top of both.  So they are a third sort here too:
`XStruct` is `Struct` with a `copyMem` leaf, `XMemory` is `Memory` with a
`copySt` node, and the plain algebras embed into them by `of`.

The paper's own presentation is the same shape: the copy rules are stated once,
applied once at the copy, and the read continues in whichever theory the view
hands it to.  What this does *not* model, accordingly, is a view nested in a
view — a `copySt` of a struct that is itself a `copyMem`.  No worked example
nests one, and upstream's taclets do not rewrite under one either.

## Sorts and casts

Both algebras are sort-free with the cast resolving the read
(`Theory/Memory.lean`), so the conversions between a `StValue` and a
`MemValue` are where the paper's sort index goes.  `StValue.toMemValue` sends
a primitive to itself and a struct to `dflt`, which is what makes
`readCopyStIdentity` a corollary of `defaultDefIdentity` rather than a separate
recursion: a *reference* member of a copied struct reads as the identity one
field further down, exactly as a reference member of a fresh root does.
-/

namespace Solidity
namespace Theory

open Semantics

/-! ## Conversions between the two value sorts -/

/-- A storage value as a memory slot.  A struct becomes `dflt` so that the
cast at the `Identity` sort manufactures `idC(r, flds·a)` -- see the module
docstring. -/
def StValue.toMemValue : StValue -> MemValue
  | .prim p => .prim p
  | .st _ => .dflt

/-- A memory slot as a storage value, at the sort the read was taken at.  An
identity has no storage image of its own; `findCopyMem` keeps reading through
the view, so the identity arm is handled by `XStruct.find` and never reaches
here. -/
def MemValue.toStValue : MemValue -> StValue
  | .prim p => .prim p
  | .ident _ => .st .mtSt
  | .dflt => .st .mtSt

@[simp] theorem StValue.toMemValue_prim (p : PrimVal) :
    StValue.toMemValue (.prim p) = .prim p := rfl

@[simp] theorem StValue.toMemValue_st (s : Struct) :
    StValue.toMemValue (.st s) = .dflt := rfl

@[simp] theorem MemValue.toStValue_prim (p : PrimVal) :
    MemValue.toStValue (.prim p) = .prim p := rfl

/-! ## `copyMem`: a struct that is a memory image -/

mutual
  /-- `Struct` with the `copyMem(mtSt, mem, id)` leaf.  `of` is the embedding
  of the plain algebra; `storeSt` is its store, re-declared here because its
  payload may now be a view. -/
  inductive XStruct where
    | of (s : Struct)
    | storeSt (s : XStruct) (a : Seg) (v : XValue)
    | copyMem (mem : Memory) (id : Identity)
    deriving Repr

  /-- `StValue` over `XStruct`. -/
  inductive XValue where
    | prim (p : PrimVal)
    | st (s : XStruct)
    deriving Repr
end

namespace XValue

/-- `(Struct) v`, as `Theory/Storage.lean`'s cast. -/
def asStruct : XValue -> XStruct
  | st s => s
  | prim _ => .of .mtSt

/-- `(int) v`. -/
def asInt : XValue -> Int
  | prim (PrimVal.int v) => v
  | _ => 0

/-- `(bool) v`. -/
def asBool : XValue -> Bool
  | prim (PrimVal.bool b) => b
  | _ => false

/-- A plain storage value in the extended sort. -/
def ofSt : StValue -> XValue
  | .prim p => .prim p
  | .st s => .st (.of s)

/-- A memory slot in the extended sort.  A slot holding an identity is the
*sub-view*: reading further below it keeps reading memory, which is the whole
content of `copyMem` being lazy. -/
def ofMem (mem : Memory) : MemValue -> XValue
  | .prim p => .prim p
  | .ident i => .st (.copyMem mem i)
  | .dflt => .st (.of .mtSt)

@[simp] theorem asStruct_st (s : XStruct) : asStruct (st s) = s := rfl
@[simp] theorem asStruct_prim (p : PrimVal) : asStruct (prim p) = .of .mtSt := rfl
@[simp] theorem ofSt_prim (p : PrimVal) : ofSt (.prim p) = prim p := rfl
@[simp] theorem ofSt_st (s : Struct) : ofSt (.st s) = st (.of s) := rfl
@[simp] theorem ofMem_prim (mem : Memory) (p : PrimVal) :
    ofMem mem (.prim p) = prim p := rfl
@[simp] theorem ofMem_ident (mem : Memory) (i : Identity) :
    ofMem mem (.ident i) = st (.copyMem mem i) := rfl

/-- The embedding commutes with the cast, which is what lets a chain in the
extended sort take a step of the plain algebra without leaving it. -/
@[simp] theorem asStruct_ofSt (v : StValue) :
    asStruct (ofSt v) = .of (StValue.asStruct v) := by cases v <;> rfl

end XValue

namespace XStruct

/-- `selectSt<[α]>(st, a)` in the extended sort.  On a view this is
`findCopyMem` at a one-segment path, which `readREmpty` says is one `read`. -/
def selectSt (h : List (Nat × MObj)) : XStruct -> Seg -> XValue
  | .of s, a => XValue.ofSt (StValue.selectSt s a)
  | .storeSt s a1 v, a2 => if a1 = a2 then v else selectSt h s a2
  | .copyMem mem id, a => XValue.ofMem mem (Memory.readIn h mem id a)

/-- `find<[α]>(st, flds)` in the extended sort.  The `copyMem` arm is
`findCopyMem`, stated as the definition: the whole remaining path goes to
`readR` in one step, as the taclet does. -/
def find (h : List (Nat × MObj)) : XStruct -> List Seg -> XValue
  | .copyMem mem id, flds => XValue.ofMem mem (Memory.readR h mem id flds)
  | .of s, flds => XValue.ofSt (StValue.find s flds)
  | .storeSt s a v, [] => .st (.storeSt s a v)
  | .storeSt s a v, [b] => selectSt h (.storeSt s a v) b
  | .storeSt s a v, b :: c :: flds =>
      find h (XValue.asStruct (selectSt h (.storeSt s a v) b)) (c :: flds)

/-- `storeSt(st, a, v)` with a plain struct underneath -- the shape a chain
writes when only one member of an otherwise ordinary store is a view. -/
abbrev store (s : Struct) (a : Seg) (v : XValue) : XStruct :=
  .storeSt (.of s) a v

/-! ### The taclets, as the plain algebra's twins -/

/-- `selectSt<[α]>(storeSt(st, a1, v), a2)` -- `selectOnStore`. -/
@[simp] theorem selectOnStore (h : List (Nat × MObj)) (s : XStruct)
    (a1 a2 : Seg) (v : XValue) :
    selectSt h (.storeSt s a1 v) a2 = if a1 = a2 then v else selectSt h s a2 := rfl

/-- The embedding commutes with `selectSt`. -/
@[simp] theorem selectSt_of (h : List (Nat × MObj)) (s : Struct) (a : Seg) :
    selectSt h (.of s) a = XValue.ofSt (StValue.selectSt s a) := rfl

/-- `find<[α]>(st, nil) ⇝ (α) st` -- `findEmptyPath`.  The view arm needs
`readREmptyPath`: reading the empty path out of `mem` from `id` is `id`, whose
storage image is the view itself. -/
@[simp] theorem findEmptyPath (h : List (Nat × MObj)) (s : XStruct) :
    find h s [] = .st s := by
  cases s <;> rfl

/-- `find<[α]>(st, ⟨a⟩) ⇝ selectSt<[α]>(st, a)` -- `findSingleton`, on a term
that is not a view. -/
theorem findSingleton (h : List (Nat × MObj)) (s : XStruct) (a : Seg)
    (hs : ∀ mem id, s ≠ .copyMem mem id) : find h s [a] = selectSt h s a := by
  cases s with
  | of _ => rfl
  | storeSt _ _ _ => rfl
  | copyMem mem id => exact absurd rfl (hs mem id)

/-- The spine step of `find`, on a term that is not a view -- `findPath`. -/
theorem findPath (h : List (Nat × MObj)) (s : XStruct) (a b : Seg)
    (flds : List Seg) (hs : ∀ mem id, s ≠ .copyMem mem id) :
    find h s (a :: b :: flds) =
      find h (XValue.asStruct (selectSt h s a)) (b :: flds) := by
  cases s with
  | of _ => simp only [find, selectSt, XValue.asStruct_ofSt]; rfl
  | storeSt _ _ _ => rfl
  | copyMem mem id => exact absurd rfl (hs mem id)

/-! ### `findCopyMem`

`find<[α]>(copyMem(mtSt, mem, id), flds) ⇝ readR<[α]>(mem, id, flds)`
(`sections/memory-to-storage.tex`).  The one rule of the view, and the
decisive step of every memory-to-storage example: it is what turns a storage
read into a memory read without either theory having walked anything. -/

/-- **`findCopyMem`** — the whole remaining path goes to `readR` in one step,
at every path including the empty one, where it agrees with `findEmptyPath`
through `readREmptyPath`. -/
@[simp] theorem findCopyMem (h : List (Nat × MObj)) (mem : Memory)
    (id : Identity) (flds : List Seg) :
    find h (.copyMem mem id) flds =
      XValue.ofMem mem (Memory.readR h mem id flds) := by
  cases flds with
  | nil => rfl
  | cons _ rest => cases rest <;> rfl

end XStruct

/-! ## `copySt`: a memory that is a storage image -/

/-- `Memory` with the `copySt(mem, r, st)` node. -/
inductive XMemory where
  | of (mem : Memory)
  | copySt (mem : XMemory) (r : Nat) (s : Struct)
  deriving Repr

namespace XMemory

open MemValue

/-- `read<[α]>(mem, id, a)` in the extended sort.  Below the copied root the
read is answered out of the struct; anywhere else it passes through. -/
def readIn (h : List (Nat × MObj)) : XMemory -> Identity -> Seg -> MemValue
  | .of m, id, a => Memory.readIn h m id a
  | .copySt m r s, id, a =>
      if r = id.root then StValue.toMemValue (StValue.find s (id.path ++ [a]))
      else readIn h m id a

/-- `read<[Identity]>(mem, id, a)`. -/
def readId (h : List (Nat × MObj)) (mem : XMemory) (id : Identity) (a : Seg) :
    Identity :=
  (readIn h mem id a).asIdentity id a

/-- `readR<[α]>(mem, id, flds)`, as `Theory/Memory.lean`'s. -/
def readR (h : List (Nat × MObj)) (mem : XMemory) (id : Identity) :
    List Seg -> MemValue
  | [] => MemValue.ident id
  | [a] => readIn h mem id a
  | a :: b :: rest => readR h mem (readId h mem id a) (b :: rest)

/-! ### The three taclets of `copySt` -/

/-- **`readCopySt`** — a read below the copied root is a `find` into the
copied struct (`sections/storage-to-memory.tex`). -/
@[simp] theorem readCopySt (h : List (Nat × MObj)) (mem : XMemory) (r : Nat)
    (s : Struct) (flds : List Seg) (a : Seg) :
    readIn h (.copySt mem r s) (.idC r flds) a =
      StValue.toMemValue (StValue.find s (flds ++ [a])) := by
  simp [readIn, Identity.root, Identity.path]

/-- **`readCopyStIdentity`** — the same read at the `Identity` sort is the
identity one field further down, so a reference member of a copied struct
exists as soon as its parent does.  The hypothesis is the sort: the member is
struct-valued. -/
theorem readCopyStIdentity (h : List (Nat × MObj)) (mem : XMemory) (r : Nat)
    (s : Struct) (flds : List Seg) (a : Seg) {inner : Struct}
    (hs : StValue.find s (flds ++ [a]) = .st inner) :
    readId h (.copySt mem r s) (.idC r flds) a = .idC r (flds ++ [a]) := by
  simp [readId, readCopySt, hs, MemValue.asIdentity, Identity.extend]

/-- **`readCopyStOther`** — a read below any other root does not see the
copy. -/
theorem readCopyStOther (h : List (Nat × MObj)) (mem : XMemory) (r1 r2 : Nat)
    (s : Struct) (flds : List Seg) (a : Seg) (hne : r1 ≠ r2) :
    readIn h (.copySt mem r1 s) (.idC r2 flds) a = readIn h mem (.idC r2 flds) a := by
  simp [readIn, Identity.root, hne]

/-- The embedding commutes with `read`. -/
@[simp] theorem readIn_of (h : List (Nat × MObj)) (m : Memory) (id : Identity)
    (a : Seg) : readIn h (.of m) id a = Memory.readIn h m id a := rfl

end XMemory

end Theory
end Solidity
