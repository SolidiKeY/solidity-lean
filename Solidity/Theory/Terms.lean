import Solidity.Semantics
import Solidity.DecEq

/-!
# The term sorts of solkey's data-structure theories

`structRules.key`, `memoryRules.key` and `structMemoryRules.key` declare one
signature between them, and the third one ties the first two together:

```
Struct copyMem(Struct, Memory, Identity)      -- memory to storage
Memory copySt(Memory, IdentityPrim, Struct)   -- storage to memory
```

So `Struct` mentions `Memory` and `Memory` mentions `Struct`, and in Lean that
is one mutual inductive.  This module is it, together with the readers that are
mutual for the same reason — `find` on a `copyMem` view is a `readR` into
memory, and `read` on a `copySt` view is a `find` into storage.

`Theory/Storage.lean`, `Theory/Memory.lean` and `Theory/CrossDomain.lean` are
the taclet files above it, each still reading against its own `.key` line by
line.  Only what has to be one block is here.

## What is in the block and what is not

`Identity` and `MemValue` stay outside: neither mentions `Memory`, and a
three-sort block is what keeps `deriving DecidableEq` cheap — `Theory/Storage.lean`'s
`Sanity` examples close by `decide`.  The invariant that keeps it working is
that **no constructor in the block takes a `List` or `Option` of a sort in the
block**: that would make it a *nested* inductive, and Lean's `DecidableEq`
deriver declines those.  `Memory.pre` takes `List (Nat × MObj)`, which is
outside.

## The pre-state leaf carries its heap

Upstream `readIn` took the heap as a parameter.  Once `find` calls `readR` the
parameter would have to be threaded through every storage function too, so the
heap moved onto the leaf that actually reads it.  The algebra above is
unchanged: `pre h` is still "the interpreter's heap, opaque", and every other
constructor is still a free term.

## Three arms with no taclet upstream

`selectSt`, `storeAt` (`Theory/Storage.lean`) and `delNode` (likewise) have no
`.key` rule for a `copyMem` view, so what they do there is ours to choose.
Each is chosen so that the rule which *does* exist subsumes it:

* `selectSt (copyMem mem id) a` pushes the view down — `copyMem mem (id·a)` —
  and reads nothing.  It is reachable only where `findCopyMem` did not already
  answer, and it is what keeps `selectSt` structural on `Struct` alone, which
  is what the termination argument below needs.
* `storeAt` puts a `storeSt` shadow node *over* the view rather than replacing
  it.  Replacing it would destroy the view and make `find_save_frame` false.
* `delNode` answers `mtSt`: it is eager here (`Theory/Storage.lean`), so it
  cannot walk a view whose members it does not know, and every member of a
  deleted node reads its default anyway.

## A view inside a view

`find` on a `copyMem` is a `readR` into memory, and `read` on a `copySt` is a
`find` into storage, so the two would be mutually recursive — and not
structurally, because the path *grows* on the way in (`readCopySt` reads
`flds ++ [a]`).  A lexicographic measure closes it, but well-founded recursion
gives up definitional unfolding, and `decide` on a closed term is how half the
taclets here are checked (`Sanity` below, `Examples/Solkey/Rules.lean`).

So the cycle is cut instead: `readIn` reads its copied struct with **`findSt`**,
the read that does not cross back into memory, and everything stays structural.
What that gives up is a view nested in a view — a `copySt` of a struct that is
itself a `copyMem`.  No worked example nests one, upstream has no taclet that
rewrites under one, and `find_eq_findSt` below says the two readers agree
wherever there is no nesting.
-/

namespace Solidity
namespace Theory

open Semantics

/-! ## Identities

`\unique Identity idC(IdentityPrim, List)` (`memoryRules.key`): the identity
reached from a root along a path of fields.  `\unique` is injectivity, which
`DecidableEq` supplies — `memoryExample2` closes on exactly that. -/

/-- `IdentityPrim` — a sort of its own in `memoryHeader.key`, not a number:
it is what `addM` allocates, what `new` tests, and what `idC` pairs with a
path.  The interpreter names objects by `Nat`, so the wrapper is where the two
meet and `toNat` is the only place the number is visible. -/
structure IdentityPrim where
  ofNat ::
  toNat : Nat
  deriving Repr, DecidableEq

inductive Identity where
  | idC (root : IdentityPrim) (path : List Seg)
  deriving Repr, DecidableEq

namespace Identity

/-- `idCC(idp)` — the root itself, as an identity. -/
@[match_pattern] abbrev idCC (r : IdentityPrim) : Identity := .idC r []

/-- `idC(idp, consr(flds, a))`: the identity one field further down. -/
def extend : Identity -> Seg -> Identity
  | .idC r p, a => .idC r (p ++ [a])

/-- The root a path identity hangs from. -/
def root : Identity -> IdentityPrim
  | .idC r _ => r

@[simp] theorem root_idC (r : IdentityPrim) (p : List Seg) :
    (Identity.idC r p).root = r := rfl

/-- The path from the root. -/
def path : Identity -> List Seg
  | .idC _ p => p

@[simp] theorem path_idC (r : IdentityPrim) (p : List Seg) :
    (Identity.idC r p).path = p := rfl

@[simp] theorem extend_idC (r : IdentityPrim) (p : List Seg) (a : Seg) :
    (Identity.idC r p).extend a = .idC r (p ++ [a]) := rfl

end Identity

/-! ## Memory values

A memory slot's contents (`memoryHeader.key`: `Prim, Identity ⊑ MemValue`).
`dflt` is `defaultValue<[α]>`/`defVal`, resolved on read. -/

inductive MemValue where
  | prim (p : PrimVal)
  | ident (i : Identity)
  | dflt
  deriving Repr, DecidableEq

/-- An interpreter slot value as a `MemValue`: the interpreter's resolved
`Nat` names the root of a path identity with an empty path, which is what
`Update/Theory.lean` writes and what `resolve` inverts. -/
def MVal.toMemValue : MVal -> MemValue
  | .prim p => .prim p
  | .ref n => .ident (.idCC (.ofNat n))

namespace MemValue

/-! ### Casts

`default<[α]>(idC(idp, flds), a)` is resolved by the sort the read is taken
at, and the two sorts answer differently: a primitive member of a fresh root
reads as the primitive default, a *reference* member reads as the identity one
field further down.  That second one is the whole of the paper's "a reference
member of a fresh root reads as the identity reached by extending the path, so
the struct it points to exists as soon as its parent does". -/

/-- `default<[prim]>(idC(idp, flds), a) ⇝ defaultValue<[prim]>` — the cast
that resolves a sort-free default at a primitive sort. -/
def asPrim : MemValue -> MVal
  | prim p => .prim p
  | ident _ => MVal.int 0
  | dflt => MVal.int 0

/-- `default<[Identity]>(idC(idp, flds), a) ⇝ idC(idp, consr(flds, a))` — the
cast at the `Identity` sort, which needs the location the read was taken at
and is why it takes `loc` and `a`. -/
def asIdentity : MemValue -> Identity -> Seg -> Identity
  | ident i, _, _ => i
  | prim _, loc, a => loc.extend a
  | dflt, loc, a => loc.extend a

end MemValue

/-! ## The three sorts -/

mutual
  /-- `structHeader.key`: `Struct ⊑ StValue`, `\unique Struct mtSt`,
  `Struct storeSt(Struct, Field, StValue)`, plus `structMemoryRules.key`'s
  `copyMem(mtSt, mem, id)` — the lazy view of a memory object as storage.

  KeY passes `mtSt` as `copyMem`'s first argument everywhere, so the view is a
  leaf here rather than a node over another struct. -/
  inductive Struct where
    | mtSt
    | storeSt (st : Struct) (a : Seg) (v : StValue)
    | copyMem (mem : Memory) (id : Identity)
    deriving Repr

  /-- `solidityDLHeader.key`: `Prim ⊑ StValue`; `st` is the injection
  `Struct ⊑ StValue`. -/
  inductive StValue where
    | prim (p : PrimVal)
    | st (s : Struct)
    deriving Repr

  /-- A term of solkey's memory theory, plus `structMemoryRules.key`'s
  `copySt(mem, idp, st)` — the lazy view of a storage struct as a memory
  object under a root. -/
  inductive Memory where
    /-- `\unique Memory mtMem`. -/
    | mtMem
    /-- The pre-state heap as an opaque leaf — the reason this algebra, unlike
    the storage one, is a theory of terms *over a concrete state*. -/
    | pre (h : List (Nat × MObj))
    /-- `write(mem, id, a, v)`. -/
    | write (mem : Memory) (id : Identity) (a : Seg) (v : MemValue)
    /-- `addM(mem, idp)`, carrying the allocated type beside the root: the one
    place this algebra is eager where KeY is lazy, because
    `Semantics.allocDefault` materializes the object. -/
    | addM (mem : Memory) (idp : IdentityPrim) (ty : RefTy)
    /-- `copySt(mem, idp, st)` — reads below `idp` are answered out of `st`. -/
    | copySt (mem : Memory) (idp : IdentityPrim) (s : Struct)
    deriving Repr
end

deriving instance DecidableEq for Struct, StValue, Memory

namespace StValue

open Struct

@[match_pattern] abbrev int (v : Int) : StValue := .prim (.int v)
@[match_pattern] abbrev bool (b : Bool) : StValue := .prim (.bool b)

/-! ### Casts

`cast<[Struct]>` and the `Prim` casts of `cast.key`/`memoryRules.key`.  KeY
deletes a cast on a well-sorted argument (`castDel`); these are total, so the
ill-sorted cases get the sort's default. -/

/-- `(Struct) v`. -/
def asStruct : StValue -> Struct
  | st s => s
  | prim _ => mtSt

/-- `(int) v`. -/
def asInt : StValue -> Int
  | prim (PrimVal.int v) => v
  | _ => 0

/-- `(bool) v`. -/
def asBool : StValue -> Bool
  | prim (PrimVal.bool b) => b
  | _ => false

@[simp] theorem asStruct_st (s : Struct) : asStruct (st s) = s := rfl
@[simp] theorem asStruct_prim (q : PrimVal) : asStruct (prim q) = mtSt := rfl
@[simp] theorem defaultValueStruct : asStruct (st mtSt) = mtSt := rfl
@[simp] theorem defaultValueInt : asInt (st mtSt) = 0 := rfl
@[simp] theorem defaultValueBool : asBool (st mtSt) = false := rfl

/-! ### Across the two value sorts

Both algebras are sort-free with the cast resolving the read, so these two
conversions are where the paper's sort index goes.  A struct becomes `dflt` so
that `defaultDefIdentity` manufactures `idC(r, flds·a)` on the read — which is
`readCopyStIdentity`, without a recursion of its own. -/

/-- A storage value as a memory slot. -/
def toMemValue : StValue -> MemValue
  | .prim p => .prim p
  | .st _ => .dflt

end StValue

namespace MemValue

/-- A memory slot as a storage value.  A slot holding an identity is the
*sub-view*: reading further below it keeps reading memory, which is the whole
content of `copyMem` being lazy. -/
def ofView (mem : Memory) : MemValue -> StValue
  | .prim p => .prim p
  | .ident i => .st (.copyMem mem i)
  | .dflt => .st Struct.mtSt

@[simp] theorem ofView_prim (mem : Memory) (p : PrimVal) :
    ofView mem (.prim p) = .prim p := rfl
@[simp] theorem ofView_ident (mem : Memory) (i : Identity) :
    ofView mem (.ident i) = .st (Struct.copyMem mem i) := rfl
@[simp] theorem ofView_dflt (mem : Memory) :
    ofView mem .dflt = .st Struct.mtSt := rfl

end MemValue

namespace Struct

/-- `induction` does not support a mutual inductive; this is the one-sort
recursor, which is all the `Struct`-recursive proofs need — none of them
descends into a stored value or into a view's memory. -/
theorem inductionOn {motive : Struct -> Prop} (h0 : motive mtSt)
    (h1 : forall s a v, motive s -> motive (storeSt s a v))
    (h2 : forall mem id, motive (copyMem mem id)) : forall s, motive s
  | mtSt => h0
  | storeSt s a v => h1 s a v (inductionOn h0 h1 h2 s)
  | copyMem mem id => h2 mem id

end Struct

namespace StValue

open Struct

/-! ## `selectSt` -/

/-- `selectSt<[α]>(st, a)`: the outermost store at `a`, or the default.  On a
view it pushes the view down and reads nothing — see the module docstring. -/
def selectSt : Struct -> Seg -> StValue
  | mtSt, _ => .st mtSt
  | storeSt s a1 v, a2 => if a1 = a2 then v else selectSt s a2
  | Struct.copyMem mem id, a => .st (Struct.copyMem mem (id.extend a))

/-- `find<[α]>(st, flds)` on a storage term that holds no memory view: the
read `readCopySt` takes into a copied struct.  `find` below is this one plus
the arm that crosses into memory, and `find_eq_findSt` says they agree
wherever nothing is nested. -/
def findSt : Struct -> List Seg -> StValue
  | s, [] => .st s
  | s, [a] => selectSt s a
  | s, a :: b :: flds => findSt ((selectSt s a).asStruct) (b :: flds)

end StValue

namespace Memory

open MemValue

/-! ## Resolving a path identity

KeY never does this: `idC(idp, flds)` *is* the name of the location and the
taclets index `read` by it.  The interpreter gives every object its own `Nat`,
so reading the pre-state leaf means following the path through the heap first.
That is the one place the two models have to be brought together, and it is
here rather than inside `readIn` so that everything below it is the algebra. -/

/-- One step of a path, in the interpreter's heap. -/
def step (h : List (Nat × MObj)) (n : Nat) : Seg -> Option Nat
  | Seg.field f =>
      match lookupBy n h with
      | some (MObj.struct fields) =>
          match lookupBy f fields with
          | some (MVal.ref m) => some m
          | _ => none
      | _ => none
  | Seg.at i =>
      match lookupBy n h with
      | some (MObj.array elems) =>
          if hb : 0 ≤ i ∧ i.toNat < elems.length then
            match elems.get ⟨i.toNat, hb.2⟩ with
            | MVal.ref m => some m
            | _ => none
          else none
      | _ => none

/-- The object a path identity names, in the interpreter's heap.  `none` where
the path leaves the heap — an unallocated root, a primitive link, an
out-of-bounds index — which is where a read falls back to `dflt`. -/
def resolveFrom (h : List (Nat × MObj)) (n : Nat) : List Seg -> Option Nat
  | [] => some n
  | a :: rest =>
      match step h n a with
      | some m => resolveFrom h m rest
      | none => none

/-- `resolveFrom` at a path identity. -/
def resolve (h : List (Nat × MObj)) : Identity -> Option Nat
  | .idC r p => resolveFrom h r.toNat p

/-- A root identity resolves to its root.  The equation `Update/Theory.lean`
needs to keep its bridges `rfl`. -/
@[simp] theorem resolve_idCC (h : List (Nat × MObj)) (n : Nat) :
    resolve h (.idCC (.ofNat n)) = some n := rfl

/-- A slot of the pre-state heap at a resolved object, `Semantics.readM` at
one segment with its halts read as `dflt` (KeY's reads do not fault; the
bounds test is the taclet's guard). -/
def preRead (h : List (Nat × MObj)) (n : Nat) (a : Seg) : MemValue :=
  match lookupBy n h, a with
  | some (MObj.struct fields), Seg.field f =>
      match lookupBy f fields with
      | some v => MVal.toMemValue v
      | none => dflt
  | some (MObj.array elems), Seg.at i =>
      if hb : 0 ≤ i ∧ i.toNat < elems.length then
        MVal.toMemValue (elems.get ⟨i.toNat, hb.2⟩)
      else dflt
  | _, _ => dflt

/-- …at a path identity, resolved first. -/
def preReadId (h : List (Nat × MObj)) (id : Identity) (a : Seg) : MemValue :=
  match resolve h id with
  | some n => preRead h n a
  | none => dflt

end Memory

/-- The `Memory` twin of `Struct.inductionOn`: `induction` does not support a
mutual inductive, and no `Memory`-recursive proof descends into a view's
struct. -/
theorem Memory.inductionOn {motive : Memory -> Prop}
    (h0 : motive .mtMem) (h1 : forall h, motive (.pre h))
    (h2 : forall m id a v, motive m -> motive (.write m id a v))
    (h3 : forall m (idp : IdentityPrim) ty, motive m -> motive (.addM m idp ty))
    (h4 : forall m (idp : IdentityPrim) st, motive m -> motive (.copySt m idp st)) :
    forall m, motive m
  | .mtMem => h0
  | .pre h => h1 h
  | .write m id a v => h2 m id a v (Memory.inductionOn h0 h1 h2 h3 h4 m)
  | .addM m idp ty => h3 m idp ty (Memory.inductionOn h0 h1 h2 h3 h4 m)
  | .copySt m idp st => h4 m idp st (Memory.inductionOn h0 h1 h2 h3 h4 m)

/-! ## The readers

`readIn` recurses on the memory term and `readR` on the path, both
structurally; `find` recurses on the path and crosses into `readR` at a view.
Nothing here is well-founded recursion, so every equation is `rfl` and a closed
term reduces in the kernel. -/

namespace Memory

/-- `read<[α]>(mem, id, a)`.  The `copySt` arm is `readCopySt`: a read below
the copied root is a `find` into the copied struct. -/
def readIn : Memory -> Identity -> Seg -> MemValue
  | .mtMem, _, _ => .dflt
  | .pre h, id, a => preReadId h id a
  | .write mem id1 a1 v, id2, a2 =>
      if id1 = id2 ∧ a1 = a2 then v else readIn mem id2 a2
  | .addM mem idp _, id, a => if idp = id.root then .dflt else readIn mem id a
  | .copySt mem idp st, id, a =>
      if idp = id.root then StValue.toMemValue (StValue.findSt st (id.path ++ [a]))
      else readIn mem id a

/-- `read<[Identity]>(mem, id, a)`. -/
def readId (mem : Memory) (id : Identity) (a : Seg) : Identity :=
  (readIn mem id a).asIdentity id a

/-- The identity a whole path names: `readR<[Identity]>`. -/
def readRId : Memory -> Identity -> List Seg -> Identity
  | _, id, [] => id
  | mem, id, a :: rest => readRId mem (readId mem id a) rest

/-- `readR<[α]>(mem, id, flds)`.  The empty path reads the identity itself
(the paper's `readREmptyPath`); a non-empty one resolves all but the last
field and reads there. -/
def readR : Memory -> Identity -> List Seg -> MemValue
  | _, id, [] => .ident id
  | mem, id, [a] => readIn mem id a
  | mem, id, a :: b :: rest => readR mem (readId mem id a) (b :: rest)

end Memory

namespace StValue

open Struct

/-- `find<[α]>(st, flds)`.  The one-segment arm is KeY's `isEmpty(flds)`
branch, and it is not the same as recursing: the last step reads at the
*caller's* sort, so a primitive leaf survives it where `(Struct)` would not.

The `copyMem` arm is `findCopyMem`: the whole remaining path goes to `readR`
in one step, as the taclet does. -/
def find : Struct -> List Seg -> StValue
  | .copyMem mem id, flds => MemValue.ofView mem (Memory.readR mem id flds)
  | s, [] => .st s
  | s, [a] => selectSt s a
  | s, a :: b :: flds => find ((selectSt s a).asStruct) (b :: flds)

end StValue

/-- The spine step of `find` on a term that is not itself a view: `findPath`,
in the reader that crosses into memory.  `findCopyMem` is what answers a view,
in one step, so this is the other half of KeY's one rule. -/
theorem StValue.find_cons_view (s : Struct) (a : Seg) {flds : List Seg}
    (h : flds ≠ []) (hs : forall mem id, s ≠ Struct.copyMem mem id) :
    StValue.find s (a :: flds) = StValue.find ((StValue.selectSt s a).asStruct) flds := by
  cases flds with
  | nil => exact absurd rfl h
  | cons b rest =>
      cases s with
      | copyMem mem id => exact absurd rfl (hs mem id)
      | mtSt => rfl
      | storeSt _ _ _ => rfl

/-! ### Where the two readers agree -/

mutual
  /-- No `copyMem` anywhere in the term. -/
  def StValue.structViewFree : Struct -> Bool
    | .mtSt => true
    | .storeSt s _ v => StValue.structViewFree s && StValue.viewFree v
    | .copyMem _ _ => false
  def StValue.viewFree : StValue -> Bool
    | .prim _ => true
    | .st s => StValue.structViewFree s
end

@[simp] theorem StValue.asStruct_viewFree {v : StValue} (h : v.viewFree = true) :
    StValue.structViewFree v.asStruct = true := by
  cases v with
  | prim _ => rfl
  | st s => exact h

theorem StValue.selectSt_viewFree {s : Struct} (a : Seg)
    (h : StValue.structViewFree s = true) :
    StValue.viewFree (StValue.selectSt s a) = true := by
  induction s using Struct.inductionOn with
  | h0 => simp [selectSt, viewFree, structViewFree]
  | h1 s0 a1 v ih =>
      simp only [StValue.structViewFree, Bool.and_eq_true] at h
      by_cases he : a1 = a
      · simp only [selectSt, he, reduceIte]; exact h.2
      · simp only [selectSt, he, reduceIte]; exact ih h.1
  | h2 mem id => simp [StValue.structViewFree] at h

/-- A term with no view in it reads the same either way, which is what makes
`findSt` an under-approximation of `find` rather than a second reader. -/
theorem StValue.find_eq_findSt : forall (flds : List Seg) (s : Struct),
    StValue.structViewFree s = true -> find s flds = findSt s flds
  | [], s, h => by
      cases s with
      | copyMem _ _ => simp [StValue.structViewFree] at h
      | mtSt => rfl
      | storeSt _ _ _ => rfl
  | [a], s, h => by
      cases s with
      | copyMem _ _ => simp [StValue.structViewFree] at h
      | mtSt => rfl
      | storeSt _ _ _ => rfl
  | a :: b :: rest, s, h => by
      have hnext : StValue.structViewFree ((selectSt s a).asStruct) = true :=
        StValue.asStruct_viewFree (StValue.selectSt_viewFree a h)
      cases s with
      | copyMem _ _ => simp [StValue.structViewFree] at h
      | mtSt =>
          show find ((selectSt Struct.mtSt a).asStruct) (b :: rest)
            = findSt ((selectSt Struct.mtSt a).asStruct) (b :: rest)
          exact StValue.find_eq_findSt (b :: rest) _ hnext
      | storeSt s0 a1 v =>
          show find (((selectSt (Struct.storeSt s0 a1 v) a)).asStruct) (b :: rest)
            = findSt (((selectSt (Struct.storeSt s0 a1 v) a)).asStruct) (b :: rest)
          exact StValue.find_eq_findSt (b :: rest) _ hnext

end Theory
end Solidity
