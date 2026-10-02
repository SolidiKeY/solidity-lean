import Solidity.Semantics
import Solidity.Semantics.DecEq

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

## Three arms on a view

`selectSt`, `storeAt` (`Theory/Storage.lean`) and `delNode` each have an arm
for a `copyMem` view.  Only the first has a taclet upstream
(`selectOnCopyMemPrim`/`selectOnCopyMemRef`, `structMemoryRules.key`), and
it is stated one level up; the other two are ours to choose, and each is
chosen so that the rule which *does* exist subsumes it:

* `selectSt (copyMem mem id) a` pushes the view down — `copyMem mem (id·a)` —
  and reads nothing, which keeps `selectSt` structural on `Struct` alone, as
  the termination argument below needs.  The two taclets that *do* read a
  selector of a view into memory are answered by `find`, whose `copyMem` arm
  (`Memory.viewRead`) is reached first: `Theory/CrossDomain.lean` states them
  there.  `selectSt`'s own arm is reachable only through `findSt`, the reader
  that stops at a view.
* `storeAt` puts a `storeSt` shadow node *over* the view rather than replacing
  it.  Replacing it would destroy the view and make `find_save_frame` false.
* `delNode` flattens a view (and `mtSt`, and the pre-state leaf `cur`) to
  `mtSt`: it cannot mark a view whose members it does not know, and every
  member of a deleted node of unknown kind reads its default anyway.

## Kinded nodes and the two lazy leaves

A chain built on `mtSt` is KeY's untyped world: it cannot tell a mapping from
a struct, so a delete resets every member and a copy goes member by member.
The interpreter can tell them apart, and what it does with a mapping member
(kept by `delete`), a fixed-size array (keeps its length), or an array
written over a longer one (the old slots cleared up to the old length, kept
beyond) depends on it.  Three constructors carry that knowledge:

* `mtK k d` — an empty node of kind `k` (`NodeKind`), whose absent members
  read `d`: a mapping's default, or `st mtSt` for a struct or an array.
  `Struct.kind` reads the kind through every write (`storeSt`) and every lazy
  leaf; `none` is "nothing is here", the kind of `mtSt` and of a view.
* `copyAt old new` — solkey's non-collapsing leaf: `new` copied over `old`,
  read one selector at a time by `copyRead`, from the two kinds, the two
  lengths and the two members (the interpreter's `SVal.overlay`, arm by arm).
* `delSt s` — `s` deleted, read one selector at a time: a member that
  `keepsOnDelete` names (a mapping's, a fixed-size array's length, an array's
  slot past its end) is kept, every other one is `delValue`d.

Both leaves are lazy for the same reason `copyMem` is: `selectSt` stays
structural, and a leaf's meaning is the read taclets that go through it,
which is how solkey states it.  On a kind-free chain (no `mtK`, no leaf) they
agree with the eager delete and the collapsing copy they replace.

`Seen`/`StValue.Equiv` at the end is observational equality: two values that
agree on every primitive and every kind along every path.  It is what the
laws that are not literal (a copy, a delete, a pop) are stated up to
(`Theory/Observe.lean`).

## A view inside a view

`find` on a `copyMem` is a `readR` into memory, and `read` on a `copySt` is a
`find` into storage, so the two would be mutually recursive — and not
structurally, because the path *grows* on the way in (`readCopySt` reads
`flds ++ [a]`).  A lexicographic measure closes it, but well-founded recursion
gives up definitional unfolding, and `decide` on a closed term is how half the
taclets here are checked (`Sanity` below; the untyped layer's corpus checked
the rest, and regenerating it as `sol[C]{}` examples is `docs/kernel-port.md`'s
"The solkey corpus").

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

/-! ## Shapes

`memoryHeader.key` declares `Shape` with four `\unique` constructors, and a
root may carry one (`shaped`, below).  It is a sort of its own, outside the
mutual block, because nothing in it mentions a struct or a memory.  Its
functions and their taclets — `sizeOf`, `shapeAt`, `idShape` — are
`Theory/Memory.lean`'s, where `memoryRules.key` states them. -/

/-- `Shape` (`memoryHeader.key`): the static shape of a location, which is
what carries a fixed-size array's length where no statement ever writes it. -/
inductive Shape where
  /-- `leaf`: a primitive, or a struct all of whose members are named. -/
  | leaf
  /-- `fixedArr(n, sh)`: a fixed-size array of length `n`. -/
  | fixedArr (n : Int) (sh : Shape)
  /-- `dynArr(sh)`: a dynamic array. -/
  | dynArr (sh : Shape)
  /-- `mapOf(sh)`: a mapping, its values of shape `sh`. -/
  | mapOf (sh : Shape)
  deriving Repr, DecidableEq

mutual
  /-- `#shapeOf(T)`, the meta-operator `fieldShapeDef` unfolds to: the shape of a
  declared type, a fixed-size array's with its length (`fixedArr(3, leaf)` for
  `uint[3]`), which is what the `typed` family of `structRules.key` reads
  (`Theory/Storage.lean`, "Shapes"). -/
  def Shape.ofTy : Ty -> Shape
    | .prim _ => .leaf
    | .ref r => Shape.ofRefTy r
  /-- `#shapeOf` at a reference type. -/
  def Shape.ofRefTy : RefTy -> Shape
    | .struct _ => .leaf
    | .array e => .dynArr (Shape.ofTy e)
    | .fixed e n => .fixedArr n (Shape.ofTy e)
    | .mapping _ v => .mapOf (Shape.ofTy v)
end

/-- `fieldShape(m)` (`structHeader.key`): the declared shape of a member.  KeY's
member constants know their declaration; a `Seg.field` carries only the
member's name, so the declarations are the caller's — `decl` is the member
table `#shapeOf` reads. -/
def fieldShape (decl : Name -> Ty) (m : Name) : Shape := Shape.ofTy (decl m)

/-! ## Identities

`\unique Identity idC(IdentityPrim, List)` (`memoryRules.key`): the identity
reached from a root along a path of fields.  `\unique` is injectivity, which
`DecidableEq` supplies — `memoryExample2` closes on exactly that. -/

/-- `IdentityPrim` — a sort of its own in `memoryHeader.key`, not a number:
it is what `addM` allocates, what `new` tests, and what `idC` pairs with a
path.  The interpreter names objects by `Nat`, so `ofNat` is where the two
meet and `toNat` is the only place the number is visible. -/
inductive IdentityPrim where
  | ofNat (n : Nat)
  /-- `\unique IdentityPrim shaped(IdentityPrim, Shape)`: a root tagged with
  its declared shape, which is how `initSize` finds a fixed-size array's
  length.  `\unique`, so a shaped root is not the root it tags. -/
  | shaped (idp : IdentityPrim) (sh : Shape)
  deriving Repr, DecidableEq

/-- The interpreter's object number: a shaped root is the root it tags. -/
def IdentityPrim.toNat : IdentityPrim -> Nat
  | .ofNat n => n
  | .shaped r _ => r.toNat

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
`Nat` names the root of a path identity with an empty path, which is what a
future denotation bridging this theory to the interpreter would write and
what `resolve` inverts (not yet written; the untyped layer's Update/Theory
module had it). -/
def MVal.toMemValue : MVal -> MemValue
  | .prim p => .prim p
  | .ref n => .ident (.idCC (.ofNat n))

namespace MemValue

/-! ### Casts

`init<[α]>(idC(idp, flds), a)` is resolved by the sort the read is taken
at, and the two sorts answer differently: a primitive member of a fresh root
reads as the primitive default, a *reference* member reads as the identity one
field further down.  That second one is the whole of the statement "a reference
member of a fresh root reads as the identity reached by extending the path, so
the struct it points to exists as soon as its parent does". -/

/-- `init<[prim]>(idC(idp, flds), a) ⇝ defaultValue<[prim]>` — the cast
that resolves a sort-free default at a primitive sort. -/
def asPrim : MemValue -> MVal
  | prim p => .prim p
  | ident _ => MVal.int 0
  | dflt => MVal.int 0

/-- `init<[Identity]>(idC(idp, flds), a) ⇝ idC(idp, consr(flds, a))` — the
cast at the `Identity` sort, which needs the location the read was taken at
and is why it takes `loc` and `a`. -/
def asIdentity : MemValue -> Identity -> Seg -> Identity
  | ident i, _, _ => i
  | prim _, loc, a => loc.extend a
  | dflt, loc, a => loc.extend a

end MemValue

/-! ## The three sorts -/

/-- What a storage node is.  `none` (see `Struct.kind`) is "nothing is here". -/
inductive NodeKind where
  | struct
  | arr (fixed : Bool)
  | map
  deriving Repr, DecidableEq

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
    /-- The `storage` program variable below `p`, as the line's pre-state
    holds it: the leaf a read over the calculus's updates is lowered onto —
    not yet written; `Update.lean` has the lowering for everything but this
    leaf.  A view, like `copyMem`: selecting pushes it down and reads
    nothing, so every theory law holds of it as of a free term. -/
    | cur (p : List Seg)
    /-- An empty node of kind `k` whose absent members read `d`.  For a struct or an
    array `d` is `st mtSt`; for a mapping it is the mapping's default. -/
    | mtK (k : NodeKind) (d : StValue)
    /-- solkey's non-collapsing leaf: `new` copied over `old`, read lazily. -/
    | copyAt (old new : Struct)
    /-- `s` deleted, read lazily by `s`'s kind and length. -/
    | delSt (s : Struct)
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
conversions are where the sort index goes.  A struct becomes `dflt` so
that `initIdentity` manufactures `idC(r, flds·a)` on the read — which is
`readCopyStIdentity`, without a recursion of its own. -/

/-- A storage value as a memory slot. -/
def toMemValue : StValue -> MemValue
  | .prim p => .prim p
  | .st _ => .dflt

end StValue

namespace MemValue

/-- A memory slot read through a `copyMem` view, as a storage value, at the
location `loc`/`a` it was read from.  A primitive is itself
(`selectOnCopyMemPrim`); anything else is the view one field down, over the
identity the slot names (`selectOnCopyMemRef`'s
`copyMem(mtSt, mem, read<[Identity]>(mem, id, a))`).  That includes a
never-written slot: its identity is `initIdentity`'s `idC(r, flds·a)`,
so a member struct that memory created implicitly is still read *through*,
and a write below it is seen. -/
def ofViewAt (mem : Memory) (loc : Identity) (a : Seg) : MemValue -> StValue
  | .prim p => .prim p
  | v => .st (Struct.copyMem mem (v.asIdentity loc a))

@[simp] theorem ofViewAt_prim (mem : Memory) (loc : Identity) (a : Seg) (p : PrimVal) :
    ofViewAt mem loc a (.prim p) = .prim p := rfl
@[simp] theorem ofViewAt_ident (mem : Memory) (loc : Identity) (a : Seg) (i : Identity) :
    ofViewAt mem loc a (.ident i) = .st (Struct.copyMem mem i) := rfl
@[simp] theorem ofViewAt_dflt (mem : Memory) (loc : Identity) (a : Seg) :
    ofViewAt mem loc a .dflt = .st (Struct.copyMem mem (loc.extend a)) := rfl

/-! ### Casts at a primitive sort

`read<[int]>`/`read<[bool]>`: the primitive casts of a memory slot, which a
non-primitive slot answers with the sort's default, as `StValue.asInt` does
on the storage side.  They are what `findCopyMem` is stated through. -/

/-- `(int) v` on a memory slot. -/
def asInt : MemValue -> Int
  | prim (PrimVal.int v) => v
  | _ => 0

/-- `(bool) v` on a memory slot. -/
def asBool : MemValue -> Bool
  | prim (PrimVal.bool b) => b
  | _ => false

end MemValue

namespace Struct

/-- An empty struct. -/
abbrev structSt : Struct := .mtK .struct (.st .mtSt)
/-- An empty array, fixed-size or dynamic. -/
abbrev arrSt (fx : Bool) : Struct := .mtK (.arr fx) (.st .mtSt)
/-- An empty mapping whose absent entries read `d`. -/
abbrev mapSt (d : StValue) : Struct := .mtK .map d

/-- The kind of the node a term is: a write keeps it, a copy takes the new
value's, a delete keeps the deleted node's.  `none` is "nothing is here". -/
def kind : Struct -> Option NodeKind
  | .mtSt | .copyMem .. | .cur _ => none
  | .mtK k _ => some k
  | .storeSt s _ _ => s.kind
  | .copyAt _ n => n.kind
  | .delSt s => s.kind

/-- `induction` does not support a mutual inductive; this is the one-sort
recursor, which is all the `Struct`-recursive proofs need — none of them
descends into a stored value or into a view's memory. -/
theorem inductionOn {motive : Struct -> Prop} (h0 : motive mtSt)
    (h1 : forall s a v, motive s -> motive (storeSt s a v))
    (h2 : forall mem id, motive (copyMem mem id))
    (h3 : forall p, motive (cur p))
    (h4 : forall k d, motive (mtK k d))
    (h5 : forall o n, motive o -> motive n -> motive (copyAt o n))
    (h6 : forall s, motive s -> motive (delSt s)) : forall s, motive s
  | mtSt => h0
  | storeSt s a v => h1 s a v (inductionOn h0 h1 h2 h3 h4 h5 h6 s)
  | copyMem mem id => h2 mem id
  | cur p => h3 p
  | mtK k d => h4 k d
  | copyAt o n =>
      h5 o n (inductionOn h0 h1 h2 h3 h4 h5 h6 o) (inductionOn h0 h1 h2 h3 h4 h5 h6 n)
  | delSt s => h6 s (inductionOn h0 h1 h2 h3 h4 h5 h6 s)

end Struct

/-- An array, of either length discipline. -/
def NodeKind.isArr : Option NodeKind -> Bool
  | some (.arr _) => true
  | _ => false

/-- A struct, or nothing: the kinds a copy goes through member by member. -/
def NodeKind.isStructLike : Option NodeKind -> Bool
  | none | some .struct => true
  | _ => false

namespace StValue

open Struct

/-! ## Delete and copy, one node at a time

A delete and a copy are the two lazy leaves `delSt` and `copyAt`; what is
here is how one member of each reads, which `selectSt` below calls. -/

/-- KeY's `size`: an array's length is a member like any other. -/
abbrev lengthSeg : Seg := .field "length"

/-- `defaultValue<[alphaPrim]>`, read off the value's own sort. -/
def primDefault : PrimVal -> PrimVal
  | .int _ => .int 0
  | .bool _ => .bool false

/-- `delNode(st)`: the delete marker.  A view, the pre-state leaf and `mtSt`
are flattened to `mtSt` (module docstring); anything else is marked, and read
through by `selectSt`'s `delSt` arm. -/
def delNode : Struct -> Struct
  | .mtSt | .copyMem .. | .cur _ => .mtSt
  | s => .delSt s

/-- A value reset: `delNode` on a `Struct`, the default on a `Prim` — the
single-sort `delValue<[α]>` that solkey's `delField` replaced, and still
what `delField` is here. -/
def delValue : StValue -> StValue
  | prim q => prim (primDefault q)
  | st s => st (delNode s)

/-- `v` copied over `old`: the value `SVal.overlay` computes.  A word
replaces; a node is laid over what was there. -/
def copyVal (old : StValue) : StValue -> StValue
  | prim p => prim p
  | st n => st (.copyAt (asStruct old) n)

/-- `0 ≤ i < n`: an index inside an array of length `n`. -/
def inRange (n i : Int) : Bool := decide (0 ≤ i) && decide (i < n)

/-- A member that a delete leaves as it is. -/
def keepsOnDelete : Option NodeKind -> Int -> Seg -> Bool
  -- a mapping: all of it (`selectStDelNodeMap`)
  | some .map, _, _ => true
  -- a fixed-size array: its length (`delNodeFixed`)
  | some (.arr true), _, .field f => f == "length"
  -- an array: a slot past the end (`selectStDelNodeIndexStruct`'s keep branch)
  | some (.arr _), n, .at i => !inRange n i
  | _, _, _ => false

/-- One member of `copyAt o n`, from the two kinds, the two lengths and the two
members (`SVal.overlay`, arm by arm). -/
def copyRead (ko kn : Option NodeKind) (lo ln : Int) (a : Seg) (vo vn : StValue) : StValue :=
  match kn with
  -- a map over a map keeps the old one (Solidity copies no mapping); over
  -- anything else it is laid as it is
  | some .map => if ko = some .map then vo else vn
  | some (.arr _) =>
    match a with
    | .field f => if f = "length" then vn else st .mtSt
    | .at i =>
      -- a new element over the old slot
      if inRange ln i then copyVal (if NodeKind.isArr ko then vo else st .mtSt) vn
      -- between the two lengths: cleared
      else if NodeKind.isArr ko && inRange lo i then delValue vo
      -- beyond both: kept
      else if NodeKind.isArr ko then vo else st .mtSt
  -- a struct: member by member; over another shape, onto fresh slots
  | some .struct | none =>
      copyVal (if NodeKind.isStructLike ko then vo else st .mtSt) vn

/-! ## `selectSt` -/

/-- `selectSt<[α]>(st, a)`: the outermost store at `a`, or the default.  On a
view it pushes the view down and reads nothing — see the module docstring.  On
an empty kinded node it is the node's default, and on the two lazy leaves it
is the member `copyRead`/`keepsOnDelete` say. -/
def selectSt : Struct -> Seg -> StValue
  | mtSt, _ => .st mtSt
  | storeSt s a1 v, a2 => if a1 = a2 then v else selectSt s a2
  | Struct.copyMem mem id, a => .st (Struct.copyMem mem (id.extend a))
  | Struct.cur p, a => .st (Struct.cur (p ++ [a]))
  | Struct.mtK _ d, _ => d
  | Struct.copyAt o n, a =>
      copyRead o.kind n.kind (asInt (selectSt o lengthSeg)) (asInt (selectSt n lengthSeg)) a
        (selectSt o a) (selectSt n a)
  | Struct.delSt s, a =>
      if keepsOnDelete s.kind (asInt (selectSt s lengthSeg)) a then selectSt s a
      else delValue (selectSt s a)

/-- An array's length, `selectSt<[int]>(st, size)`. -/
def lenOf (s : Struct) : Int := asInt (selectSt s lengthSeg)

/-- `find<[α]>(st, flds)` on a storage term that holds no memory view: the
read `readCopySt` takes into a copied struct.  `find` below is this one plus
the arm that crosses into memory, and `find_eq_findSt` says they agree
wherever nothing is nested. -/
def findSt : Struct -> List Seg -> StValue
  | s, [] => .st s
  | s, [a] => selectSt s a
  | s, a :: b :: flds => findSt ((selectSt s a).asStruct) (b :: flds)

end StValue

/-! ## Observation

What a read shows, and the equality the laws that are not literal are stated
up to.  (`Obs` is `Calculus/DecideComplete.lean`'s, hence `Seen`.) -/

/-- What one read shows: a primitive exactly, or a node's kind (`none` means absent). -/
inductive Seen where
  | prim (p : PrimVal)
  | node (k : Option NodeKind)
  deriving DecidableEq, Repr

namespace StValue

/-- What `v` shows. -/
def seen : StValue -> Seen
  | .prim p => .prim p
  | .st s => .node s.kind

/-- `v` read along a path, one selector at a time through the `Struct` cast. -/
def readAt (v : StValue) : List Seg -> StValue
  | [] => v
  | a :: q => readAt (selectSt (asStruct v) a) q

/-- Observational equality: every read along every path shows the same. -/
def Equiv (v w : StValue) : Prop := ∀ q, (v.readAt q).seen = (w.readAt q).seen

end StValue

/-- `StValue.Equiv` at `Struct`. -/
def Struct.Equiv (s t : Struct) : Prop := StValue.Equiv (.st s) (.st t)

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
      | some (MObj.array elems _) =>
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

/-- A root identity resolves to its root.  The equation a future
theory-to-interpreter denotation bridge would need to keep its bridges
`rfl` (not yet written; the untyped layer's Update/Theory module had it). -/
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
  | some (MObj.array elems _), Seg.at i =>
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
(`readREmptyPath`); a non-empty one resolves all but the last
field and reads there. -/
def readR : Memory -> Identity -> List Seg -> MemValue
  | _, id, [] => .ident id
  | mem, id, [a] => readIn mem id a
  | mem, id, a :: b :: rest => readR mem (readId mem id a) (b :: rest)

/-- A read through a `copyMem(mtSt, mem, id)` view, as a storage value: `readR`'s
walk, with the last slot seen through `MemValue.ofViewAt`.  At a primitive sort
it is `readR` (`findCopyMem`); at `Struct` it is the view one field further
down (`selectOnCopyMemRef`), which is what lets a storage copy *of* a view's
member stay lazy. -/
def viewRead (mem : Memory) : Identity -> List Seg -> StValue
  | id, [] => .st (Struct.copyMem mem id)
  | id, [a] => MemValue.ofViewAt mem id a (readIn mem id a)
  | id, a :: b :: rest => viewRead mem (readId mem id a) (b :: rest)

end Memory

namespace StValue

open Struct

/-- `find<[α]>(st, flds)`.  The one-segment arm is KeY's `isEmpty(flds)`
branch, and it is not the same as recursing: the last step reads at the
*caller's* sort, so a primitive leaf survives it where `(Struct)` would not.

The `copyMem` arm is `findCopyMem`: the whole remaining path goes to memory
in one step, as the taclet does, and `Memory.viewRead` is that read at the
storage sorts. -/
def find : Struct -> List Seg -> StValue
  | .copyMem mem id, flds => Memory.viewRead mem id flds
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
      | cur _ => rfl
      | mtK _ _ => rfl
      | copyAt _ _ => rfl
      | delSt _ => rfl

/-! ### Where the two readers agree -/

mutual
  /-- No `copyMem` anywhere in the term. -/
  def StValue.structViewFree : Struct -> Bool
    | .mtSt => true
    | .storeSt s _ v => StValue.structViewFree s && StValue.viewFree v
    | .copyMem _ _ => false
    | .cur _ => true
    | .mtK _ d => StValue.viewFree d
    | .copyAt o n => StValue.structViewFree o && StValue.structViewFree n
    | .delSt s => StValue.structViewFree s
  def StValue.viewFree : StValue -> Bool
    | .prim _ => true
    | .st s => StValue.structViewFree s
end

@[simp] theorem StValue.asStruct_viewFree {v : StValue} (h : v.viewFree = true) :
    StValue.structViewFree v.asStruct = true := by
  cases v with
  | prim _ => rfl
  | st s => exact h

/-- A copy of view-free values is view-free. -/
theorem StValue.copyVal_viewFree {o n : StValue} (ho : o.viewFree = true)
    (hn : n.viewFree = true) : (StValue.copyVal o n).viewFree = true := by
  cases n with
  | prim _ => rfl
  | st n' =>
      simp only [StValue.copyVal, StValue.viewFree, StValue.structViewFree, Bool.and_eq_true]
      exact ⟨StValue.asStruct_viewFree ho, hn⟩

/-- A delete of a view-free value is view-free. -/
theorem StValue.delValue_viewFree {v : StValue} (h : v.viewFree = true) :
    (StValue.delValue v).viewFree = true := by
  cases v with
  | prim _ => rfl
  | st s =>
      cases s <;> first
        | rfl
        | exact h

/-- `copyRead` builds nothing but copies and deletes of its two members. -/
theorem StValue.copyRead_viewFree (ko kn : Option NodeKind) (lo ln : Int) (a : Seg)
    {vo vn : StValue} (ho : vo.viewFree = true) (hn : vn.viewFree = true) :
    (StValue.copyRead ko kn lo ln a vo vn).viewFree = true := by
  have hm : (StValue.st Struct.mtSt).viewFree = true := rfl
  unfold StValue.copyRead
  split
  · split <;> assumption
  · split
    · split
      · exact hn
      · exact hm
    · split
      · exact StValue.copyVal_viewFree (by split <;> assumption) hn
      · split
        · exact StValue.delValue_viewFree ho
        · split <;> assumption
  · exact StValue.copyVal_viewFree (by split <;> assumption) hn
  · exact StValue.copyVal_viewFree (by split <;> assumption) hn

theorem StValue.selectSt_viewFree {s : Struct} (a : Seg)
    (h : StValue.structViewFree s = true) :
    StValue.viewFree (StValue.selectSt s a) = true := by
  induction s using Struct.inductionOn generalizing a with
  | h0 => rfl
  | h1 s0 a1 v ih =>
      simp only [StValue.structViewFree, Bool.and_eq_true] at h
      by_cases he : a1 = a
      · simp only [selectSt, he, reduceIte]; exact h.2
      · simp only [selectSt, he, reduceIte]; exact ih a h.1
  | h2 mem id => simp only [StValue.structViewFree, Bool.false_eq_true] at h
  | h3 p => rfl
  | h4 k d => exact h
  | h5 o n iho ihn =>
      simp only [StValue.structViewFree, Bool.and_eq_true] at h
      exact StValue.copyRead_viewFree _ _ _ _ _ (iho a h.1) (ihn a h.2)
  | h6 s0 ih =>
      simp only [selectSt]
      split
      · exact ih a h
      · exact StValue.delValue_viewFree (ih a h)

/-- A term with no view in it reads the same either way, which is what makes
`findSt` an under-approximation of `find` rather than a second reader. -/
theorem StValue.find_eq_findSt : forall (flds : List Seg) (s : Struct),
    StValue.structViewFree s = true -> find s flds = findSt s flds
  | [], s, h => by
      cases s with
      | copyMem _ _ => simp only [StValue.structViewFree, Bool.false_eq_true] at h
      | _ => rfl
  | [a], s, h => by
      cases s with
      | copyMem _ _ => simp only [StValue.structViewFree, Bool.false_eq_true] at h
      | _ => rfl
  | a :: b :: rest, s, h => by
      have hnext : StValue.structViewFree ((selectSt s a).asStruct) = true :=
        StValue.asStruct_viewFree (StValue.selectSt_viewFree a h)
      have hs : forall mem id, s ≠ Struct.copyMem mem id := by
        intro mem id he
        subst he
        simp only [StValue.structViewFree, Bool.false_eq_true] at h
      rw [StValue.find_cons_view s a (List.cons_ne_nil _ _) hs]
      exact StValue.find_eq_findSt (b :: rest) _ hnext

end Theory
end Solidity
