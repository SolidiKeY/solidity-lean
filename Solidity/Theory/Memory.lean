import Solidity.Theory.Terms
import Solidity.Semantics.DecEq

/-!
# `memoryRules.key` as a term algebra

The memory twin of `Theory/Storage.lean`: `mtMem`, `write`, `addM`, `read`,
`readR` and `new` (`memoryHeader.key`, `memoryRules.key`) as total Lean
functions, one theorem per taclet.  There is no denotation into the
interpreter's heap: it would need `writeMemField`/`allocDefault`, which this
module deliberately does not import so that the algebra stays as cheap to
elaborate as the storage one.  The link runs the other way: the closer's
memory readers, sound by the interpreter, read a memory as a term of this
algebra and answer what `readIn` answers, each arm by its taclet's theorem,
here or in `Theory/CrossDomain.lean` (`Calculus/MemTheory.lean`).

Unlike `structRules.key`, this file has **no counterpart in the fundamentals
repository**: that one models `read` and nothing else, so `readOnWrite`,
`readOnAddM`, the `new` family and the `default` family are transcribed here
from the `.key` source directly.

## Identities are KeY's path identities

A memory location is named the way KeY names it: `idC(idp, flds)`, a root of
sort `IdentityPrim` together with the field path that reaches the location
from it.  `idCC(idp)` is `idC(idp, [])`, and `initIdentity` manufactures
`idC(idp, flds · a)` on the fly, which is what makes a reference member of a
freshly added root *exist* without anything being allocated for it — the
point: "this is how Solidity's implicit creations are modelled without
allocating anything".

The interpreter is the other way round: every object it allocates gets its own
`Nat` and a path is resolved to one *before* any read or write happens
(`Wp.memBase`, `Semantics.readM`).  Resolving a path identity against a
concrete heap is therefore a function (`resolve`, `Theory/Terms.lean`), used
by the `pre` leaf, which reads a heap as it stands; the algebra itself never
resolves anything, exactly as KeY's does not.

`readR` walks a whole path one field at a time, resolving each field to the
identity it names before reading the next, so the chain-walking layer —
`readR`, `readREmpty`, `readRCons`, `idCCDef`, `initIdentity` — is here
and proved.

`addM` carries two things: KeY's own root, which is what lets `readOnAddM` and
`newFromAdd` branch on it exactly as the taclets do, and the allocated type,
which KeY does not carry.  The type is the one place this is eager where KeY
is lazy, for the same reason as the storage side: KeY resolves a never-written
slot of a fresh object to `init<[α]>` at whatever sort the reader asks for,
while `Semantics.allocDefault` materializes the object when it is allocated,
so the term has to know its type to denote.

## Shaped roots

A root may be `shaped(idp, sh)` (`Theory/Terms.lean`): solkey tags every fresh
root with its declared shape so that `init<[int]>` at its `size` is the
declared length of a fixed-size array (`initSize`).  The shape algebra
that answers it — `sizeOf`, `shapeAt`, `idShape` — is the last section here.
-/

namespace Solidity
namespace Theory

open Semantics

/-! ## What is here and what is one module down

The sorts, the path-identity resolver and the readers are
`Theory/Terms.lean`: `read` on a `copySt` view is a `find` into storage, so
they have to be declared in the same block as the storage reader.  What is
here is `memoryRules.key`'s taclets and the `new` predicate. -/

namespace Memory

open MemValue

/-! ## The taclets of `memoryRules.key` -/

/-- `read<[α]>(write(mem, id1, a1, v), id2, a2)`. -/
@[simp] theorem readOnWrite (mem : Memory)
    (id1 id2 : Identity) (a1 a2 : Seg) (v : MemValue) :
    readIn (write mem id1 a1 v) id2 a2 =
      if id1 = id2 ∧ a1 = a2 then v else readIn mem id2 a2 := rfl

/-- `read<[α]>(mtMem, id, a) ⇝ init<[α]>(id, a)`. -/
@[simp] theorem readFromEmptyMemory (id : Identity)
    (a : Seg) : readIn mtMem id a = dflt := rfl

/-- `read<[α]>(addM(mem, idp1), idC(idp2, flds), a)`: KeY splits on
`idp1 = idp2` and answers `init<[α]>` on the fresh root, reading through
otherwise.  This is that taclet. -/
@[simp] theorem readOnAddM (mem : Memory) (idp : IdentityPrim)
    (ty : RefTy) (id : Identity) (a : Seg) :
    readIn (addM mem idp ty) id a =
      if idp = id.root then dflt else readIn mem id a := rfl

/-- `readAddEqual`: a read of the root just added is its default. -/
@[simp] theorem readAddEqual (mem : Memory) (r : IdentityPrim)
    (ty : RefTy) (flds : List Seg) (a : Seg) :
    readIn (addM mem r ty) (.idC r flds) a = dflt := by
  simp [readOnAddM, Identity.root]

/-- `readAddDifferent`: a read below any other root passes through. -/
theorem readAddDifferent (mem : Memory) (r1 r2 : IdentityPrim)
    (ty : RefTy) (flds : List Seg) (a : Seg) (hne : r1 ≠ r2) :
    readIn (addM mem r1 ty) (.idC r2 flds) a =
      readIn mem (.idC r2 flds) a := by
  simp [readOnAddM, Identity.root, hne]

/-- `defaultValueInt`: a primitive default is `0`, wherever it is read — the
location-free cast.  Where the location matters (a shaped root's length) the
cast is `MemValue.asIntAt`, and `initElement`/`initMember`/
`initSize` below are its three rules. -/
@[simp] theorem defaultDefInt : MemValue.asPrim dflt = MVal.int 0 := rfl

/-- **`initIdentity`** — `init<[Identity]>(idC(idp, flds), a)` is
`idC(idp, consr(flds, a))`.  The taclet that gives a fresh root its members. -/
@[simp] theorem initIdentity (r : IdentityPrim) (flds : List Seg) (a : Seg) :
    MemValue.asIdentity dflt (.idC r flds) a = .idC r (flds ++ [a]) := rfl

/-- `idCCDef`: `idCC(idp) ⇝ idC(idp, nil)`. -/
@[simp] theorem idCCDef (r : IdentityPrim) : Identity.idCC r = Identity.idC r [] := rfl

/-- `readREmpty`: a one-field path is one read. -/
@[simp] theorem readREmpty (mem : Memory)
    (id : Identity) (a : Seg) : readR mem id [a] = readIn mem id a := rfl

/-- `readRCons`: a longer path resolves its first field to an identity and
continues from there.  KeY writes the same step as `firsts`/`last`. -/
@[simp] theorem readRCons (mem : Memory)
    (id : Identity) (a1 a2 : Seg) (flds : List Seg) :
    readR mem id (a1 :: a2 :: flds) =
      readR mem (readId mem id a1) (a2 :: flds) := rfl

/-- `readREmptyPath`: the empty path reads the identity itself. -/
@[simp] theorem readREmptyPath (mem : Memory)
    (id : Identity) : readR mem id [] = MemValue.ident id := rfl

/-! ## `defVal`, `defaultValue<[α]>` and `isPrimitive`

Three symbols of `memoryRules.key` that were implicit here.  `defVal` is the
sort-free reset constant a delete writes, resolved on read by `defValResolve`;
`defaultValue<[α]>` is the sorted one the casts already produce; `isPrimitive`
is the predicate the sort-directed delete taclets branch on.

They are *names* rather than new notions: `MemValue.dflt` already is the
sort-free default, and `Ty.isPrimitive` already is the test the interpreter
uses.  Naming them is what lets a chain and a rule cite the taclet KeY
cites. -/

/-- `\unique Prim defVal` — a location reset outright, sorted so it serves
storage and memory alike.  `defValResolve` is the cast that reads it. -/
def defVal : MemValue := .dflt

/-- `defaultValue<[prim]>` — `defVal` at a primitive sort, which is
`defaultDefInt`'s right-hand side. -/
@[simp] theorem defValResolvePrim : MemValue.asPrim defVal = MVal.int 0 := rfl

/-- `defaultValue<[Identity]>(idC(idp, flds), a)` — `defVal` at the identity
sort is the identity one field further down. -/
@[simp] theorem defValResolveIdentity (r : IdentityPrim) (flds : List Seg) (a : Seg) :
    MemValue.asIdentity defVal (.idC r flds) a = .idC r (flds ++ [a]) := rfl

/-- `isPrimitive(f)` — the predicate the delete taclets branch on.  A `Seg`
carries no type here, so the test is the field's declared one, which is the
same test `Semantics` makes. -/
def isPrimitive (t : Ty) : Bool := t.isPrimitive

/-! ## `readR` in KeY's own shape

`readRCons` is stated upstream with `firsts`/`last`: resolve all but the last
field, then read there.  The definition here recurses from the front, because
that is what keeps it structural and every chain in `Examples/Tactics/Theory.lean`
steps through `readREmpty`/`readRCons` by `rfl`.  This is the same rule in
KeY's spelling, as a theorem. -/

theorem readR_eq_firsts_last (mem : Memory) (id : Identity) :
    forall (flds : List Seg) (h : flds ≠ []),
      readR mem id flds = readIn mem (readRId mem id flds.dropLast) (flds.getLast h)
  | [], h => absurd rfl h
  | [_], _ => rfl
  | a :: b :: rest, _ => by
      show readR mem (readId mem id a) (b :: rest) = _
      rw [readR_eq_firsts_last mem (readId mem id a) (b :: rest) (by simp)]
      rfl

/-! ## `new`

`new(mem, idp)` is a *predicate* in KeY, and the only one in the memory
theory: it is what a freshly allocated identity's `\add` clause asserts.  Its
three taclets are the three ways a memory term can be built. -/

/-- `new(mem, idp)` against a concrete pre-state heap: `idp` is unallocated. -/
def new : Memory -> IdentityPrim -> Bool
  | mtMem, _ => true
  | pre h, idp => (lookupBy idp.toNat h).isNone
  | write mem _ _ _, idp => new mem idp
  | addM mem idp1 _, idp2 => if idp1 = idp2 then false else new mem idp2
  -- `structMemoryRules.key` states no `new` taclet for `copySt`: the copy
  -- goes under a root its own `addM` already minted, so freshness is whatever
  -- the term below it says.
  | copySt mem _ _, idp => new mem idp

/-- `new(mtMem, idp) ⇝ true`. -/
@[simp] theorem newFromEmptyMemory (idp : IdentityPrim) :
    new mtMem idp = true := rfl

/-- `new(write(mem, id1, a1, v), idp) ⇝ new(mem, idp)` — writing a slot
allocates nothing. -/
@[simp] theorem newFromWrite (mem : Memory)
    (id : Identity) (a : Seg) (v : MemValue) (idp : IdentityPrim) :
    new (write mem id a v) idp = new mem idp := rfl

/-- **`newFromAdd`** — `new(addM(mem, idp1), idp2)` is `false` when the two
agree and recurses otherwise.  The taclet, not an approximation of it: the
root `addM` allocates is carried in the term. -/
@[simp] theorem newFromAdd (mem : Memory)
    (idp1 : IdentityPrim) (ty : RefTy) (idp2 : IdentityPrim) :
    new (addM mem idp1 ty) idp2 =
      if idp1 = idp2 then false else new mem idp2 := rfl

/-- `newAddSame`: the root just added is not fresh. -/
@[simp] theorem newAddSame (mem : Memory) (r : IdentityPrim)
    (ty : RefTy) : new (addM mem r ty) r = false := by simp

/-- `newAddDifferent`: any other root is as fresh as it was. -/
theorem newAddDifferent (mem : Memory) (r1 r2 : IdentityPrim)
    (ty : RefTy) (hne : r1 ≠ r2) :
    new (addM mem r1 ty) r2 = new mem r2 := by simp [hne]

end Memory

/-! ## Shapes

`memoryRules.key`'s shape algebra: `sizeOf`, `shapeAt`, `idShape` over the
`Shape` sort of `Theory/Terms.lean`, and the one cast that reads a shape,
`init<[int]>` at a shaped root's length.  All of it is free terms — no
struct, no memory — so all of it is stated; a declared `uint[3]` has the
shape `fixedArr(3, leaf)` (`Shape.ofTy_fixed`).

`shapeAt` descends one field at a time, as `save` and `find` do.  solkey
recurses head-first (`shapeAt(sh, cons(a, xs))`); the suffix rule states one field
at the end (`shapeAtSuffix`).  The two agree on every well-typed path, and
disagree on one ill-typed one, which is solkey's `shapeAtLeafElement`:
`shapeAt(leaf, cons(at(pk), xs)) ⇝ leaf` *discards* `xs`, so solkey reads
`leaf·at(i)·m` as `leaf` where the suffix rule reads it as
`fieldShape(m)`.  Indexing a `leaf` is ill-typed, but a term can still write
it.  This package follows the suffix rule: `shapeAt` is `shapeStep` folded along the
path, `shapeAtSuffix` holds outright, and each head-first rule below is stated
as "one step, then the rest", which at `xs = nil` is the one-field rule and for
every `xs` but solkey's leaf case is solkey's. -/

/-- `sizeOf(sh)`: the length a shape fixes, `0` where none is.  (`sizeOf` is
Lean's own, so the name here is `shapeSize`.)  `mapOf` has no taclet upstream;
it is given `0`, as for `dynArr`. -/
def shapeSize : Shape -> Int
  | .fixedArr n _ => n
  | .dynArr _ => 0
  | .leaf => 0
  | .mapOf _ => 0

/-- One field of `shapeAt`.  An index keeps the element shape, a named member
restarts from its declared shape.  `size` is not a `MemberField` and has no
taclet; its shape is `leaf`, the shape of the `int` it holds. -/
def shapeStep (decl : Name -> Ty) : Shape -> Seg -> Shape
  | .fixedArr _ sh, .at _ => sh
  | .dynArr sh, .at _ => sh
  | .mapOf sh, .at _ => sh
  | .leaf, .at _ => .leaf
  | _, .field m => if m = "length" then .leaf else fieldShape decl m

/-- `shapeAt(sh, flds)`: the shape reached along a path. -/
def shapeAt (decl : Name -> Ty) (sh : Shape) (flds : List Seg) : Shape :=
  flds.foldl (shapeStep decl) sh

/-- `idShape(id)`: the shape attached to the root an identity is built on,
carried through the fields it has travelled.  An unshaped root has no taclet
upstream; `leaf` is the shape whose `shapeSize` is the flat default `0`. -/
def idShape (decl : Name -> Ty) : Identity -> Shape
  | .idC (.shaped _ sh) flds => shapeAt decl sh flds
  | .idC (.ofNat _) _ => .leaf

/-- **`sizeOfFixed`** — `sizeOf(fixedArr(n, sh)) ⇝ n`. -/
@[simp] theorem sizeOfFixed (n : Int) (sh : Shape) : shapeSize (.fixedArr n sh) = n := rfl

/-- **`sizeOfDyn`** — `sizeOf(dynArr(sh)) ⇝ 0`. -/
@[simp] theorem sizeOfDyn (sh : Shape) : shapeSize (.dynArr sh) = 0 := rfl

/-- **`sizeOfLeaf`** — `sizeOf(leaf) ⇝ 0`. -/
@[simp] theorem sizeOfLeaf : shapeSize .leaf = 0 := rfl

/-- **`shapeAtNil`** — `shapeAt(sh, nil) ⇝ sh`. -/
@[simp] theorem shapeAtNil (decl : Name -> Ty) (sh : Shape) : shapeAt decl sh [] = sh := rfl

/-- **`shapeAtSuffix`** — `shapeAt(sh, flds·a) ⇝ shapeAt(shapeAt(sh, flds), a)`.  No
taclet upstream (module section above). -/
theorem shapeAtSuffix (decl : Name -> Ty) (sh : Shape) (flds : List Seg) (a : Seg) :
    shapeAt decl sh (flds ++ [a]) = shapeAt decl (shapeAt decl sh flds) [a] := by
  simp [shapeAt, List.foldl_append]

/-- **`shapeAtFixed`** — `shapeAt(fixedArr(n, sh), cons(at(pk), xs)) ⇝ shapeAt(sh, xs)`.
`atMap(i)` is `Seg.at i` here, so this is **`shapeAtFixedMapElement`** too. -/
@[simp] theorem shapeAtFixed (decl : Name -> Ty) (n : Int) (sh : Shape) (i : Int) (xs : List Seg) :
    shapeAt decl (.fixedArr n sh) (.at i :: xs) = shapeAt decl sh xs := rfl

/-- **`shapeAtDyn`** — `shapeAt(dynArr(sh), cons(at(pk), xs)) ⇝ shapeAt(sh, xs)`,
and **`shapeAtDynMapElement`**. -/
@[simp] theorem shapeAtDyn (decl : Name -> Ty) (sh : Shape) (i : Int) (xs : List Seg) :
    shapeAt decl (.dynArr sh) (.at i :: xs) = shapeAt decl sh xs := rfl

/-- **`shapeAtMap`** — `shapeAt(mapOf(sh), cons(at(pk), xs)) ⇝ shapeAt(sh, xs)`. -/
@[simp] theorem shapeAtMap (decl : Name -> Ty) (sh : Shape) (i : Int) (xs : List Seg) :
    shapeAt decl (.mapOf sh) (.at i :: xs) = shapeAt decl sh xs := rfl

/-- **`shapeAtLeafElement`** (and **`shapeAtLeafMapElement`**) — `shapeAt(leaf, at(i))
⇝ leaf`, in its one-field form; along a longer path the walk goes on
from `leaf` (module section above). -/
@[simp] theorem shapeAtLeafElement (decl : Name -> Ty) (i : Int) (xs : List Seg) :
    shapeAt decl .leaf (.at i :: xs) = shapeAt decl .leaf xs := rfl

/-- **`shapeAtMember`** — `shapeAt(sh, cons(m, xs)) ⇝ shapeAt(fieldShape(m), xs)`,
for a named member: `size` is not one. -/
theorem shapeAtMember (decl : Name -> Ty) (sh : Shape) (m : Name) (xs : List Seg)
    (hm : m ≠ "length") :
    shapeAt decl sh (.field m :: xs) = shapeAt decl (fieldShape decl m) xs := by
  cases sh <;> simp [shapeAt, shapeStep, hm]

/-- **`idShapeDef`** — `idShape(idC(shaped(idp, sh), flds)) ⇝ shapeAt(sh, flds)`. -/
@[simp] theorem idShapeDef (decl : Name -> Ty) (r : IdentityPrim) (sh : Shape) (flds : List Seg) :
    idShape decl (.idC (.shaped r sh) flds) = shapeAt decl sh flds := rfl

/-! ### `init<[int]>` at its location

`init<[α]>(idC(idp, flds), a)` is split three ways by the field since
solkey `8c5c69ca25`: an element and a named member read the flat default
(`initElement`, `initMember`, the old single `defaultDef`), and
the length of a *shaped* root reads its shape's size (`initSize`).  So the
cast needs the location, as `MemValue.asIdentity` already does. -/

/-- `read<[int]>` of a memory slot read at `loc`/`a`: the slot's integer, `0`
for a non-integer, and for a never-written slot the default at that location. -/
def MemValue.asIntAt (decl : Name -> Ty) : MemValue -> Identity -> Seg -> Int
  | .prim (.int v), _, _ => v
  | .prim (.bool _), _, _ => 0
  | .ident _, _, _ => 0
  | .dflt, .idC (.shaped _ sh) flds, .field m =>
      if m = "length" then shapeSize (shapeAt decl sh flds) else 0
  | .dflt, _, _ => 0

namespace Memory

/-- **`initElement`** — `init<[prim]>(idC(idp, flds), at(pk)) ⇝
defaultValue<[prim]>`. -/
@[simp] theorem initElement (decl : Name -> Ty) (r : IdentityPrim) (flds : List Seg) (i : Int) :
    MemValue.asIntAt decl .dflt (.idC r flds) (.at i) = 0 := by
  cases r <;> rfl

/-- **`initMember`** — `init<[prim]>(idC(idp, flds), m) ⇝
defaultValue<[prim]>`, for a named member: `size` is not one. -/
theorem initMember (decl : Name -> Ty) (r : IdentityPrim) (flds : List Seg) (m : Name)
    (hm : m ≠ "length") :
    MemValue.asIntAt decl .dflt (.idC r flds) (.field m) = 0 := by
  cases r <;> simp [MemValue.asIntAt, hm]

/-- **`initSize`** — `init<[int]>(idC(shaped(idp, sh), flds), size) ⇝
sizeOf(shapeAt(sh, flds))`: a fixed-size array's length is its declared one
the moment anything reads it. -/
@[simp] theorem initSize (decl : Name -> Ty) (r : IdentityPrim) (sh : Shape) (flds : List Seg) :
    MemValue.asIntAt decl .dflt (.idC (.shaped r sh) flds) (.field "length") =
      shapeSize (shapeAt decl sh flds) := rfl

/-- An unshaped root's length defaults to the flat `0`, the case `initSize`
leaves to `defaultValue<[int]>`. -/
@[simp] theorem initSizeUnshaped (decl : Name -> Ty) (n : Nat) (flds : List Seg) :
    MemValue.asIntAt decl .dflt (.idC (.ofNat n) flds) (.field "length") = 0 := rfl

end Memory
end Theory
end Solidity
