import Solidity.DecEq

/-!
# `memoryRules.key` as a term algebra

The memory twin of `Theory/Storage.lean`: `mtMem`, `write`, `addM`, `read`,
`readR` and `new` (`memoryHeader.key`, `memoryRules.key`) as total Lean
functions, one theorem per taclet.  The denotation into the interpreter's heap
lives in `Update/Theory.lean`, beside the update it is used to read — it needs
`writeMemField`/`allocDefault`, which this module deliberately does not
import so that the algebra stays as cheap to elaborate as the storage one.

Unlike `structRules.key`, this file has **no counterpart in the fundamentals
repository**: that one models `read` and nothing else, so `readOnWrite`,
`readOnAddM`, the `new` family and the `default` family are transcribed here
from the `.key` source directly.

## Identities are KeY's path identities

A memory location is named the way KeY names it: `idC(idp, flds)`, a root of
sort `IdentityPrim` together with the field path that reaches the location
from it.  `idCC(idp)` is `idC(idp, [])`, and `defaultDefIdentity` manufactures
`idC(idp, flds · a)` on the fly, which is what makes a reference member of a
freshly added root *exist* without anything being allocated for it — the
paper's "this is how Solidity's implicit creations are modelled without
allocating anything".

The interpreter is the other way round: every object it allocates gets its own
`Nat` and a path is resolved to one *before* any read or write happens
(`Wp.memBase`, `Semantics.readM`).  Resolving a path identity against a
concrete heap is therefore a function of this module (`resolve`), used by the
denotation in `Update/Theory.lean` and by the `pre` leaf below; the algebra
itself never resolves anything, exactly as KeY's does not.

`readR` walks a whole path one field at a time, resolving each field to the
identity it names before reading the next, so the chain-walking layer —
`readR`, `readREmpty`, `readRCons`, `idCCDef`, `defaultDefIdentity` — is here
and proved.

`addM` carries two things: KeY's own root, which is what lets `readOnAddM` and
`newFromAdd` branch on it exactly as the taclets do, and the allocated type,
which KeY does not carry.  The type is the one place this is eager where KeY
is lazy, for the same reason as the storage side: KeY resolves a never-written
slot of a fresh object to `default<[α]>` at whatever sort the reader asks for,
while `Semantics.allocDefault` materializes the object when it is allocated,
so the term has to know its type to denote.
-/

namespace Solidity
namespace Theory

open Semantics

/-- `\unique Identity idC(IdentityPrim, List)` (`memoryRules.key`): the
identity reached from a root along a path of fields.  `\unique` is
injectivity, which `DecidableEq` supplies — `memoryExample2` closes on
exactly that. -/
inductive Identity where
  | idC (root : Nat) (path : List Seg)
  deriving Repr, DecidableEq

namespace Identity

/-- `idCC(idp)` — the root itself, as an identity. -/
@[match_pattern] abbrev idCC (r : Nat) : Identity := .idC r []

/-- `idC(idp, consr(flds, a))`: the identity one field further down. -/
def extend : Identity -> Seg -> Identity
  | .idC r p, a => .idC r (p ++ [a])

/-- The root a path identity hangs from. -/
def root : Identity -> Nat
  | .idC r _ => r

@[simp] theorem root_idC (r : Nat) (p : List Seg) : (Identity.idC r p).root = r := rfl

/-- The path from the root. -/
def path : Identity -> List Seg
  | .idC _ p => p

@[simp] theorem path_idC (r : Nat) (p : List Seg) : (Identity.idC r p).path = p := rfl

@[simp] theorem extend_idC (r : Nat) (p : List Seg) (a : Seg) :
    (Identity.idC r p).extend a = .idC r (p ++ [a]) := rfl

end Identity

/-- A memory slot's contents (`memoryHeader.key`: `Prim, Identity ⊑ MemValue`).
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
  | .ref n => .ident (.idCC n)

namespace MemValue

/-! ## Casts

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

/-- A term of solkey's memory theory. -/
inductive Memory where
  /-- `\unique Memory mtMem`. -/
  | mtMem
  /-- The pre-state heap as an opaque leaf — the reason this algebra, unlike
  `Theory/Storage.lean`'s, is a theory of terms *over a concrete state*. -/
  | pre
  /-- `write(mem, id, a, v)`. -/
  | write (mem : Memory) (id : Identity) (a : Seg) (v : MemValue)
  /-- `addM(mem, idp)`, carrying the allocated type beside the root — see the
  docstring. -/
  | addM (mem : Memory) (idp : Nat) (ty : RefTy)
  deriving Repr

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
  | .idC r p => resolveFrom h r p

/-- A root identity resolves to its root.  The equation `Update/Theory.lean`
needs to keep its bridges `rfl`. -/
@[simp] theorem resolve_idCC (h : List (Nat × MObj)) (n : Nat) :
    resolve h (.idCC n) = some n := rfl

/-! ## `read`

KeY's read is total and sort-indexed; here it is total and sort-free, with
`dflt` standing for `default<[α]>(id, a)` until a cast resolves it.  On the
`pre` leaf the read is the interpreter's own, which is what makes a taclet
theorem below a statement about a real heap. -/

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

/-- `read<[α]>(mem, id, a)`, against a concrete pre-state heap. -/
def readIn (h : List (Nat × MObj)) : Memory -> Identity -> Seg -> MemValue
  | mtMem, _, _ => dflt
  | pre, id, a => preReadId h id a
  | write mem id1 a1 v, id2, a2 =>
      if id1 = id2 ∧ a1 = a2 then v else readIn h mem id2 a2
  | addM mem idp _, id, a =>
      if idp = id.root then dflt else readIn h mem id a

/-- `read<[Identity]>(mem, id, a)`. -/
def readId (h : List (Nat × MObj)) (mem : Memory) (id : Identity) (a : Seg) :
    Identity :=
  (readIn h mem id a).asIdentity id a

/-! ## `readR`

`readR<[α]>(mem, id, flds)` follows a whole path from an identity, resolving
each field to the identity it names before reading the next.  KeY states it
with `firsts`/`last`; the same recursion from the front is `readRId` composed
with one final `read`, and `readRCons` below is that equality. -/

/-- The identity a whole path names: `readR<[Identity]>`. -/
def readRId (h : List (Nat × MObj)) (mem : Memory) : Identity -> List Seg -> Identity
  | id, [] => id
  | id, a :: rest => readRId h mem (readId h mem id a) rest

/-- `readR<[α]>(mem, id, flds)`.  The empty path reads the identity itself
(the paper's `readREmptyPath`); a non-empty one resolves all but the last
field and reads there. -/
def readR (h : List (Nat × MObj)) (mem : Memory) (id : Identity) :
    List Seg -> MemValue
  | [] => MemValue.ident id
  | [a] => readIn h mem id a
  | a :: b :: rest => readR h mem (readId h mem id a) (b :: rest)

/-! ## The taclets of `memoryRules.key` -/

/-- `read<[α]>(write(mem, id1, a1, v), id2, a2)`. -/
@[simp] theorem readOnWrite (h : List (Nat × MObj)) (mem : Memory)
    (id1 id2 : Identity) (a1 a2 : Seg) (v : MemValue) :
    readIn h (write mem id1 a1 v) id2 a2 =
      if id1 = id2 ∧ a1 = a2 then v else readIn h mem id2 a2 := rfl

/-- `read<[α]>(mtMem, id, a) ⇝ default<[α]>(id, a)`. -/
@[simp] theorem readFromEmptyMemory (h : List (Nat × MObj)) (id : Identity)
    (a : Seg) : readIn h mtMem id a = dflt := rfl

/-- `read<[α]>(addM(mem, idp1), idC(idp2, flds), a)`: KeY splits on
`idp1 = idp2` and answers `default<[α]>` on the fresh root, reading through
otherwise.  This is that taclet. -/
@[simp] theorem readOnAddM (h : List (Nat × MObj)) (mem : Memory) (idp : Nat)
    (ty : RefTy) (id : Identity) (a : Seg) :
    readIn h (addM mem idp ty) id a =
      if idp = id.root then dflt else readIn h mem id a := rfl

/-- `readAddEqual`: a read of the root just added is its default. -/
@[simp] theorem readAddEqual (h : List (Nat × MObj)) (mem : Memory) (r : Nat)
    (ty : RefTy) (flds : List Seg) (a : Seg) :
    readIn h (addM mem r ty) (.idC r flds) a = dflt := by
  simp [readOnAddM, Identity.root]

/-- `readAddDifferent`: a read below any other root passes through. -/
theorem readAddDifferent (h : List (Nat × MObj)) (mem : Memory) (r1 r2 : Nat)
    (ty : RefTy) (flds : List Seg) (a : Seg) (hne : r1 ≠ r2) :
    readIn h (addM mem r1 ty) (.idC r2 flds) a =
      readIn h mem (.idC r2 flds) a := by
  simp [readOnAddM, Identity.root, hne]

/-- `defaultValueInt` / `defaultDef`: a primitive default is `0`. -/
@[simp] theorem defaultDefInt : MemValue.asPrim dflt = MVal.int 0 := rfl

/-- **`defaultDefIdentity`** — `default<[Identity]>(idC(idp, flds), a)` is
`idC(idp, consr(flds, a))`.  The taclet that gives a fresh root its members. -/
@[simp] theorem defaultDefIdentity (r : Nat) (flds : List Seg) (a : Seg) :
    MemValue.asIdentity dflt (.idC r flds) a = .idC r (flds ++ [a]) := rfl

/-- `idCCDef`: `idCC(idp) ⇝ idC(idp, nil)`. -/
@[simp] theorem idCCDef (r : Nat) : Identity.idCC r = Identity.idC r [] := rfl

/-- `readREmpty`: a one-field path is one read. -/
@[simp] theorem readREmpty (h : List (Nat × MObj)) (mem : Memory)
    (id : Identity) (a : Seg) : readR h mem id [a] = readIn h mem id a := rfl

/-- `readRCons`: a longer path resolves its first field to an identity and
continues from there.  KeY writes the same step as `firsts`/`last`. -/
@[simp] theorem readRCons (h : List (Nat × MObj)) (mem : Memory)
    (id : Identity) (a1 a2 : Seg) (flds : List Seg) :
    readR h mem id (a1 :: a2 :: flds) =
      readR h mem (readId h mem id a1) (a2 :: flds) := rfl

/-- The paper's `readREmptyPath`: the empty path reads the identity itself. -/
@[simp] theorem readREmptyPath (h : List (Nat × MObj)) (mem : Memory)
    (id : Identity) : readR h mem id [] = MemValue.ident id := rfl

/-! ## `new`

`new(mem, idp)` is a *predicate* in KeY, and the only one in the memory
theory: it is what a freshly allocated identity's `\add` clause asserts.  Its
three taclets are the three ways a memory term can be built. -/

/-- `new(mem, idp)` against a concrete pre-state heap: `idp` is unallocated. -/
def new (h : List (Nat × MObj)) : Memory -> Nat -> Bool
  | mtMem, _ => true
  | pre, idp => (lookupBy idp h).isNone
  | write mem _ _ _, idp => new h mem idp
  | addM mem idp1 _, idp2 => if idp1 = idp2 then false else new h mem idp2

/-- `new(mtMem, idp) ⇝ true`. -/
@[simp] theorem newFromEmptyMemory (h : List (Nat × MObj)) (idp : Nat) :
    new h mtMem idp = true := rfl

/-- `new(write(mem, id1, a1, v), idp) ⇝ new(mem, idp)` — writing a slot
allocates nothing. -/
@[simp] theorem newFromWrite (h : List (Nat × MObj)) (mem : Memory)
    (id : Identity) (a : Seg) (v : MemValue) (idp : Nat) :
    new h (write mem id a v) idp = new h mem idp := rfl

/-- **`newFromAdd`** — `new(addM(mem, idp1), idp2)` is `false` when the two
agree and recurses otherwise.  The taclet, not an approximation of it: the
root `addM` allocates is carried in the term. -/
@[simp] theorem newFromAdd (h : List (Nat × MObj)) (mem : Memory)
    (idp1 : Nat) (ty : RefTy) (idp2 : Nat) :
    new h (addM mem idp1 ty) idp2 =
      if idp1 = idp2 then false else new h mem idp2 := rfl

/-- `newAddSame`: the root just added is not fresh. -/
@[simp] theorem newAddSame (h : List (Nat × MObj)) (mem : Memory) (r : Nat)
    (ty : RefTy) : new h (addM mem r ty) r = false := by simp

/-- `newAddDifferent`: any other root is as fresh as it was. -/
theorem newAddDifferent (h : List (Nat × MObj)) (mem : Memory) (r1 r2 : Nat)
    (ty : RefTy) (hne : r1 ≠ r2) :
    new h (addM mem r1 ty) r2 = new h mem r2 := by simp [hne]

end Memory
end Theory
end Solidity
