import Solidity.Theory.Terms
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

/-- `read<[α]>(mtMem, id, a) ⇝ default<[α]>(id, a)`. -/
@[simp] theorem readFromEmptyMemory (id : Identity)
    (a : Seg) : readIn mtMem id a = dflt := rfl

/-- `read<[α]>(addM(mem, idp1), idC(idp2, flds), a)`: KeY splits on
`idp1 = idp2` and answers `default<[α]>` on the fresh root, reading through
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

/-- `defaultValueInt` / `defaultDef`: a primitive default is `0`. -/
@[simp] theorem defaultDefInt : MemValue.asPrim dflt = MVal.int 0 := rfl

/-- **`defaultDefIdentity`** — `default<[Identity]>(idC(idp, flds), a)` is
`idC(idp, consr(flds, a))`.  The taclet that gives a fresh root its members. -/
@[simp] theorem defaultDefIdentity (r : IdentityPrim) (flds : List Seg) (a : Seg) :
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

/-- The paper's `readREmptyPath`: the empty path reads the identity itself. -/
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
that is what keeps it structural and every chain in `Paper/Theory.lean` steps
through `readREmpty`/`readRCons` by `rfl`.  This is the same rule in KeY's
spelling, as a theorem. -/

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
end Theory
end Solidity
