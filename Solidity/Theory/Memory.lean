import Solidity.DecEq

/-!
# `memoryRules.key` as a term algebra

The memory twin of `Theory/Storage.lean`: `mtMem`, `write`, `addM`, `read`
and `new` (`memoryHeader.key`, `memoryRules.key`) as total Lean functions,
one theorem per taclet.  The denotation into the interpreter's heap lives in
`Update/Theory.lean`, beside the update it is used to read — it needs
`writeMemField`/`allocDefault`, which this module deliberately does not
import so that the algebra stays as cheap to elaborate as the storage one.

Unlike `structRules.key`, this file has **no counterpart in the fundamentals
repository**: that one models `read` and nothing else, so `readOnWrite`,
`readOnAddM`, the `new` family and the `default` family are transcribed here
from the `.key` source directly.

## Identities are resolved, and KeY's are not

This is the one real modelling difference, and it is worth stating plainly.
KeY addresses a memory object by a **path identity**, `idC(idp, flds)`: a
root allocation plus the field chain that reaches it, with
`defaultDefIdentity` manufacturing `idC(idp, consr(flds, a))` on the fly and
`readR`/`firsts`/`last` walking such a chain one field at a time.  The
interpreter gives every allocated object its own `Nat` and resolves a path to
one *before* any read or write happens (`Wp.memBase`, `Semantics.readM`).

So `Identity` here is that resolved `Nat`.  What is lost is exactly the
chain-walking layer — `readR`, `readREmpty`, `readRCons`, `idCCDef`,
`defaultDefIdentity` — whose whole job is to get from a path to the object
KeY's `read` then indexes.  Those five have no theorem below and are listed
as such in `docs/lean-key-rule-map.md`; everything that says what a *read of
a write* or a read of a *fresh* object means is here and proved.

Eager where KeY is lazy, for the same reason as the storage side: `addM`
carries the allocated type, because `readOnAddM` resolves a never-written
slot of a fresh object to `default<[α]>` at whatever sort the reader asks
for, while `Semantics.allocDefault` materializes the object when it is
allocated.
-/

namespace Solidity
namespace Theory

open Semantics

/-- A memory slot's contents (`memoryHeader.key`: `Prim, Identity ⊑ MemValue`).
`dflt` is `defaultValue<[α]>`/`defVal`, resolved on read. -/
inductive MemValue where
  | mval (v : MVal)
  | dflt
  deriving Repr, DecidableEq

/-- A term of solkey's memory theory. -/
inductive Memory where
  /-- `\unique Memory mtMem`. -/
  | mtMem
  /-- The pre-state heap as an opaque leaf — the `StValue.sval` role, and the
  reason the algebra is a theory of terms *over a concrete state*. -/
  | pre
  /-- `write(mem, id, a, v)`. -/
  | write (mem : Memory) (id : Nat) (a : Seg) (v : MemValue)
  /-- `addM(mem, idp)`, carrying the allocated type — see the docstring. -/
  | addM (mem : Memory) (ty : RefTy)
  deriving Repr

namespace Memory

open MemValue

/-! ## `read`

KeY's read is total and sort-indexed; here it is total and sort-free, with
`dflt` standing for `default<[α]>(id, a)` until a cast resolves it.  On the
`pre` leaf the read is the interpreter's own, which is what makes a taclet
theorem below a statement about a real heap. -/

/-- A slot of the pre-state heap, `Semantics.readM` at one segment with its
halts read as `dflt` (KeY's reads do not fault; the bounds test is the
taclet's guard). -/
def preRead (h : List (Nat × MObj)) (id : Nat) (a : Seg) : MemValue :=
  match lookupBy id h, a with
  | some (MObj.struct fields), Seg.field f =>
      match lookupBy f fields with
      | some v => mval v
      | none => dflt
  | some (MObj.array elems), Seg.at i =>
      if h : 0 ≤ i ∧ i.toNat < elems.length then mval (elems.get ⟨i.toNat, h.2⟩)
      else dflt
  | _, _ => dflt

/-- `read<[α]>(mem, id, a)`, against a concrete pre-state heap.  A freshly
added object has no written slot yet, so a read of one falls through to the
leaf — KeY's `readOnAddM`, whose `idp1 = idp2` branch answers
`default<[α]>`. -/
def readIn (h : List (Nat × MObj)) : Memory -> Nat -> Seg -> MemValue
  | mtMem, _, _ => dflt
  | pre, id, a => preRead h id a
  | write mem id1 a1 v, id2, a2 =>
      if id1 = id2 ∧ a1 = a2 then v else readIn h mem id2 a2
  | addM mem _, id, a => readIn h mem id a

/-! ## The taclets of `memoryRules.key` -/

/-- `read<[α]>(write(mem, id1, a1, v), id2, a2)`. -/
@[simp] theorem readOnWrite (h : List (Nat × MObj)) (mem : Memory)
    (id1 id2 : Nat) (a1 a2 : Seg) (v : MemValue) :
    readIn h (write mem id1 a1 v) id2 a2 =
      if id1 = id2 ∧ a1 = a2 then v else readIn h mem id2 a2 := rfl

/-- `read<[α]>(mtMem, id, a) ⇝ default<[α]>(id, a)`. -/
@[simp] theorem readFromEmptyMemory (h : List (Nat × MObj)) (id : Nat) (a : Seg) :
    readIn h mtMem id a = dflt := rfl

/-- `read<[α]>(addM(mem, idp), id, a)`: a fresh object has no written slot, so
the read passes through.  KeY splits on `idp1 = idp2` and answers
`default<[α]>` on the fresh one; here the object *is* materialized at
allocation, so the pre-state leaf answers instead — which is the same value
and the reason `addM` carries its type. -/
@[simp] theorem readOnAddM (h : List (Nat × MObj)) (mem : Memory) (ty : RefTy)
    (id : Nat) (a : Seg) : readIn h (addM mem ty) id a = readIn h mem id a := rfl

/-- `default<[prim]>(idC(idp, flds), a) ⇝ defaultValue<[prim]>` — the cast
that resolves a sort-free default at a primitive sort. -/
def asPrim : MemValue -> MVal
  | mval v => v
  | dflt => MVal.int 0

/-- `defaultValueInt`. -/
@[simp] theorem defaultDefInt : asPrim dflt = MVal.int 0 := rfl

/-! ## `new`

`new(mem, idp)` is a *predicate* in KeY, and the only one in the memory
theory: it is what a freshly allocated identity's `\add` clause asserts.  Its
three taclets are the three ways a memory term can be built. -/

/-- `new(mem, idp)` against a concrete pre-state heap: `idp` is unallocated. -/
def new (h : List (Nat × MObj)) : Memory -> Nat -> Bool
  | mtMem, _ => true
  | pre, idp => (lookupBy idp h).isNone
  | write mem _ _ _, idp => new h mem idp
  | addM mem _, idp => new h mem idp

/-- `new(mtMem, idp) ⇝ true`. -/
@[simp] theorem newFromEmptyMemory (h : List (Nat × MObj)) (idp : Nat) :
    new h mtMem idp = true := rfl

/-- `new(write(mem, id1, a1, v), idp) ⇝ new(mem, idp)` — writing a slot
allocates nothing. -/
@[simp] theorem newFromWrite (h : List (Nat × MObj)) (mem : Memory) (id : Nat)
    (a : Seg) (v : MemValue) (idp : Nat) :
    new h (write mem id a v) idp = new h mem idp := rfl

/-- `new(addM(mem, idp1), idp2)`: KeY answers `false` when the two agree and
recurses otherwise.  Here the identity `addM` mints is not in the term — it is
`nextId`, read at denotation time — so the recursion is unconditional and the
`idp1 = idp2` case is discharged where the identity is known, by
`SemanticsProperties.nextId_fresh`. -/
@[simp] theorem newFromAdd (h : List (Nat × MObj)) (mem : Memory) (ty : RefTy)
    (idp : Nat) : new h (addM mem ty) idp = new h mem idp := rfl

end Memory
end Theory
end Solidity
