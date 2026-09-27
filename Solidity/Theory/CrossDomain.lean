import Solidity.Theory.Storage
import Solidity.Theory.Memory

/-!
# `structMemoryRules.key` — the two copy views

```
Struct copyMem(Struct, Memory, Identity)      -- memory to storage
Memory copySt(Memory, IdentityPrim, Struct)   -- storage to memory
```

Both are constructors of `Theory/Terms.lean`'s sorts, as KeY declares them:
they are why `Struct` and `Memory` are one mutual inductive. This module is
their six taclets and nothing else.

A copy is lazy in KeY — nothing is walked at the assignment. The copied-to
side gets a **view** of the copied-from one and the reads resolve through it:
`copyMem(mtSt, mem, id)` answers every `find` by a `readR` into `mem` from
`id` — a primitive read is the slot, a struct read is the view one field
further down (`selectOnCopyMemRef`) — and `copySt(mem, r, st)` answers every `read` below `r` by a `find` into
`st`.

## What is not modelled

A view inside a view: a `copySt` whose struct is itself a `copyMem`. The read
that crosses back is `StValue.findSt`, which stops at a view, and
`Struct.find_eq_findSt` is where that is stated. No worked example nests one
and upstream has no taclet that rewrites under one.

`readCopyStIdentity` is a *corollary* here rather than a recursion of its own:
`StValue.toMemValue` sends a struct to `dflt`, so the cast at the `Identity`
sort manufactures `idC(r, flds·a)` by `defaultDefIdentity` — a reference member
of a copied struct exists as soon as its parent does, exactly as a reference
member of a fresh root does.
-/

namespace Solidity
namespace Theory

open Semantics

/-! ## `findOnCopy`, `selectOnCopyMem{Prim,Ref}` — memory to storage

The three taclets are stated through `find`, whose `copyMem` arm
(`Memory.viewRead`) answers a view before `selectSt` is reached
(`Theory/Terms.lean`, "Three arms on a view").  At a primitive sort the read
is `readR`'s; at `Struct` it is the view one field further down. -/

namespace StValue

/-- `find` on a view is the view's own read. -/
@[simp] theorem find_copyMem (mem : Memory) (id : Identity) (flds : List Seg) :
    find (Struct.copyMem mem id) flds = Memory.viewRead mem id flds := by
  cases flds with
  | nil => rfl
  | cons _ rest => cases rest <;> rfl

theorem viewRead_asInt (mem : Memory) :
    forall (flds : List Seg) (id : Identity),
      asInt (Memory.viewRead mem id flds) = (Memory.readR mem id flds).asInt
  | [], _ => rfl
  | [a], id => by
      show asInt (MemValue.ofViewAt mem id a (Memory.readIn mem id a))
        = (Memory.readIn mem id a).asInt
      cases Memory.readIn mem id a with
      | prim p => cases p <;> rfl
      | ident _ => rfl
      | dflt => rfl
  | _ :: b :: rest, _ => viewRead_asInt mem (b :: rest) _

theorem viewRead_asBool (mem : Memory) :
    forall (flds : List Seg) (id : Identity),
      asBool (Memory.viewRead mem id flds) = (Memory.readR mem id flds).asBool
  | [], _ => rfl
  | [a], id => by
      show asBool (MemValue.ofViewAt mem id a (Memory.readIn mem id a))
        = (Memory.readIn mem id a).asBool
      cases Memory.readIn mem id a with
      | prim p => cases p <;> rfl
      | ident _ => rfl
      | dflt => rfl
  | _ :: b :: rest, _ => viewRead_asBool mem (b :: rest) _

/-- **`findCopyMem`** (`findOnCopy`) — `find<[prim]>(copyMem(mtSt, mem, id), flds)
⇝ readR<[prim]>(mem, id, flds)`, at `int`.  The whole remaining path goes in
one step, as the taclet does.

The decisive step of every memory-to-storage example: it turns a storage read
into a memory read without either theory having walked anything. -/
theorem findCopyMem (mem : Memory) (id : Identity) (flds : List Seg) :
    asInt (find (Struct.copyMem mem id) flds) = (Memory.readR mem id flds).asInt := by
  rw [find_copyMem]; exact viewRead_asInt mem flds id

/-- …at `bool`. -/
theorem findCopyMem_asBool (mem : Memory) (id : Identity) (flds : List Seg) :
    asBool (find (Struct.copyMem mem id) flds) = (Memory.readR mem id flds).asBool := by
  rw [find_copyMem]; exact viewRead_asBool mem flds id

/-- **`selectOnCopyMemPrim`** — `selectSt<[prim]>(copyMem(mtSt, mem, id), a) ⇝
read<[prim]>(mem, id, a)`: `findCopyMem`'s one-field form, at `int`. -/
theorem selectOnCopyMemPrim (mem : Memory) (id : Identity) (a : Seg) :
    asInt (find (Struct.copyMem mem id) [a]) = (Memory.readIn mem id a).asInt :=
  findCopyMem mem id [a]

/-- …at `bool`. -/
theorem selectOnCopyMemPrim_asBool (mem : Memory) (id : Identity) (a : Seg) :
    asBool (find (Struct.copyMem mem id) [a]) = (Memory.readIn mem id a).asBool :=
  findCopyMem_asBool mem id [a]

/-- **`selectOnCopyMemRef`** — `selectSt<[Struct]>(copyMem(mtSt, mem, id), a) ⇝
copyMem(mtSt, mem, read<[Identity]>(mem, id, a))`: a reference member of a view
is a view itself.  The hypothesis is the sort: KeY reads at `Struct` only a
member that holds one, and a slot holding a primitive is not that. -/
theorem selectOnCopyMemRef (mem : Memory) (id : Identity) (a : Seg)
    (h : forall p, Memory.readIn mem id a ≠ .prim p) :
    asStruct (find (Struct.copyMem mem id) [a]) = Struct.copyMem mem (Memory.readId mem id a) := by
  show asStruct (MemValue.ofViewAt mem id a (Memory.readIn mem id a))
    = Struct.copyMem mem ((Memory.readIn mem id a).asIdentity id a)
  cases hv : Memory.readIn mem id a with
  | prim p => exact absurd hv (h p)
  | ident _ => rfl
  | dflt => rfl

/-- `selectOnCopyMemRef` along a whole path: a struct read out of a view is the
view at the identity the path names (`readR<[Identity]>`). -/
theorem findCopyMemStruct (mem : Memory) :
    forall (flds : List Seg) (id : Identity),
      (forall p, Memory.readR mem id flds ≠ .prim p) ->
      asStruct (find (Struct.copyMem mem id) flds) = Struct.copyMem mem (Memory.readRId mem id flds)
  | [], _, _ => rfl
  | [a], id, h => selectOnCopyMemRef mem id a h
  | a :: b :: rest, id, h => by
      rw [find_copyMem]
      show asStruct (Memory.viewRead mem (Memory.readId mem id a) (b :: rest)) = _
      rw [← find_copyMem]
      exact findCopyMemStruct mem (b :: rest) _ h

end StValue

/-! ## `readFromCopyToStorage` — storage to memory -/

namespace Memory

open MemValue

/-- **`readCopySt`** — a read below the copied root is a `find` into the
copied struct. -/
@[simp] theorem readCopySt (mem : Memory) (r : IdentityPrim) (s : Struct)
    (flds : List Seg) (a : Seg) :
    readIn (Memory.copySt mem r s) (.idC r flds) a =
      StValue.toMemValue (StValue.findSt s (flds ++ [a])) := by
  simp [readIn, Identity.root, Identity.path]

/-- **`readCopyStIdentity`** — the same read at the `Identity` sort is the
identity one field further down. The hypothesis is the sort: the member is
struct-valued. -/
theorem readCopyStIdentity (mem : Memory) (r : IdentityPrim) (s : Struct)
    (flds : List Seg) (a : Seg) {inner : Struct}
    (hs : StValue.findSt s (flds ++ [a]) = .st inner) :
    readId (Memory.copySt mem r s) (.idC r flds) a = .idC r (flds ++ [a]) := by
  simp [readId, readCopySt, hs, StValue.toMemValue, MemValue.asIdentity,
    Identity.extend]

/-- **`readCopyStOther`** — a read below any other root does not see the
copy. -/
theorem readCopyStOther (mem : Memory) (r1 r2 : IdentityPrim) (s : Struct)
    (flds : List Seg) (a : Seg) (hne : r1 ≠ r2) :
    readIn (Memory.copySt mem r1 s) (.idC r2 flds) a =
      readIn mem (.idC r2 flds) a := by
  simp [readIn, Identity.root, hne]

end Memory

end Theory
end Solidity
