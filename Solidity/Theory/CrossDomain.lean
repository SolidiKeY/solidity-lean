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
their four taclets and nothing else.

A copy is lazy in KeY — nothing is walked at the assignment. The copied-to
side gets a **view** of the copied-from one and the reads resolve through it:
`copyMem(mtSt, mem, id)` answers every `find` by a `readR` into `mem` from
`id`, and `copySt(mem, r, st)` answers every `read` below `r` by a `find` into
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

/-! ## `findOnCopy` — memory to storage -/

namespace StValue

/-- **`findCopyMem`** — `find<[α]>(copyMem(mtSt, mem, id), flds) ⇝
readR<[α]>(mem, id, flds)`. The whole remaining path goes in one step, as the
taclet does, and the empty path agrees with `findEmptyPath` through
`readREmptyPath`: both sides are the view itself.

The decisive step of every memory-to-storage example: it turns a storage read
into a memory read without either theory having walked anything. -/
@[simp] theorem findCopyMem (mem : Memory) (id : Identity) (flds : List Seg) :
    find (Struct.copyMem mem id) flds =
      MemValue.ofView mem (Memory.readR mem id flds) := by
  cases flds with
  | nil => rfl
  | cons _ rest => cases rest <;> rfl

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
