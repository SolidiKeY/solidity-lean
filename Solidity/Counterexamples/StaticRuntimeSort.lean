import Solidity.StorageTyping

/-!
# Static array and mapping sorts are not their runtime nodes

solkey gives an array type its own sort `T[]` and a mapping type its own
sort `mapping(K => V)`, each `\extends StValue` directly
(`SolJSONParser.java:1015-1030`, `valueSupersort("StValue")`) — siblings
of `Struct`, not below it. At runtime, though, a storage array or
mapping *is* a `Struct` node: `structRules.key` builds it from `mtSt`
with `at(i)` fields, and the copy taclets read it with `find<[Struct]>`
(`memoryStorageCopy`, `storageFieldWriteCopySource`, …).

So the static sort (`Ty.keySort`, what a `\hasSort`-family varcond
binds a generic to) and the runtime sort (`SVal.keySort`, what the value
found at the path is) disagree on every array and mapping, and agree on
everything else. Both halves are proved here.

The consequence upstream: `\hasSort(x, \sort(alphaSt))` on an
array-typed path binds `alphaSt := uint[]`, and the taclet's
`find<[alphaSt]>(storage, x)` is then a term of sort `uint[]` that no
`selectSt`/`find` simplification rule (all stated on `Struct`) can
consume. Today's `solidityProgramRules.key` binds only `alphaPrim` under
`\hasSort`, so the gap is latent; a future taclet that binds `alphaSt`
on an unconstrained `Path` would hit it. See `docs/solkey-feedback.md`.
-/

namespace Solidity
namespace Counterexamples
namespace StaticRuntimeSort

open Semantics

/-- A well-typed storage array is a `Struct` node whose static sort is
`uint[]` — and `Struct ≰ uint[]`. -/
theorem array_runtime_not_le_static :
    ∃ (v : SVal) (ty : Ty), v.hasTy ty = true ∧
      (v.keySort).le (ty.keySort false) = false :=
  ⟨SVal.array [] [], Ty.ref (RefTy.array Ty.uint), by decide, by decide⟩

/-- The same for a mapping: a `Struct` node whose static sort is
`mapping(int => int)`. -/
theorem mapping_runtime_not_le_static :
    ∃ (v : SVal) (ty : Ty), v.hasTy ty = true ∧
      (v.keySort).le (ty.keySort false) = false :=
  ⟨SVal.map [] (SVal.int 0), Ty.ref (RefTy.mapping Ty.uint Ty.uint),
    by decide, by decide⟩

/-- Nor the other way round: the static sort is not below `Struct`
either, so the two are simply incomparable. -/
example : (KeySort.array KeySort.int).le KeySort.struct = false := by decide
example : (KeySort.mapping KeySort.int KeySort.int).le KeySort.struct = false := by decide

/-- Where the two sides do agree: primitives (`StorageTyping.hasTy_keySort_of_primitive`)
and structs. -/
example : (SVal.struct []).keySort = (Ty.ref (RefTy.struct "Person")).keySort false := rfl

theorem prim_runtime_eq_static {ty : Ty} {v : SVal}
    (hprim : ty.isPrimitive = true) (h : v.hasTy ty = true) :
    (v.keySort).le (ty.keySort false) = true := by
  rw [hasTy_keySort_of_primitive hprim h]
  exact KeySort.le_refl _

/-- The safe reads are the ones the corpus actually has: a bound of
`Prim` (`alphaPrim`) never binds on an array or mapping, so the gap
cannot be reached through `\hasSort(x, \sort(alphaPrim))`. -/
example : ((Ty.ref (RefTy.array Ty.uint)).keySort false).le KeySort.prim = false := by decide
example : ((Ty.ref (RefTy.mapping Ty.uint Ty.uint)).keySort false).le KeySort.prim = false := by
  decide

/-- …while a bound of `StValue` (`alphaSt`) would. -/
example : ((Ty.ref (RefTy.array Ty.uint)).keySort false).le KeySort.stValue = true := by decide

end StaticRuntimeSort
end Counterexamples
end Solidity
