import Solidity.Semantics.Storage.Values
import Solidity.Semantics.Storage.Ops
import Solidity.Semantics.Storage.Anon

/-!
# Typed storage

A storage value indexed by its type (`docs/intrinsic.md`, Decision 4, M4b):
`SVal T` is the tree of `structRules.key` with the shape `T` gives it, so a
struct has exactly the members `structDef` lists, in order, each of its own
type, an array's elements are all of its element type, a fixed-size array has
exactly its length, and a mapping's values are all of its value type.
`Storage C` is the contract's state variables as one such struct
(`SFields C.vars`), and a typed path `Path T U` leads from a `T` to a `U`, so
the storage operations are total except where the program's index is out of
bounds: they return an `Option`, `none` for that revert (`TRes.ofOpt`).

The shapes are solkey's storage trees (`structRules.key`): an array keeps
the slots past its end (`shadow`), a mapping its default.  A fixed-size
array keeps none (no operation puts one there).  (The untyped storage this
mirrored went at W10.5.6.)

Defaults (`SVal.dflt`) are structural on the rank `structDef_rank_lt`
certifies, so the kernel can reduce them; their fuel is `rankBound`, which
reads no struct name.

Nothing the kernel evaluates `match`es on the indexed families (Gate G0,
conditions 1 and 2): `find`, `findLive`, `save`, `SFields.get`/`set` and
`Path.append` are written with the recursors (`Path.rec` over `SVal.view`,
`SFields.rec`), `Path.index` and `inBounds` with `casesOn`, the functions on
a whole value are folds (`SVal.fold`), and the array operations read their
array through `SVal.view`.  Each recursor form has a `match` twin as its
compiled form (`implemented_by`) and a theorem that they are equal
(`SVal.fold_eq_foldM`, `SVal.defaultOf_eq_defaultOfM`, …); `defaultOf`,
`strip`, `overlay` and the `toList`s have their own twins rather than
`SVal.foldM`, which is strict and would walk a mapping's entries.  These
state their equations and are irreducible, so a proof rewrites them as it
would a `match` (`Solidity/Eqns.lean`).

The module is split by topic, each piece importing the one before
(`Semantics/Storage/Values.lean`, `Semantics/Storage/Ops.lean`,
`Semantics/Storage/Anon.lean`);
this module imports them all.
-/
