# Recursive types: graph storage

`recursiveTypes` is **missing** in the ordinary pipeline: `solc_import`,
`Stmt`, `State`, `Spec`, terms, the heap and the taclets do not accept
recursive structs. What exists is a standalone typed graph storage API
(`Solidity/Semantics/RecursiveStorage.lean` and its submodules) with copy
admission and a bridge to ordinary values, exercised by
`Examples/RecursiveCopy.lean`.

## Representation

- `Solidity.TypeGraph.Schema n` names nodes by `Fin n` and compiler declaration
  IDs; fields have typed positions. Its rank follows struct and fixed-array
  edges and stops at mapping and dynamic-array edges. `Schema.no_inline_cycle`
  rules out nonempty inline cycles, so direct and fixed recursion get no
  certificate.
- `Value G T` and `Slot G T` are strictly positive, well-founded inductives:
  fields are dependent functions, array slots functions on bounded positions,
  mapping slots functions on the bounded key sorts. No erased value or untyped
  fallback. Missing slots produce the default only when read. A stored value has
  no pointer cycle, though a path may follow a recursive mapping edge any number
  of times. `defaultBelow` uses a proved layout bound; `clear` recurses on
  existing children, never on `sizeOf`.
- Arrays separate live length `Fin (2^256)` from retained extent
  `Fin (2^256+1)`. Deletion clears the live prefix, keeps old shadows and
  extent, and stops at the first mapping. Empty push keeps reference elements
  but resets the new primitive slot (as `pushSlot` does); pop clears the last
  live slot.
- `Value.ObsEq` observes failed reads, primitive values, live lengths and
  extents. Raw equality separates an absent child from a stored default.

## Interfaces

- **Copy** (`Semantics/RecursiveStorage/Copy.lean`) is by induction on present source
  values: an absent source slot clears the destination instead of unfolding
  the schema, so defaults cannot allocate recursively. It keeps destination
  mappings, ignores source shadows, clears the shortened live suffix and keeps
  older shadows. `copyAt` captures the source before writing, so overlapping
  paths are fine. No raw equality between copy and source is claimed.
- **Admission** (`Semantics/RecursiveStorage/Admission.lean`). `CopyPermit.check`
  returns a typed certificate that `assign`/`assignAt` require. Its closure
  follows node, dynamic- and fixed-array edges and rejects mappings (layout
  rank alone cannot show mapping freedom). Permits are inherited along typed
  paths, and `no_mapping_path` rules out reachable mappings. So guarded
  mapping-free cycles are accepted and mapping-containing assignment is
  refused (solc error 9214). The JSON importer does not call it yet.
- **Bridge** (`Semantics/RecursiveStorage/Legacy.lean`). `Layout G A B` and
  `FieldLayouts` relate ordinary intrinsic types to graph types: primitives,
  structs, dynamic arrays, legal fixed sizes, mappings. Mapping slots hold
  pointwise legacy lookups, so arbitrary fallback values need no
  canonical-default hypothesis. Legacy shadows are capped at the
  word-addressable extent. `writeLegacy` writes an `SVal` at a typed path;
  `assignLegacy` also needs a permit. Proved: read-back, and commutation of
  `SVal.find` with graph reads along finite mapping-key chains.
- **Observations** (`Semantics/RecursiveStorage/Observations.lean`): equivalence laws,
  observation through appended paths, descent to read subtrees, implicit
  versus explicit default mapping slots.

## Cost

The ordinary indexed representation was not migrated: `323951dd`, `3929cbc2`
and `01dd890d` explain the encoded-name struct table, and `d0c13aba`,
`2f41a68a` keep recursor/match twins chosen for checking cost. Carrying a
graph through the ordinary signatures will rebuild broadly and may slow
elaboration. Functional slots give no efficient enumeration, printing or
executable equality, and updates keep closures, so lookups can grow with
history. Measure before any migration.

## Left

- Congruence of `ObsEq` under save, delete, push/pop and copy; general
  field/index path commutation; update/copy correspondence with the ordinary
  storage.
- Shared type foundations (to avoid an AST/graph import cycle), admission of
  compiler declaration graphs, and migration of storage, heap, state,
  signature, terms, typing, notation, printers, rules and soundness.
- Recursive memory-to-storage copying must handle legal heap cycles with an
  explicit exhaustion/divergence policy; the old decreasing `tyRank` argument
  does not cover it. Copying synthesized defaults needs its own argument (a
  default allocator can recurse on layout rank).

## Reference check

`node scripts/check-recursive-types.mjs SOLJSON_FILE NODE_MODULES_DIRECTORY`
checks the pinned 0.8.38 compiler, both pipelines, the EVM vectors and the
rejections (direct, fixed and mutual-inline recursion; recursive external ABI
arguments; mapping-bearing memory parameters). The legal memory-alias cycle is
a reference-only case, outside this storage API.
