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

## Upstream Group 06 reproduction (2026-10-26)

The Group 06 current-master reproduction confirms that
`array_of_recursive_struct.sol`, `recursive_structs.sol` and
`struct_reference.sol` remain broken in both required pipelines at the ordinary
import boundary. The finite library-struct repair does not broaden recursive
source admission or migrate the core representation. These are explicit
ordinary-model exclusions, not adapter passes or universal counterexamples to
the standalone graph foundation. Complete gaps and provenance are retained in
[the Group 06 evidence](../../tests/upstream/group06.json); the finite repair and
its remaining boundaries are recorded in
[declarations-metadata.md](declarations-metadata.md#upstream-group-06-finite-library-struct-identity-2026-10-26).

The resumed Group 06 finite implementation from `615bd3fa` increases actual
both-pipeline passes from five to twelve of the fifteen assigned fixtures. It
leaves the same three recursive fixtures broken; the final reports retain both
mode gaps and every original input/expectation. The independent reviews confirm
that recursive memory allocation/deletion and schema-indexed storage aliases
still need ordinary interpreter integration and operation correspondence.
[The continuation handoff](declarations-metadata.md#upstream-group-06-continuation-from-615bd3fa)
distinguishes implemented finite repairs from these unimplemented interfaces.
There is no finite-depth substitute or new recursive source admission in that
patch.

Final Group 06 evidence after `49b55764` still records twelve both-pipeline
passes and the same three recursive import failures. TestSuite kernel checking,
frozen sort and corpus parity pass independently. The full default library
check remains resource-blocked on the unchanged array-decision example, not
on a recursive source admission attempt. See the final validation continuation
in [declarations-metadata.md](declarations-metadata.md) and the per-fixture
[evidence](../../tests/upstream/group06.json). No ordinary recursive admission
or graph representation migration is claimed by this lane.

## Group 06 operation-boundary diagnosis after d4a55688

The authorized continuation inspected the final, unchanged `struct_reference`
legacy/viaIR reports rather than rerunning the same failed admission. Both
first report `check()` reading omitted state root `data` at adapted compiler
source line 10; `set()` has the same root failure at adapted line 16. These
include the runner's two preamble lines: the archived source lines are 8
(`return data.z`) and 14 (`data.z = 2`). The compiler AST identifies
`s2` as declaration 9, its `uint32 z` member as 3, recursive mapping member
as 8, and state root `data` as 12. The mapping's value refers back to 9.
`Body.lean`'s local `shapes` checker in `readStructs` rejects this declaration
before `Frontend/SolcJson/Contract.lean`
can retain `data`. The earliest evaluated read would be `data.z`, followed
by `data.recursive[0].z`; this is not a failed graph lookup at runtime.

The exact missing interface is a schema-indexed counterpart of ordinary
`SPath`/`Loc`, `SRef`, `Storage`, alias locals and `State`, connected to the
existing scoped run and its typed terms. The graph already represents the
root as a node with a primitive member and a mapping back to that node.
`Step.field`, `Step.key`, `Path.append`, `Path.read_save`, and
`Value.find_write` provide typed graph operations and local laws. They do
not supply the ordinary execution interface: `SPath.resolveT`,
`Loc.resolveT`, `declStorage` and `assign` currently require ordinary `Ty`.
That type's struct table has strict field-rank descent. A cyclic root cannot
have a `Legacy.Layout` certificate; extending the mapping-only
`KeyPath.find_encode` theorem with field cases would still require that
impossible finite root certificate.

For this fixture, an operation-preserving integration must prove all of:

- Resolving `data.recursive` and binding `map`, then resolving `map[0]`
  and binding `inner`, denotes the same schema root plus composed typed
  field/key path. Alias binding must not copy a subtree.
- Primitive reads and successful writes commute with that resolution,
  including untouched keys, implicit defaults and field/key composition.
  Writes through `inner` must be observed by later reads through `data`.
- `inner.recursive[1].z + 1` is evaluated before the destination write;
  `uint8` keys and `uint32` member arithmetic retain their source ranges.
  Failure, rollback and exhaustion remain the ordinary run's outcomes.
- The typed state relation is preserved by each admitted source operation,
  so composition establishes the original `check → set → check` observations
  (`false`, empty return, `true`), with every original call retained.

These are required theorem obligations, not declarations added to the trust
base. No existing theorem states this commuting execution relation. A
fixture-specific graph evaluator would bypass it and is not an admission
repair. The scope decision is therefore to stop dependent recursive admission:
this requires a representation/semantic integration across the ordinary run,
signatures, typing and calculus, rather than a small graph API extension.
Before undertaking it, retain the performance warning and speed-history
review above; this continuation makes no representation change.

The other two exact fixtures require more than that storage interface.
`array_of_recursive_struct` allocates 42 recursive memory elements inside a
fixed-array/struct constructor and reads the resulting length.
`recursive_structs` allocates ten recursive memory elements, deletes the
memory root, then clears the storage root. The standalone foundation is
storage-only. A checked graph heap must carry allocation/alias typing and
mapping-freedom in its types, and prove allocation, field/index lookup,
initialization and memory deletion agreement. Storage clearing additionally
needs the ordinary `delete` correspondence to `Value.clear`. Layout rank is
not a bound on dynamic path depth; finite unrolling or deleting the source
operations would not discharge these obligations. All three fixture statuses
remain broken in both pipelines, with their previous reports preserved.

The same continuation's checked arithmetic normalization repair resolves the
original default array verdict check: the unchanged module passes all three
pins in 11 s, and the full serial default check passes. This is independent
of recursive source admission and leaves the three gaps above unrepaired.
Final read-only finder and skeptic reviews confirm the documented boundary;
current build, fixture and baseline-limit evidence is recorded in the final
monitor section of [declarations-metadata.md](declarations-metadata.md).
