# Recursive types: storage foundation and copy compatibility

Integration status (2026-10-26): included in the shared checkout. Current
combined validation is tracked in [integration.md](integration.md).
Worker handoff statuses and isolated validation results below are historical;
they neither report the current combined checks nor establish full source support.

`recursiveTypes` remains **missing in the ordinary source/interpreter/calculus
pipeline**. M1 supplies a checked standalone type graph and storage API.
The M2 patch adds copy admission, snapshot copy and a finite-layout bridge to
ordinary interpreter values. M2 was handed off as `patch_ready_unvalidated`
and is now included in the combined integration; validation remains in progress
in integration.md.
It does not make `solc_import`, `Stmt`, `State`, `Spec`, terms,
the heap or existing taclets accept recursive structs.

## M2: integrated storage interfaces

`Semantics/RecursiveStorage/Legacy.lean` imports the ordinary storage API.
`Legacy.Layout G A B` and `FieldLayouts` relate existing intrinsic types and
ordered fields to graph types. Encoding handles primitives, structs, dynamic
arrays, legal fixed sizes and mappings. Mapping slots contain pointwise
legacy lookup results, preserving arbitrary fallback values without a
canonical-default hypothesis. Legacy shadows are capped at the word-addressable
extent; there is no equality claim for larger raw extents.

`writeLegacy` embeds an ordinary `SVal` and calls graph assignment at a typed
path into a recursive root. `assignLegacy` additionally requires a copy
permit. Proof scripts give read-back of that assignment and commutation of
ordinary `SVal.find` with graph reads and head observations along every finite
mapping-key chain. Concrete regressions also exercise struct fields, fixed
arrays and live/retained dynamic-array reads. General field/index path
commutation and operation-preserving compatibility remain open.

`Solidity/Semantics/RecursiveStorage/Copy.lean` implements storage overlay by induction on present source values.
An absent source slot clears its old destination instead of unfolding the
schema, so implicit defaults cannot cause recursive allocation. Copy preserves
destination mappings, ignores source shadows, clears the shortened destination
live suffix and keeps older shadows. `write` copies a captured source;
`copyAt` captures it before writing, including overlapping paths. The proof
scripts cover copy read-back, default-copy/clear agreement, mapping barriers, source length,
destination extent, shortened live slots and older shadows. They do not claim raw equality
between the copy result and the source.

`Admission.lean` checks a finite node marking against the actual schema. Its
closure condition follows node, dynamic-array and fixed-array edges and rejects
mappings; inline layout rank alone cannot establish mapping freedom.
`CopyPermit.check` returns a typed certificate, and `assign`/`assignAt` require
one. The `step`/`along` proof scripts inherit permits along every typed path;
`no_mapping_path` rules out any reachable mapping endpoint. This accepts guarded mapping-free cycles while rejecting recursive
mapping-containing assignments. It is an admission interface used by these
graph clients; the ordinary JSON importer does not call it yet.

`Solidity/Semantics/RecursiveStorage/Observations.lean` supplies proof scripts for equivalence laws, observation
through appended paths, descent to successfully read subtrees, and equivalence
of implicit versus explicit default mapping slots. Congruence under updates,
deletion and copying still remains open.

The updated reference script was executed only against temporary fixture
copies with the pinned 0.8.38 compiler: **20 EVM vectors and seven rejection
cases passed**, across legacy and via-IR pipelines. New positive vectors cover
populated recursive storage copy, shortened nested contents, retained
destination shadows, ignored source shadows and ordinary scalar subtrees.
New negatives pin error 9214 for direct and nested mapping-containing storage
assignment. The overlapping-path regression is a graph-kernel statement only;
no compiler/Lean correspondence theorem or Solidity overlap claim is made.

No core indexed representation was migrated. Existing match/recursor
optimizations and the current upstream frame/loop APIs remain untouched.
The bridge adds finite-layout recursion and list lookup; functional copy slots
remain lazy and may retain source/destination closures. The primary must
measure the new example and an unchanged struct example before any future
migration, and separately check costs as history and depth grow. No speed or
scaling result is asserted for M2.

Integration must check the four new semantic modules and
`Examples/RecursiveCopy.lean`, inspect the headline `#print axioms`, then run
the library/TestSuite, sort, corpus, layering and trust gates after merging.
Register the example in `site/examples.json` only during primary integration;
the patch worker was explicitly forbidden to change that shared manifest.

## Representation and laws

`Solidity.TypeGraph.Schema n` identifies nodes by `Fin n` and compilation
origin/declaration IDs. Ordered fields have typed positions. Its rank follows
struct and fixed-array edges and stops at mapping/dynamic-array boundaries.
`Schema.no_inline_cycle` rules out every nonempty inline cycle; direct and
fixed recursion cannot receive this certificate. Mapping-freedom must follow
all graph edges instead; this layout rank is not a mapping-freedom decision.

`Value G T` and `Slot G T` are strictly positive, well-founded inductives.
Fields are dependent functions, array slots functions on bounded positions,
and mapping slots functions on the existing bounded primitive key sorts.
There is no erased value/state or untyped fallback. Missing slots generate
the type's default only when read; fields are lazy too. A stored value cannot
contain a pointer cycle, while finite paths may follow a recursive mapping
edge arbitrarily many times. `defaultBelow` uses a proved layout bound;
`clear` recurses on existing value children, never on `sizeOf`.

Arrays distinguish live `Fin (2^256)` length from retained `Fin (2^256+1)`
extent. Logical reads and saves fail beyond extent. Live reads also check the
live length. Fixed indices are word-sized and checked against fixed size.
Deletion clears the former live prefix, preserves old shadows and extent,
and stops at the first mapping, preserving that whole subtree. Empty push
retains reference elements but resets the newly live primitive slot, matching
the existing `pushSlot`; pop clears its former last live slot.

Generic kernel proofs cover typed field/slot writes, read-after-save,
read/append composition, no inline cycle, deletion idempotence, deletion of
defaults, mapping preservation, old-tail preservation, push length/extent
and retained-slot preservation under its explicit primitive/index condition,
and pop length/extent. The headline axiom output uses only standard
`propext`/`Quot.sound`; the inline-cycle theorem has no axioms. No new axiom,
`sorry`, native proof, `unsafe`, `implemented_by`, external dependency or
heartbeat override was added.

`Value.ObsEq` observes failed reads, primitive values, live lengths and
retained extents. M1 only defined it; M2 adds the laws listed above.
Congruence of save, deletion and push/pop is not yet proved. Raw equality distinguishes an absent child
from an explicitly stored default. There is no structural mapping get-put
claim, path-level divergent-path frame law or save-composition theorem.

## M1 validation and review (historical; not M2 validation)

Per-file MCP diagnostics pass for every new Lean module. Kernel examples
cover every depth of a self-mapping default path (including depth 64),
recursive saves, independent leaves, populated recursive tree deletion,
mutual-array reads/writes, mapping-bearing fixed elements, allocated-zero
versus absent reads, live versus retained bounds, dirty reference reuse,
primitive reset on push, old primitive shadows and nested shadow lengths.

Final `./run-lean.sh` passed: 595 library jobs, 243 TestSuite jobs and the
frozen SolKey sort gate (377 taclets, 131 read-bearing annotations, zero
mismatches). Frozen corpus parity passed with 774 obligations. The TestSuite
audit reports 552 derived, 11 refuted and zero pending; the automatic gate
reports 491 automatic and 61 with a step budget. Feature generation is
current. Layering passes with 133 core modules and no elaborator reach.
`git diff --check` passes. The existing 33 Scratch orphans and 13 missing
vendor/external documentation references remain. The global trust inventory
reports 25 existing findings; excluding all eight new graph Lean files gives
the identical findings, and no trust inventory was refreshed.

The independent reference script is:

```
node scripts/check-recursive-types.mjs SOLJSON_FILE NODE_MODULES_DIRECTORY
```

It verifies the exact 0.8.38+commit.1835d247 compiler SHA-256, compiles the
fixture under both legacy and via-IR pipelines, and checks 12 EVM vectors.
Five negative cases reject direct, fixed and mutual-inline recursion,
recursive external ABI arguments, and mapping-bearing memory parameters.
These reference observations and the Lean regressions are separate checks;
there is no compiler/Lean correspondence theorem. In particular, the legal
memory-alias cycle is a reference-only test and is outside this storage API.

The read-only finder found that the initial push reused arbitrary primitive
shadows, unlike the existing model. The implementation now resets that slot;
the frame theorem has an explicit preservation condition, and a kernel
regression distinguishes primitive reset from retained reference reuse.
The skeptic confirmed the primitive correction, bounds and deletion behavior and identified
the unproved observational/whole-pipeline interfaces above. Both reviewers
ran no Lean and made no edits. Their requested populated-tree and mutual
path fixtures were added and checked. The skeptic also corrected an obsolete
sparse-map compatibility claim: functional slots can encode arbitrary legacy
mapping defaults, though that bridge has not been proved.

## Cost and integration boundary

The warning and history review preceded representation edits. Commits
`323951dd`, `3929cbc2` and `01dd890d` explain the encoded-name/table choice;
`d0c13aba` and `2f41a68a` retain recursor/match optimizations motivated by
indexed-match checking cost. This milestone leaves that existing
representation and those optimizations intact. Carrying a graph through
the ordinary signatures will require a broad rebuild and may increase
elaboration cost; this isolated implementation is not evidence otherwise.

Functional slots do not give efficient support enumeration, whole-value
printing or executable equality. Updates/deletes retain closures and lookup
can grow with operation history. Measurements time the complete example module
(0.88 s) and an unchanged existing struct example (11.49 s before, 10.51 s
after). These single observations include ordinary run-to-run variation and
are not a speedup, history-scaling or whole-interpreter performance claim.

Remaining work includes extracting shared type foundations to avoid an
AST/graph import cycle, admitting compiler declaration graphs into the ordinary
pipeline, migrating storage/heap/state/signature/terms and their folds,
completing operation congruence and compatibility laws, and connecting typing,
source notation, printers, rules and soundness. A default allocator can recurse on guarded
layout rank, while copies of present storage children use value induction.
Copying synthesized defaults requires that separate argument. Recursive
memory-to-storage copying must additionally handle legal heap cycles through
an explicit exhaustion/divergence policy; the old decreasing `tyRank` proof
does not justify it. M2 introduces a finite-layout compatibility bridge and mapping-path proof
scripts, including arbitrary legacy mapping defaults. Its general field/index
path and update/copy correspondence theorems remain open. Combined M2 Lean
and repository validation is tracked in integration.md.

Historical M1 validation logs and timing JSON live under
`/tmp/solidity-lean-feature-groups-20261025/recursive-*`; final results are in
`recursive-types.status.json`. M2 was delivered as a patch with original base
bytes and SHA-256 hashes; the primary owns combined integration validation. The full recursive-types group
remains incomplete and its catalog status stays missing.

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
before `Contract.lean`
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
