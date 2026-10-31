# V11 memory operations: independent adapter checkpoint

Lane status: **partial**, never a whole-lane completion certificate.
Base: `fb379ae20f10e2c92113453ddd9d40d8f2efbe09`.
Branch: `codex/solidity-v07-v11-20261030/v11-memory-operations`.
Checkout: `/workspace/v11-memory-operations-pinned`.
The original checkout and its `work` and `bridge-theorems` branches are preserved.

## Concrete gap and published interfaces

The manifest's `rangeAccess` localEvidence includes
`Solidity/Syntax/Elab/SliceCopy.lean`, concrete slice examples and
[calldata-slice-copies.md](../calldata-slice-copies.md). That document explicitly
leaves general slice-lowering equivalence and symbolic copy-loop invariants open.
The actual `sliceElementCopy` implementation retains the named refusal for
reference shapes beyond fixed primitive rows. This lane changes neither the
refusal nor its owner. `calldataLocation` points at the intrinsic AST;
`memoryAliasing` points at storage operations. Neither establishes target
byte-memory transport. The G03 ledger and G04 restrictions remain untouched.

At this exact base, `Heap`, `MVal`, `MObj`, `HRef`, `Heap.Keeps`, and `Heap.set`
are the existing intrinsic interfaces. Published `Theory/Typed/Mem` proves
`MObj.elems_wk`, `Heap.keeps_alloc`, `Heap.get_set_same`, `Heap.get_set_ne`,
and `HRef.id_lt`; the new modules import these checked interfaces read-only.
`Evm/MemoryObjects` and `Evm/MemoryObjectCompile` provide typed word-object
ownership and a narrow certificate compiler, not the required final byte-EVM
source composition. No unmerged branch or unpublished premise is consumed.

## Implemented checkpoint

All names below are under `Solidity.Backend.MemoryOps`.

| Theorem | Exact material premises and result |
|---|---|
| `SliceBounds.index` | Ordered half-open endpoints `start ≤ stop ≤ size`, and `i < stop-start`; concludes `start+i < size`. |
| `SliceBounds.compose`, `sliceElems_compose` | Outer endpoint bounds and inner bounds relative to `stop-start`; compose coordinates exactly. |
| `sliceElems_length`, `sliceElems_read` | Existing typed array/fixed-array reference, endpoint certificate, and for reads an in-slice index; exact runtime length and original element read plus original index bound. |
| `sliceElems_keeps`, `sliceBounds_keeps` | Explicit heap prefix and `Heap.Keeps`; exact map by `MVal.wk` and unchanged endpoint validity. |
| `sliceElems_alloc` | Existing heap/object allocation; discharges `Keeps` with published allocator proof. |
| `local_ref_wk`, `local_unset_wk`, `local_slice_push_wk` | Existing typed local lookup plus prefix; local identity/unset status survive heap growth and context push, with explicit `Keeps` for slice content. |
| `adopt_local_slice` | Actual `State.adopt`, initialized memory local and explicit `Keeps`; local/slice transport and unchanged storage, net, transaction and balance fields. |
| `sliceElems_copyStToM`, `copyStToM_old_ne_fresh` | Published intrinsic `SVal` copy and its existing `mapFree=true` argument; old slices preserved and returned reference distinct from all older identities. |
| `sliceElems_allocDefault`, `allocDefault_old_ne_fresh` | Published `Heap.allocDefault`, same `mapFree` premise; default construction preserves old views and returns a fresh root. |
| `overwriteSlice_space`, `overwriteSlice_keeps`, `withElems_wk` | Prefix, explicit pre-overwrite `Keeps` and original capacity; derive weakened capacity and commute object repackaging/overwrite with growth at every old object. No new-object or re-executed-copy claim. |
| `alias_iff_wk`, `old_ne_fresh` | Existing typed references/prefix or actual allocation; weakening preserves alias equality and no old identity becomes fresh. |
| `replaceSlice_length`, `replaceSlice_inside/before/after` | Destination capacity `dst+payload.length ≤ xs.length`, with respective index tests; exact size, payload reads and exterior framing. |
| `snapshotCopy_read/length` | Actual source and destination interval bounds, interior index for reads; captures original list before overwrite, with no overlap restriction. |
| `checkedSnapshotCopy_none_iff` | No premises; failure exactly when either endpoint exceeds the original list length. |
| `checkedSnapshotCopy_correct` | Both endpoints in bounds; successful result has original length and every captured source element. |
| `overwriteSlice_elems/inside/outside/frame` | Existing intrinsic typed heap array, capacity, corresponding index/identity separation; actual destination/exterior/other-object reads after `Heap.set`. |
| `captureOverwrite_read` | Source endpoint certificate, destination capacity and interior index; actual overwritten heap reads original source even for same-object overlap. |

No new state/value representation, AST, source semantics, target semantics,
axiom, trust shortcut, proof-budget increase or public payload/depth cap is added.
`withElems` only repackages an existing typed array object at unchanged length,
using `ArrTy.casesOn`; no reference constructor or child-allocation queue is
reimplemented. References in snapshots are shallow identities, not fresh deep
copies. The natural-number boundary witnesses are element boundaries; they do
not establish physical 32-byte encoding.

Controls inhabit a fixed parent containing aliases to a nonempty dynamic
Boolean child. They cover empty/nonempty views, reversed/overrun bounds,
shared identity across allocation, distinct fresh identity, an actual changed
reference slot with both child objects framed, both overlap directions, a
streaming-copy negative control, checked source/destination failures, empty
input, and a nonempty 33-element payload in a 65-element source, crossing index 32 with suffix checks.
Headline theorem axiom sets are guarded in each module: subsets of `propext`,
`Quot.sound`, `Classical.choice`; no additional axiom is admitted.
Additional controls instantiate initialized and hidden unset locals, real context
push/State.adopt, a nonempty nested storage-tree copy, nested default
construction, reference overwrite across that actual growth, and a negative
identity-with-changed-content witness refuting `Keeps`. These are intrinsic
storage-tree/memory combinations, not calldata or independent Source semantics.
These are kernel proofs, not bounded external EVM/compiler tests.

## Queue and ownership accounting

Current cumulative accounting through checkpoint thirty-two. Earlier checkpoint
narratives retain their historical observations and gate outcomes.

| Item | Status | Remaining obligation / owner boundary |
|---|---|---|
| G32 | partial | Intrinsic heap-object framing/noninterference components here; typed heap-to-byte representation and final separation transport still need the reserved byte-memory bridge and actual target interfaces. |
| G33 | partial | Old-slice allocation/default-construction extension and fresh-vs-alias identity proved using published constructors; supported actual Source Boolean allocation and MemOK preservation now checked. All-type construction/defaults, exact target allocation failures and stack/frame transport remain; reference constructors stay with reserved owners. |
| G34 | partial | Typed slice coordinate/read/overwrite adapters, identity controls and actual supported Source memory reads and single-element read/write-to-intrinsic-copy transitions proved. General paths/rebinding/delete, stale aliases and nonprimitive source/target compilation remain; existing MemoryCompile/MemoryObjects queues untouched. |
| G35.01 | partial | Published intrinsic multi-object storage copying and recursive Mirrors are consumed; interleaved builder/snapshot mirror frames are proved here. Source/target compiler, physical representation and full liveness composition remain. |
| G35.02 | blocked | Memory-storage-copy owner retains implementation, tail clearing and mapping obligations. |
| G35.03 | partial | Actual decoded Boolean/uint256 table-to-existing-memory transfer, exact runtime guards, ordered reads, frames and growth are proved, including actual ordered two-transfer composition and local commutation. General families/reference construction, calldata-to-storage, ABI decoding, general Source copy/program execution and target transport remain. |
| G35.04 | partial | Actual intrinsic shallow overwrite, original-heap snapshot and overlap/framing laws proved. Target emitter, language alias/deep-copy classification and fresh deep-copy transport remain. |
| G35.05 | partial | Published finite map-free recursive Mirrors are transported through actual multi-generation builder/snapshot operations with typed generation separation. Source/type-graph/cycle/mapping/shadow coverage and emitted traversal/deep-copy realization remain; no fixed cutoff is introduced. |
| G35.06 | blocked | Requires all preceding copies plus V10/source/target composition; no V07–V10 unpublished lane imported. |
| Backfill A | partial | Runtime bounds, same-object intervals, ordered recapture, real allocator extension, Boolean/uint256 decoded transfer and element-boundary controls are proved. General family/physical-byte/target transport remains. |
| Backfill B | partial | Typed nested alias/growth/path and multi-generation recursive intrinsic mirror/identity composition are proved. Fresh-root Source representation, general graph/deep-copy realization and mixed-location Source/target composition remain. |

V04 source semantics, V05/V06 partial prerequisites and serial V06→V11 final
composition remain open at the pinned revision. Other owners' scalar, storage
representation, environment, failure, creation, ABI/function-reference, memory
loops, reference construction, internal-call and Bridge work is neither edited
nor replicated. No source shape or refusal is removed. Proposed G03 feature
reconciliation: attach this limited component evidence to `rangeAccess`,
`memoryAliasing`, `memoryLocation`, `calldataLocation`; do not promote their
whole-feature or parent-group status.

## Runtime and checks

Lean 4.24.0 (`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`),
Lake 5.0.0-src+797c613. `lake build -j1` is unsupported by this Lake; the failed
attempt is retained. A temporary alternate TOML adds Lean `-j1` to every library.
`LEAN_NUM_THREADS=1` is explicit. No Lean MCP tools are exposed in this session.

Systemd probes fail because PID 1 is `tail`. Supported Docker/cgroupfs v2
provides the equivalent enforced process-group cap: observed
`memory.max=12884901888`, `memory.swap.max=0`, with 16 GiB parent limit and OS
headroom. No daemon restart, privileged container, networking bypass or host
resource-policy change is used. Build containers have networking disabled.
Actual `Solidity.KeySort` gate passed (2 jobs; cgroup peak 24,711,168 bytes)
before RUNTIME_GATE_PASS. Initial cache-path and unsupported-flag failures are
retained separately. Builds reuse source/toolchain-keyed disk caches.

Evidence lives at `/workspace/v11-memory-operations-evidence`.
Focused kernel checks through the heap-capture/context/extension/control closure pass; early
failed iterations are retained and never counted as passing gates. The bounded
gate driver records raw commands, exit codes, cgroup peaks and sampled aggregate
Lean/Lake RSS. Final registration/import, structural, docs and full gates are
recorded in the external handoff after execution, with exact outcomes.

## Independent reviews and checkpoint handoff

Separate finder and skeptic reviewed the actual four initial modules without
Lean/server/build use. No mathematical defect found. Both identified the absent
nonempty boundary payload witness and absent registration/documentation. The
witness was added; registration and this document resolve the other finding.
Both explicitly rejected treating these adapters as calldata, byte-EVM,
recursive deep-copy, context extension or lane completion. Second finder/skeptic reviews found no mathematical defect in heap overwrite
or context/extension transport. Confirmed gaps were additional instantiated
local/adopt, storage-copy, overwrite-growth and identity/content negative
controls; these were added and kernel-checked. Boundary wording now precisely
distinguishes a 33-element payload in a 65-element source and crossing index
32, not physical byte transport. New module registrations and axiom guards
are included. The full gate completed with exit 0: default build 858 jobs, SolkeyTestSuite
262 jobs, and frozen sort check (377 taclets, 131 read-bearing annotations).
The container reports OOMKilled=false. Complete retained stdout is recovered
in `v11-final-full-recovery-841fcaed.log`; its final cgroup peak is exactly
12 GiB, under the enforced 12 GiB/no-swap cap. Reconnects interrupted the cold
aggregate RSS collector; no uninterrupted cold RSS maximum is claimed. A
warm confirmation records uninterrupted telemetry without discarding this gap.
No push, merge, PR, scope decision, new exclusion or new premise approval occurs.


The first cold full-gate attempt was intentionally paused at 129 reported jobs
while finishing the additional independent backfill. Exit 137 is a deliberate
stop of this task's own container, not a passing gate or an inherited failure;
Docker OOM status and measured peaks are retained. The checked disk cache is
preserved for the final resumed gate. Full documentation checking fails with
46 historical findings at both exact base and checkpoint; the distinct
no-new-findings check passes. Raw failures are retained, not relabeled green.


Recovery audit `841fcaed-076b-493a-991e-d8eb76efa283` restored access to the same
VM and unchanged staged tree. No second cold build was launched and the surviving
gate was neither stopped nor restarted. The prior recovered log was preserved
with a SHA-256 receipt before a fresh exclusive-output collector recovered all
ordered phases and the actual container exit. Earlier deliberate exit 137,
transport failures, and the goal RPC/context failure remain failures, not passes.
This checkpoint remains partial; committed head and exported patch/bundle hashes
are recorded in the external handoff after commit. The runtime TOML remains
untracked and outside the checkpoint.


Checkpoint gate closure (recovery 841fcaed): the cache-reusing warm full gate also
exited 0, with all ordered phases passed and sampled aggregate Lean/Lake peak
62,624 KiB. This warm measurement does not fill the interrupted cold RSS record.
Layer, orphan, trust, owned-boundary and diff checks pass. Strict automation
passes unchanged at base and checkpoint: 491 automatic plus 61 budgeted replays,
11 refutations, zero manual/pending; all 26 timed TestSuite modules meet the
existing 300-second budget. The complete TestSuite trust/parity audit passes
against the committed snapshot: 564 functions = 552 derived + 11 refuted + one
existing exclusion; two skip. A first invocation against the setup copy failed
because its adjacent pin file was absent; that raw failure is retained. The
committed snapshot and setup manifest have the same SHA-256; no re-pin occurred.
Strict documentation checking still fails with the identical 46 missing-path
findings at exact base and checkpoint; the separate no-new-findings gate passes.

Refreshed independent finder/skeptic source reviews after recovery found no
additional defect. They verified the ordered complete log and required durable
OOM/command evidence and staging the final document; both are included. The
next independent checkpoint will trace actual published calldata objects/read
interfaces and extend transport or disjoint overwrite composition as those
interfaces permit. This checkpoint is not completion of any parent G group,
Backfill queue, or the original persistent goal.

## Decoded-object and disjoint-write checkpoint

This continuation traces the actual `Source/State.lean` interface:
`Source.Calldata.objects : Nat → Option (Σ τ, Source.Data D τ)`, `Data.array`
with finite typed contents, and `Val.cdRef`. `Source/TypingExamples.lean`
explicitly defers slice expressions to S02. There is no published source slice
execution judgment to instantiate here. Raw `Calldata.input` is independent of
its decoded-object table; these theorems do not prove their ABI correspondence.
No Source, byte-memory, decoder or reserved copy implementation is changed.

`CalldataRead` defines a certificate of actual decoded Boolean-array lookup and
finite structural reads of that existing object, not an expression evaluator.
`decodedBoolRead_iff` proves those reads exactly equal `List.getElem?` of the
certified input. `decodedBoolRead_bound` and `decodedBoolRead_overrun` establish
actual decoded-object bounds/impossibility, not a source halt classification.
`decodedBoolSlice_read` applies the existing interval index law.
`decodedBoolSlice_overwrite_read` and `decodedBoolSlice_transport` connect that
read to the actual intrinsic `overwriteSlice` result and a different typed
object's contents. Premises are initial object-table equality, ordered source
endpoints, destination runtime capacity, interior index and (for framing)
different object IDs. There is no assumed preservation result, payload cap or
fixed recursion cutoff. The component is dynamic Boolean arrays only; general
calldata types, decoding, storage targets and source execution remain open.

`overwriteTwo` in `DisjointOverwrite` performs two existing heap overwrites on
already captured payloads. Original capacities and distinct destination IDs
derive second-write capacity. `overwriteTwo_comm` proves actual whole-heap
equality, for arbitrary typed primitive/reference array elements, offsets and
lists. `overwriteTwo_path` transports every published `MPath.mvalT` observation
by that heap equality; it assumes no path-preservation premise. `overwriteTwo_first`
and `overwriteTwo_frame` retain the first destination and every third object.
`overwriteSlice_empty` proves whole-heap identity at every valid endpoint.
These laws concern captured shallow values, not re-executed source reads,
fresh deep copies, source evaluation order or stale-alias compilation.

The concrete controls discharge decoded lookup at offset 7, source slice [1,4),
and destination offset 1; values change and a reference-containing parent is
framed. They reject wrong values, absent/wrong-type lookup, reversed/overrun
endpoints and reads from empty input, exercise an actual empty overwrite at the
end, and transport a nonempty 33-element slice across element index 32. This is
not a byte-word encoding claim. Two different fixed reference parents share
children, both parent slot arrays change, children remain unchanged, an actual
nested typed path reads the redirected false child, and an out-of-bounds path
returns the existing revert. Same-slot alias writes demonstrably fail to commute.

Independent read-only finder and skeptic reviews inspected all four modules,
actual statements, non-vacuity, ownership and controls without builds/server or
writes. Neither found a semantic defect. Both required exact observed axiom
pins and explicit source/ABI/general transport boundaries; these are retained.
Focused closure passes 54 jobs, including all axiom guards, after repairing the
redundant injection/generalization tactics and explicit concrete evaluator/list
reductions. Earlier failed elaboration logs remain failures in the evidence.
Headline axiom sets are only subsets of `propext`, `Quot.sound` and
`Classical.choice`; no `sorryAx` remains in the passing closure.

Queue accounting remains partial: G32 heap/frame/identity adapters exist but
heap-to-byte and full compiler certificates remain open. G33 published default
extension adapters exist but all-type/default/target failures and reserved
reference construction remain open. G34 overwrite/path observation components
exist but general path/rebinding/delete/stale-alias compilation remains open.
G35.01 has published intrinsic storage-tree transport only; G35.02 retains the
reserved memory-to-storage prerequisite. G35.03 now has actual decoded Boolean
object-to-memory transport, not general immutable calldata/source/storage/ABI
transport. G35.04 adds disjoint captured shallow-copy composition to snapshot
laws, with fresh deep-copy compilation open. G35.05 has arbitrary existing typed
path observation transport, not recursive child-content traversal; the published
legacy layout and graph interfaces supply no completed graph-to-memory bridge.
G35.06 remains blocked on reserved copy/representation/liveness results and the
V10/source/target chain. Backfill A gains actual decoded reads, empty identity
and disjoint overwrite composition; Backfill B gains shared-child and nested
path observations, not full traversal. No parent, queue or goal is complete.

Checkpoint-two final gates: `run-lean.sh` exits 0 in the bounded serial container,
862 default jobs, 262 TestSuite jobs, and SolKey 377/131 annotations OK; OOMKilled
is false. Sampled aggregate Lean/Lake RSS peaks at 1,515,016 KiB and cgroup peak
is 954,744,832 bytes (different measurement domains). The container memory limit
is 12 GiB and swap allowance zero. Strict automation, complete committed-snapshot
TestSuite parity/trust, layers, orphans, trust, owned-boundary/script and diff
checks pass. Global strict docs still exits 1 with exactly the same raw output
at frozen base and current tree; the separate no-new-doc-findings comparison
passes. The global axiom inventory exits 1 at both base and current: zero unsafe
pin errors, respectively 14 and 67 unrecorded changes. The 53 additional pins
are owned MemoryOps pins from both checkpoints, not changes to the 14 inherited
pins. The reserved inventory is untouched; exact proposed pin additions are
exported for coordinator reconciliation. The lane checker independently parses
all owned pins using the published parser and rejects nonstandard axioms.
A sandbox-only Docker socket observation was denied; the supported escalated
read-only observation recovered actual exit 0/OOMKilled=false and the same cap.

Checkpoint-two handoff: the committed parent is
`899789503b0cb283935e9f151bdb1a6df9c50f01`; exact resulting head is recorded after
commit in `/workspace/v11-memory-operations-evidence/checkpoint2/handoff.json`.
Cumulative original patch, incremental bundle, handoff and checksum manifest
are exported in that absolute directory; raw gates and proposed pin additions
remain in its parent evidence directory. Runtime TOML stays untracked. Refreshed
finder found no further issue; skeptic corrected a module-qualified name in this
document to the actual `overwriteTwo` namespace before closure. No integration,
publish or persistent-goal completion is authorized by this checkpoint.

## Allocator and disjoint-write growth checkpoint

`overwriteTwo_keeps` transports both actual captured writes through an initial
published `Heap.Keeps`. It derives the first/intermediate preserving relation
and both grown capacities. `overwriteTwo_alloc` discharges initial preservation
with `Heap.keeps_alloc`. `overwriteTwo_alloc_frame` additionally proves the newly
allocated object's own contents unchanged, using actual fresh-versus-old IDs.
Payloads are typed over the original heap; they cannot reference fresh objects.
The result is old-object naturality plus fresh structural framing, not equality
with allocation after writes, recursive liveness or a deep-copy compiler.

The inhabited control allocates a fixed reference parent with child identities
[0,1], then genuinely changes both nonempty Boolean child arrays. It applies the
allocator transport and fresh-frame theorems and proves exact old contents.
`child_content_negative` refutes the claim that the framed parent's child
contents remain unchanged. This distinction matters for nested aliases.
Separate independent read-only finder and skeptic reviews found no semantic,
ownership or vacuity defect; neither ran Lean/server/builds or wrote files.
Skeptic required the original-heap payload limitation, retained above. Focused
closure passes 47 jobs; all seven new headline/control axiom sets are
`[propext, Quot.sound]` and are guarded. Prior failed proof attempts are retained.
This advances G32/G33 and Backfill B operation-side extension only; all prior
queue statuses and missing source/target/byte/deep-traversal premises remain.

Checkpoint-three handoff will be exported under
`/workspace/v11-memory-operations-evidence/checkpoint3` with exact head/base,
cumulative patch, named-ref bundle, gate logs and checksum manifest. Parent head
is `ba337ab29d9f55a768e11a446f10f2f074526b24`. Checkpoint-two finder and skeptic
artifact reviews both passed exact patch/bundle/checksum/link and identity
checks; their original artifacts and manifest are preserved.

Checkpoint-three final confirmation exits 0: 864 default jobs, 262 TestSuite
jobs and final SolKey 377/131 OK. Sampled aggregate Lean/Lake peak is
1,566,388 KiB; cgroup peak is 380,190,720 bytes. Strict automation and committed
snapshot TestSuite parity/trust pass, as do layers/orphans/trust/lane/script/diff.
Global docs still fail with byte-identical exact-base output; no-new passes.
Global pin inventory still fails: zero errors and 74 unrecorded changes, comprising
14 inherited plus 60 owned pins. The owned checker passes all 60 standard pins
and 13 module boundaries. Final finder and skeptic reviews found no further
source/document defect; runtime TOML remains outside the commit. These passing
checkpoint checks do not close G32-G35, reserved prerequisites or the goal.

## Published word-object frame checkpoint

`ObjectFrames` imports the pinned `Evm/MemoryObjectFrame` read-only. That module
proves single-element write frames. The new adapter proves
`overwriteSlice_cells` for this lane's arbitrary captured range overwrite,
using the unchanged runtime length and different-object frame laws.
`overwriteSlice_ownership` transports the existing positive, disjoint object
reservations and frame; `overwriteSlice_base_identity` derives address/identity
equivalence from the published positive-reservation injectivity theorem.
`overwriteSlice_other_repr` retains an actual different array's published
`ArrayRepr` in the unchanged machine, including reference-valued elements.
Premises are actual initial ownership/representation, runtime range capacity,
and identity separation for other-object content framing. No preservation
result is assumed, and no primitive-only payload restriction is added.
This is a word-object adapter, not the missing byte-memory bridge.

The nontrivial witness simultaneously inhabits separated ownership and actual
initial word representations of a nonempty Boolean child and a fixed parent
with two aliases to it. The child changes true to false; parent pointer words
retain their representation. `stale_target_negative` proves the old machine
cannot represent the changed destination, so ownership transport cannot be
mistaken for target execution correctness. `colliding_base_negative` rejects
coincident addresses. The stack conjunct observes the same unchanged machine;
it is not an emitted-operation stack-tail preservation proof. Both independent
read-only reviews found no defect and required this distinction in the handoff.
Focused closure passes 88 jobs; all eleven new axiom outputs are guarded and
contain only the standard allowlist. Reserved single-write code, byte-memory,
copy-loop and reference-construction modules are unchanged.

### Historical published-interface blockers at the original frozen base

The exact pinned `Evm/MemoryObjects.lean` relations use `Machine.mem : Nat → Word`,
one word per element and dynamic headers. `MemoryObjectCompile.StmtFrag` and
construction certificates prove only their published fragments. Neither gives
this lane a range-copy byte emitter/bridge. G04 R31 records the missing
byte-addressed memory; R25 records the still-explicit allocator-capacity premise
and missing generated panic check. `AllocationInput` and `GrowsAllocator` in `Evm/MemoryObjectAllocator.lean` retain those capacity hypotheses. This lane cannot erase
them or count operation-side naturality as exact allocation-failure compilation.

`Source/State.lean` publishes immutable decoded tables and typed array fields,
but `Source/TypingExamples.lean` at that original revision deferred source slice execution to S02.
The Boolean structural observation here is not that missing judgment. Thus
calldata ABI/source/revert/storage transport remains open. Existing
`Semantics/RecursiveStorage/Legacy.lean` explicitly realizes finite layouts and
never unfolds graph cycles; it supplies no generic recursive memory-child copy
or liveness relation to instantiate. Existing intrinsic heap aliases can share
children; the negative controls show why unconditional deep preservation is
false. No depth cutoff or alternate semantics can fill that missing interface.
Reserved memory-to-storage/loops/reference constructors and final V10/source/
target prerequisites remain with their owners. All prerequisite source modules
were read at frozen revision `fb379ae20f10e2c92113453ddd9d40d8f2efbe09`; none
was imported from another worker's branch or edited here.

Backfill A now has generic typed captured slice/snapshot bounds, overlap,
empty/nonempty element-boundary controls, allocator noninterference and actual
decoded Boolean-object transport. Backfill B has context/heap extension,
nested coordinate/path observations, disjoint overwrite/growth composition,
fresh-versus-alias identity and published word-object frame transport. Their remaining general calldata/recursive-child obligations remain open; full
byte/Source/target composition additionally depends on the prerequisites above.
An unavailable Source evaluator does not establish that every independent
decoded-object or traversal backfill is unavailable. G32/G33/G34/G35.01/.03/.04/
.05 and both Backfill queues remain partial; G35.02 and G35.06 remain blocked.
A full lane cannot close without those published owner results and final chain.

Checkpoint-four handoff path is
`/workspace/v11-memory-operations-evidence/checkpoint4`; cumulative original
patch, named-ref bundle, handoff, raw gates, proposed pin inventory and checksums
record exact head/base. Parent is `7bfc56b0e7bb7bdf2fde0ef1150dae3c8a2d2564`.
Checkpoint-three independent finder/skeptic artifact reviews both passed exact
identity, cumulative patch/bundle, all 33 checksums, links and premise/status
checks. Earlier artifacts, caches, failures and runtime TOML remain preserved.

Checkpoint-four final audits: full gate exits 0 (866 default and 262 TestSuite
jobs, final SolKey377/131 OK), sampled aggregate Lean/Lake peak1,561,596 KiB,
cgroup peak380,588,032 bytes. Strict automatic/TestSuite/layer/orphan/trust/lane/
script/diff checks pass. Strict docs fails with exactly identical raw frozen-base
output; separate no-new passes. Global pin inventory fails with zero errors,
85 unrecorded changes:14 inherited and71 owned. Reserved inventory is untouched.
Final finder found no defect. Skeptic required the open-versus-unavailable
backfill distinction above; corrected before commit. Further independent generic
decoded-object laws remain candidate work, not ruled out by a missing evaluator.

## Generic decoded-array and nonprimitive transport checkpoint

`CalldataArrayRead` uses the same published `Source.Data.array` and immutable
table for every existing element `Source.STy`, both static and dynamic length
options. `decodedArrayRead_iff` derives exact finite structural observations by
constructor injectivity, with no axioms. `decodedArrayRead_overrun` rejects an
index beyond the certified actual length. `decodedArraySlice_length/read/compose`
connect runtime endpoint bounds, captured existing Source.Data values and nested
view coordinates. No array-type restriction, payload cap or depth cutoff is
introduced. This is not child execution, Source expression evaluation or ABI
correspondence. The earlier Boolean observation is definitionally equivalent
to this generic observation (`bool_observation_compatibility`, no axioms).

Static nonprimitive controls contain actual `Source.Val.cdRef` offsets37/42,
including shared37 identities, reject a different38 offset and exact-end read,
and exercise empty end/source plus nested array constructors. Offsets alone
are syntactic identities, not validated child lookup/liveness. Both reviewers
required replacing the word "stale" with "different" for the negative; fixed.
Those controls do not establish stale-alias execution/compilation.

`decodedArray_overwrite_read/transport` connects generic immutable decoded reads
to this lane's actual typed heap overwrite. Premises: exact initial decoded
table/array, an already existing typed value list of the same runtime length,
an initial per-element relation from Source.Data to MVal, ordered source bounds,
destination capacity and (for framing) distinct IDs. Every resulting interior
read and other-object frame is derived. No converter, generic payload emitter,
loop, alternative value/state or desired preservation premise is introduced.
The generic conclusion retains the same supplied `rel`, which may close over
the initial heap; it does not generically establish a heap-indexed relation at
the output heap. The concrete controls prove that stronger final relation only
for their separately framed children. Initial correspondence and existing
payload/conversion remain prerequisites for types without concrete certificates;
parameterization is not all-type proof completion.

The concrete nonprimitive application discharges every premise: actual parent
source entries at7 refer to children42/37, those child tables contain the same
Boolean contents as typed heap children1/0, and the initial relation records
both offset/identity and child contents. The actual fixed-parent overwrite
redirects its reference IDs from[0,0] to[1,0]. Both children are framed, so final
source child table contents and final memory contents still match. A different
source offset and an absent child table fail the initial relation in explicit
negative controls. This is genuine decoded-reference-to-existing-memory slice
transport, not a fresh deep copy or decoder. Initial relations for all approved
recursive/aggregate types and storage destinations remain unproved.

Focused generic read/control closures pass32/53 jobs and actual reference
transport54 jobs, with all19new headline/control axiom sets guarded after final
confirmation. Independent finder/skeptic reviews inspect all four modules and
preserve the initial-relation versus full-source/target distinction. All prior
G32-G35 and Backfill statuses remain partial/blocked; this advances G35.03 and
Backfill A/B without declaring remaining independent work unavailable.

Checkpoint-five handoff is exported at
`/workspace/v11-memory-operations-evidence/checkpoint5`, with cumulative patch,
named-ref bundle, exact head/base, raw gates, proposed pins and checksums.
Parent is `a6953e6b1aaee5d10ee27b975e982db8f82b03a4`. Checkpoint-four artifact
finder and skeptic both passed all33checksums, exactbase/head/branch, patch,
bundle, handoff links and honest open-work statuses. Runtime TOML and all prior
artifacts/caches/failure receipts remain preserved; no integration is performed.

Checkpoint-five final confirmation exits0:870 default jobs,262 TestSuite jobs,
SolKey377/131 OK; aggregate sampled RSS1,561,324 KiB, cgroup peak381,456,384 bytes.
Strict automatic and complete committed-snapshot TestSuite trust/parity pass;
layers/orphans/trust/lane/script/diff pass. Docs global still fails with raw
byte-identical exact-base output; separate no-new passes. Global pin inventory
fails with zero errors and104 unrecorded changes:14 inherited plus90owned.
All90owned pins pass the standard allowlist. Final independent finder/skeptic
reviews found no further defect after precise relation-boundary wording. No
all-type correspondence, recursive-child traversal or lane completion follows.

## Checked actual-heap snapshot checkpoint

`checkedCaptureOverwrite` checks runtime source ordering/length and destination
capacity before the existing `captureOverwrite`. It returns `Option (Heap H)`;
None is this adapter's result, not a newly defined Source/target halt semantics.
`checkedCaptureOverwrite_none_iff` proves rejection exactly for reversed source
bounds, source-end overrun or destination overrun. `some_iff` identifies every
successful heap with the actual captured operation. `read` observes the original
source even for overlaps; `frame` preserves every different typed object;
`empty` proves actual whole-heap identity at valid endpoints.

`captureOverwrite_keeps` derives source capture and destination overwrite
naturality together under an initial preserving extension. The checked version
`checkedCaptureOverwrite_keeps` derives a grown successful result and output
Keeps; `checkedCaptureOverwrite_none_keeps` preserves exact rejection. Both
grown capacities and source bounds are derived. They do not assume the desired
output preservation. Payloads retain existing typed values/references and no
fresh deep copy is claimed. There is no new loop, code emitter, heap semantics,
public payload cap or recursive-depth bound.

Controls use an actual fixed parent with shared typed child references. Right
and left same-object overlaps yield identities[0,0,1,0] and[1,0,0,0]; the right
case refutes a streaming result[0,0,0,0]. Both child objects remain unchanged.
Reversed/source/destination failures and empty exact-end identity are observed
on that same heap. Actual allocation supplies initial Keeps; successful copy
transports old output objects and frames the fresh reference-containing object,
while the same invalid copy still fails. A 33-element nonempty same-object
Boolean overlap crosses element index32 and reads the expected captured true.
This is not physical byte-word memory or target capacity-failure compilation.

Focused closure passes47jobs;21new headline/control axiom sets are guarded after
final confirmation. Independent finder/skeptic reviews inspect actual statements,
non-vacuity, controls and scope. This advances Backfill A and G34/G35.04 operation
adapters; all original parent/Backfill statuses remain partial or blocked.
Source/target bounds failures, emitted copy loops, recursive child traversal,
all-type correspondence/constructors and final chain remain unclosed.

Checkpoint-six handoff directory is
`/workspace/v11-memory-operations-evidence/checkpoint6`; exact resulting head/base,
cumulative patch, named-ref bundle, raw logs, proposed pins and checksum manifest
are exported after commit. Parent is `887c818f3624c4757cc62c611b94d816b23ff5cd`.
Checkpoint-five independent artifact reviews both passed all33checksums, base/
head/branch/patch/bundle/links and honest premise/queue/failure boundaries.
Runtime TOML and every older source/artifact/cache/failure receipt are preserved.

Checkpoint-six review repairs: finder identified that the original source-failure
control also overran destination, so it would not discriminate a missing source
guard. Replaced by source[3,5) into offset0 of length4, with valid ordering and
destination capacity proved separately. Skeptic requested a real zero-length
dynamic heap object: new control succeeds unchanged at(0,0,0), rejects source
endpoint(1,1) despite an empty payload, and rejects destination offset1 despite
valid source(0,0). These fixes strengthen controls without changing any theorem
statement, operation guard or approved profile. Initial full confirmation passed
before these control refinements; final gate is rerun on the refined tree.

Checkpoint-six refined final gates: `run-lean.sh` exits0,872 default jobs,
262 TestSuite jobs, final SolKey377/131 OK. Aggregate sampled Lean/Lake peak
1,612,440 KiB; cgroup peak380,317,696 bytes. Strict automatic, committed-snapshot
complete TestSuite trust/parity, layers/orphans/trust/lane/script/diff all pass.
Global docs still fails with byte-identical frozen-base raw output; separate
no-new passes. Global pin inventory still fails:0errors,125unrecorded changes,
14inherited plus111owned. Owned allowlist/boundary check passes111pins21modules;
reserved inventory is not edited. Final independent finder/skeptic reviews
confirmed both control fixes and found no remaining source/document defect.

Coordinator reconciliation proposals are additive evidence only for exact
feature IDs `memoryLocation`, `newMemory`, `memoryAliasing`, `rangeAccess` and
`calldataLocation`, mapped respectively to G32/G33/G34/G35 operation adapters.
No global feature status, G03 ledger, manifest, TrustAudit or pin inventory was
rewritten. The handoff lists all111owned pins for proposed registration, not a
global inventory pass. All original Work G32,G33,G34,G35.01-.06 and Backfill A/B
remain individually accounted above and unfinished at lane level.

The available tool catalog still has no `get_goal` or per-file Lean diagnostic
RPC; only a goal-stop tool is advertised. The prior trusted-context limitation
is preserved, no new/reset/reactivated goal is created, and no completion is
reported. Full assignment remains partial. Published byte-memory/source/type/
traversal/owner-copy/V10 prerequisites are required for full closure; this does
not assert every future independent refinement is unavailable.

## Output-heap decoded child correspondence checkpoint

The reproduced gap is precise: `decodedArray_overwrite_read` returns the same
supplied initial `rel`; `TransportControls.reference_contents` had a stronger
output-heap child relation only for private two-element constants. Neither old
theorem is renamed or weakened. New owned modules prove actual output relations.

`BoolChildRepr` relates an existing `Source.Val.cdRef` to a typed Boolean-array
`HRef`, its pointer address and the immutable table's actual decoded contents.
Its `overwrite` theorem derives that relation at the output heap using the real
`overwriteSlice_frame`. An arbitrary destination type requires explicit distinct
child/destination IDs; this is a local framing premise, not a source admission
exclusion. `read_iff` observes the actual heap in its certificate through the
published decoded Boolean reads. `alias` gives equal memory-ID implies equal
source pointer; `alias_iff` proves the reverse only with initial address
injectivity on live represented Boolean children. No global injectivity is
silently assumed, and a colliding-address negative demonstrates its necessity.

`decodedBoolChildren_overwrite` handles arbitrary runtime reference lists and
source slices, including shared/repeated children. It concludes actual source
read, actual destination slot and `BoolChildRepr` at the output heap for every
interior element. Initial decoded array, list-length/element correspondence,
ordered endpoints and destination capacity are explicit. Specialized destination
and child types force ID separation: `boolChild_parent_ne` derives it from
`ArrTy` and `HRef.heq_of_id`. Callers supply no redundant separation premise.
`referenceSlice_empty` proves whole-heap identity for empty/exact-end captures.
There is no arbitrary payload cap; the family witness's `<2^256` is exactly the
existing dynamic `MObj` constructor invariant, not a new admission limit.

`RefChildRepr` additionally represents a reference-containing child's actual
immutable decoded table and every referenced Boolean leaf. `overwrite` frames
both the root and its observed leaf footprint with explicit local separation.
`decodedRefChildren_overwrite` derives both footprint separations from its
specialized finite intrinsic types and gives the nested output relation for
arbitrary runtime lists/slices. No pairwise child or leaf separation is needed.
`index`, `index_bool` and `index_bounds` compose the existing `Heap.index` and
finite decoded-array observations, including exact-end failure. They do not
replace an interpreter, invent Source halts or assume path preservation.

`BoolChildRepr.grow` and `RefChildRepr.grow` transport actual old root/leaf
correspondence using initial `Heap.Keeps`. `decodedChildRefs_wk` proves the finite
Source array retains pointer offsets under typed `HRef.wk`. The helper uses
existing `Source.Data.array` extensionality, not a new value/state layer.
Actual allocator witnesses discharge initial Keeps and distinguish old children
from fresh same-type objects. No source representation of a fresh root, nor
injectivity over a newly extended address set, follows from these theorems.

### Inhabited controls and review fixes

The arbitrary-length family discharges every initial child certificate and
capacity. Its nonempty sample changes parent IDs[0,0,0] to[1,0,1], keeps repeated
shared identities and proves alias equivalence under an independently proved
address assignment. Empty source and exact-end operations are actual identities.
Missing/wrong child offsets and wrong contents fail separately; perturbed child
tables retain root7 (and the missing-table control retains the other child37).
A colliding address can represent two different equal-content heap children,
so source pointer equality alone cannot imply equal memory IDs.

`aliased_destination_negative` writes the represented Boolean child itself:
initial contents match the immutable table, the actual write changes them, and
output correspondence is false. This is the named unresolved general-frame case
`alias-child-destination`. It is not a possible same-ID case of the differently
typed specialized parent slices, nor an exclusion from the source profile.

The nested witness changes parent IDs[2,2] to[3,2], selecting an actual child with
repeated leaf IDs[1,1]. Both final typed memory-index reads succeed and the
immutable decoded leaf is false; the equivalence is non-vacuous. Exact-end typed
index/table observations fail. Actual allocation preserves these old nested
correspondences and proves fresh identity separately.

Independent read-only finder/skeptic reviews found redundant specialized
separation premises, which were removed and derived from typing. They required
injectivity-qualified reverse identity, isolated child failures and the
fresh-root/growth limits, all retained above. Neither reviewer ran Lean/server/
builds or wrote files. Focused final closure passes59jobs;35new headline/control
axiom sets are guarded after final confirmation. All earlier failing proof logs
remain retained failures, including dependent-array congruence attempts.

### Remaining clauses and queue accounting

This advances G35.03/.05 and Backfill B with genuine final-heap correspondence.
It does not complete arbitrary recursive correspondence: `RefChildRepr` is the
explicit array-of-Boolean-array component, not a depth admission cutoff. Missing
clauses include arbitrary nested element/struct fields, mapping treatment,
source-to-intrinsic type/layout correspondence, graph sharing/cycles and copy
liveness. The published `Semantics/RecursiveStorage/Legacy.lean` realizes finite
layouts and does not unfold graph cycles; no full Source/TypeGraph-to-memory
recursive child-copy certificate is supplied here. These exact clauses remain
open, without claiming all further independent refinements unavailable.
G32 byte-memory, G33 generated allocation/size failures and all-type default
construction, G34 general compilation, reserved G35.01/.02 copy prerequisites,
G35.04 fresh deep-copy compilation and G35.06 Source/V10/target composition remain
as before. All original Work and Backfill statuses stay partial or blocked.
No source-profile, refusal, exclusion, global ledger or reserved file is changed.

Checkpoint-seven handoff is exported at
`/workspace/v11-memory-operations-evidence/checkpoint7` with cumulative original
patch, named-ref bundle, exact head/base, logs, proposed pins and checksum manifest.
Parent is `99512648c9d4d39157b5ba5141d7adf784b65e97`. Previous sealed exports and
runtime TOML are preserved; no goal reset, completion or integration is performed.

Checkpoint-seven final gates on the refined code tree: `run-lean.sh` exits0,
877 default jobs,262 TestSuite jobs and final SolKey377/131 OK. Aggregate sampled
Lean/Lake peak is1,448,544 KiB; cgroup peak388,222,976 bytes (distinct accounting
measurements). Containment is12GiB/no-swap, serial Lean-j1/LEAN_NUM_THREADS1.
Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b and
Lake5.0.0-src+797c613 execute; fresh KeySort gate passes2jobs. Strict automation,
complete committed-snapshot TestSuite trust/parity, layers/orphans/trust/owned
boundary+standard-pin/script/diff checks pass. Owned checker covers146pins26modules.
Global docs still exits1 with raw byte-identical frozen-base output (46findings);
separate no-new passes. Global inventory still exits1:0unsafeerrors,160unrecorded
changes=14inherited+146owned. Reserved inventory remains untouched; exact proposed
owned pin additions are exported for coordinator reconciliation. Both final
independent source reviews found no further defect after the fixes above.

No `get_goal` or Lean diagnostic RPC is exposed in the actual tool catalog.
No goal is created/reset/reactivated/completed; serial focused closures were used
in place of unavailable per-file diagnostics. Full assignment remains partial,
including every original G32-G35.01-.06 and Backfill A/B obligation recorded above.
No push/merge/PR or unpublished owner result is used. The only intentionally
untracked runtime file is `lakefile.v11-runtime.toml`, excluded from the commit.

## Same-object intervals and ordered recapture checkpoint

The reproduced gap is in actual owned source: `overwriteTwo_comm` requires
distinct object IDs and captures both payloads before either write; previous
snapshot/checked theorems concern one operation. They do not establish
same-object separated-interval commutation or second-source recapture.
No old theorem or premise is weakened to fill that gap.

| New theorem | Material premises and exact result |
|---|---|
| `replaceSlice_comm` | Both captured payloads fit the original list; `IntervalsApart` admits empty intervals anywhere and touching ordered endpoints. Two replacements commute. Arbitrary element type and runtime lengths; no payload cap. |
| `overwriteSlice_len`, `overwriteSlice_all_len` | Actual write capacity. Every existing typed array length is unchanged, including same-ID views, so subsequent capacities are derived. |
| `overwriteIntervals_comm` | Existing typed array, two captured payloads with original capacities and local interval separation. Actual dependent heaps are equal; all other objects are framed. Primitive and reference elements are equally supported. |
| `overwriteIntervals_path` | Same premises; whole-heap equality transports every existing `MPath.mvalT` observation, including failures. |
| `captureTwice_read_cases`, `captureTwice_inside` | Both source intervals and destination capacities hold in the original array. Second capture actually reads the first output. The formula distinguishes both destinations and whether the second source reads inside/outside the first destination. No separation required for these observations. |
| `captureOverwrite_source_other` | First destination ID differs from the subsequent source object; that source's actual slice is unchanged, even with a different element type. |
| `captureOverwrite_source_apart` | Same-object first destination and second source intervals are apart. The second source capture is unchanged. This fact is derived from actual per-index frame/read laws. |
| `captureTwice_frozen` | Source noninterference above suffices to freeze the second input from the original heap. This is not claimed necessary for every value instance. |
| `captureTwice_comm` | Both cross destination/source interval noninterference facts plus destination separation suffice for true sequential snapshot commutation. Destination separation alone is not sufficient generally. These are sufficient conditions, not an iff. |
| `checkedCaptureSequence_some_iff`, `captureTwice_checked` | Option composition exposes actual first intermediate and second output; valid same-array bounds yield precisely the ordered heap. |
| `checkedCaptureSequence_none_iff` | No premises. Failure is exactly either stage's reversed/source-overrun/destination-overrun condition, in original runtime lengths. Successful first writes preserve all lengths; payload contents may still change. |
| `overwriteIntervals_keeps`, `captureTwice_keeps`, `checkedCaptureSequence_keeps` | Initial published `Heap.Keeps`; first-output preservation is derived and used for the actual second operation. All grown bounds/capacities are derived. |
| `checkedCaptureSequence_none_keeps` | Initial `Keeps`; exact failure observations transport through growth. |
| `BoolChildRepr.overwriteIntervals`, `RefChildRepr.overwriteIntervals` | Initial actual child/root/leaf representation and distinct destination footprint; both output relations follow from actual frames. The first root frame derives the second leaf footprint. No output relation or new Source entries are assumed. |

`IntervalsApart` is a local theorem case, not a source admission restriction.
Overlapping/aliased writes and captures remain defined and checked normally.
Neither `captureTwice` nor `checkedCaptureSequence` defines a new interpreter:
they compose the existing intrinsic operations. Option failure is not a Source
or target halt/rollback observation, and no memory loop or payload emitter is
implemented. Reference payloads retain identities; fresh deep copies remain open.

### Discriminating concrete observations

Dynamic heap input[true,false,false,true,false,false] first copies[0,2) to2,
then captures the actual updated[2,4) into4. It yields
[true,false,true,false,true,false], whereas freezing both original inputs or
reversing operations yields[true,false,true,false,false,true]. The destination
intervals touch and are disjoint; their source dependency is the difference.
Mixed-source controls exercise all four ordered-read branches: outside both,
retained first-only destination, and second capture outside/inside first output.

Fixed nonprimitive writes change parent IDs[0,1,0,1] to[1,1,0,0], commute on the
same object and preserve both child contents. Touching nonempty, empty-inside-
another-range and exact-end empty cases are inhabited. Overlapping captured
writes with different payloads demonstrably fail to commute; this is a supported
operation case. Right-overlap then left-overlap reference copies yield[0,1,0,0]
and preserve children, with actual checked success. A positive mutually
noninterfering pair inhabits sequential commutation. Existing typed path order
and actual parent/Boolean child `Heap.index` reads are exercised.

All six first/second reversed/source-only/destination-only failures have actual
Option-none results while the other guards are valid. A second-failure witness
also records the successful first intermediate heap. Zero-length dynamic objects
support two empty copies and reject invalid empty source endpoints independently
at either stage. Actual allocation discharges the sequential-growth premise.

The child integration reuses the already proved `ChildControls.changed_shared`
certificate. Its existential statement explicitly records capacities, payload,
and output equality to the actual `overwriteIntervals` operation, together with
initial/final child correspondence and parent change[1,0,1] to[0,0,0]. No immutable
calldata entry or injectivity assumption is manufactured for this witness.

### Reviews and original obligations

Separate independent read-only finder/skeptic reviews found two issues: comments
incorrectly suggested sufficient interval hypotheses were necessary; fixed.
The child integration initially constructed the operation only in its proof;
the statement now records exact operation equality and capacities. All read
branches and extra dynamic/empty/overlap controls were strengthened. Neither
reviewer used Lean/server/builds or writes. Focused final closure passes65jobs;
40new headline/control axiom sets are guarded after final confirmation. Earlier
proof failures and deprecation diagnostics remain retained in separate logs.

This advances original G35.04 and Backfill A/B; all original G32/G33/G34 and
G35.01-.06 statuses remain partial or blocked. Fresh-root source representation,
reverse address injectivity on added objects, arbitrary recursive child/copy
liveness, generated allocation failures, physical byte memory and final
Source/V10/target composition remain open as previously recorded. Source
semantics, reserved loops/copies/constructors and global inventories are untouched.
No exclusion or admitted shape is removed, and no proof/test/fuel budget changes.

Checkpoint-eight cumulative export directory:
`/workspace/v11-memory-operations-evidence/checkpoint8`. Exact head/base, original
patch, named-ref bundle, handoff, raw gates, proposed pins and checksums are
recorded after commit. Parent is `f205bba434611085faba4da3fb99ae123a51b582`.
Every prior sealed artifact/cache/error and the untracked runtime TOML is preserved.
The existing blocked goal remains unchanged and unfinished; no integration occurs.

Checkpoint-eight final refined-tree confirmation exits0:882 default jobs,
262 TestSuite jobs, final SolKey377/131 OK. Sampled aggregate Lean/Lake RSS peak
is1,575,252 KiB; cgroup peak386,568,192 bytes, with12GiB/no-swap containment and
serial-j1/LEAN_NUM_THREADS1. Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b,
Lake5.0.0-src+797c613 execute and fresh KeySort passes2jobs. Strict automation,
committed-snapshot complete TestSuite trust/parity, layers/orphans/trust/owned
boundary+standard-pin/script/diff checks pass. Owned checker covers186pins31modules.
Global docs still exits1 with raw byte-identical frozen-base output,46findings;
separate no-new passes. Global pin inventory still exits1:0unsafeerrors,
200unrecorded=14inherited+186owned. Earlier160unrecorded checkpoint-seven output
remains sealed, not rewritten. Exact additive pin proposals are exported; no
reserved inventory/ledger is edited. Both final source reviews found no further
confirmed defect after the sufficiency and operation-witness fixes.

Available tools still expose neither `get_goal` nor per-file Lean diagnostic RPC;
no goal is created/reset/reactivated/completed. Existing writer lock, original
checkout, pinned branch/base, disk caches, prior failed commands and sealed
exports are preserved. Runtime TOML remains outside the commit. This checkpoint
does not complete any parent G group, either original Backfill queue, or the
original full assignment; remaining independent refinements are not declared
unavailable by the missing source/byte/compiler prerequisites.


## Checkpoint nine: actual interstage allocation and recapture

Parent: `9f340a4396edd6b3ed2388edaded2d3525dd64a3`; frozen base remains
`fb379ae20f10e2c92113453ddd9d40d8f2efbe09`. Existing sequential transport grew
before both captures. It did not allocate on the actual first output. The six
new `Backend/MemoryOps/Interstage*.lean` modules close that operation-side clause
without changing any intrinsic representation or reserved source.

`checked_interstage_success` starts with an actual checked first result `mid`,
a prefix extension with `Heap.Keeps mid mid'`, and bounds measured in `mid`.
It derives the second actual result on weakened old references and its typed
reads. `checked_interstage_read_cases` distinguishes first-destination interior
reads from original destination reads outside it; the first source may differ.
`checked_interstage_none_iff` records exact second-stage Option failures.
`captureAfterAlloc` applies published `Heap.alloc` to `mid`; its checked, keeps,
fresh and fresh-index theorems discharge growth and frame the supplied object's
own structural fields through a second old-object write. No object constructor,
default builder, Source allocator failure, rollback or target execution is proved.

Dynamic Boolean controls recapture changed data, discriminate a frozen-original
snapshot, exercise independent second source/destination/reversed failures, empty
exact-end operations, and a zero-length first/second chain. A supplied actual
mid-object retains its changed data. Fixed reference-array controls exercise both
overlap directions, repeated parent identities, exact fresh IDs/fields, typed
index observations and changed referents. Distinct-object controls discriminate
both branches of the first-write read formula with different source/destination
objects. Fresh fields retain old identities; their deep contents are not frozen.

`BoolChildRepr.interstage` and `RefChildRepr.interstage` derive final old-child
correspondence from initial representation, actual operations, intermediate
Keeps, and both destination/root/leaf separation facts. The first root frame and
weakening derive the second leaf footprint. An allocator corollary and inhabited
existing-certificate chain reuse a published immutable child table: parent IDs
change `[1,0,1]` to `[0,0,1]` then `[0,1,1]` across actual allocation. No fresh
Source entry or new address injectivity is assumed. The concrete correspondence
controls instantiate Boolean and nested children. Both reviewers identified the
initially missing nested application; `existing_nested_chain` now reuses the
published nested certificate, records actual first success, allocation on mid
and second success, and derives final root/leaf correspondence. Its nonempty
first write changes parent IDs `[3,2]` to `[3,3]`; the second recaptures that
changed slot. Published type separation discharges both root and leaf frames.
Generic nested footprint transport is proved, not arbitrary recursive traversal.

The combined focused closure passes69jobs after repairing the closed singleton
capacity proof. Failed attempts01-04 and their sorryAx diagnostic output remain
raw evidence; successful final guards contain only standard axioms. Exactly36
new guarded headline pins are additive proposals, not edits to reserved inventory.
Full final gate exits0:888default jobs,262TestSuite jobs, and final SolKey377taclets,
131read-bearing, annotations OK. Refined full02 sampled aggregate Lean/Lake RSS peak1,445,080KiB;
container cgroup peak386,539,520bytes,12GiB/no-swap and serial-j1 containment.

G32 remains partial: typed frames do not supply all heap-to-physical-byte clauses.
G33 remains partial: this supplies interstage existing-object allocation transport,
not all-type defaults, target allocation failures or reserved reference builders.
G34 remains partial: general paths/rebinding/delete and stale-alias compilation
remain open. G35.01 is partial; G35.02 is blocked on its reserved copy prerequisite.
G35.03 remains partial: decoded correspondence is not ABI/general calldata/source
execution. G35.04 advances actual interstage recapture but does not realize fresh
deep copy. G35.05 remains partial: no arbitrary recursive child-copy liveness.
G35.06 remains blocked on reserved copies and V10/Source/target composition.
Backfill A and B remain partial, with substantive bounds/frame/identity progress;
no claim is made that all further independent refinements are unavailable.
Fresh-root representation, new-address injectivity, recursive traversal/copy,
physical byte-memory and final compiler composition remain explicit obligations.

Checkpoint-nine export directory:
`/workspace/v11-memory-operations-evidence/checkpoint9`. Exact committed head,
cumulative patch/bundle, command logs, reviews and checksums are recorded there.
Prior sealed exports, errors, caches, original checkout and runtime TOML remain
untouched. No integration, global ledger/status rewrite or goal transition occurs.


Final checkpoint-nine source finder and skeptic reviews found no confirmed
mathematical, hypothesis, ownership or nonvacuity defect. Their concrete nested
witness gap was fixed, checked and re-reviewed. Their evidence wording finding
was fixed: final metrics refer to refined `v11-checkpoint9-full-02`, exit0,
OOMKilled=false; prior full01 and all failed focused runs remain distinct raw logs.
Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b and
Lake5.0.0-src+797c613 execute; KeySort passes2jobs in
`v11-checkpoint9-runtime-01.log`: RUNTIME_GATE_PASS is setup evidence only.
Strict automation, complete committed-snapshot TestSuite parity/trust, layer,
orphan, trust, owned boundary/standard-pin, script syntax and diff checks pass.
Owned evidence covers222standard pins37modules. Global axiom inventory still
exits1:0unsafe errors236unrecorded=14inherited+222owned. Global docs still exits1
with46findings; raw output equals the exact frozen-base log, so the separate
no-new-findings comparison passes. Neither global failure is relabeled green.
Proposed additive registrations and exact feature IDs remain coordinator work.
No external compiler/EVM execution or Source/target allocation semantics is claimed.
The existing blocked goal is unchanged; get_goal and per-file diagnostics RPCs
remain unavailable. All original queues and mandatory unfinished gates stay open.


## Checkpoint ten: published multi-object builders between snapshots

Parent `c7ac6ae92ba4c35b2a28e538efee2e6346240bc5`, exact frozen base unchanged.
Reproduced gap: InterstageGrowth used one supplied MObj; ContextTransport and
SliceExtension used published builders outside a two-capture operation chain.
The new InterstageBuilders module applies actual SVal.copyStToM to actual mid,
consuming its Grown.H', ext, heap and val and SVal.keeps_copyStToM read-only.
Heap.allocDefault is definitionally the published typed-default copy, exercised
as an actual builder, not replaced by another construction implementation.

captureAfterCopy_checked/keeps and copy_interstage_success/read_cases/none_iff
transport actual second operations through that concrete growth. Premises remain
actual first checked Some mid, existing mapFree=true, and second source bounds /
destination capacity measured in mid. The read formula observes changed first
payloads; none classifies SECOND snapshot guards, not construction/target failure.
copy_interstage_alias preserves old IDs/aliases; copyStToM_id_ge separates the
fresh root. captureAfterCopy_fresh frames the fresh root's own fields.
The additional independent Backfill frame captureAfterCopy_new_frame proves that
any typed object with ID at least old H.length is framed by the actual second
old-object write. Concrete final copied-child contents discharge that ID fact;
no arbitrary-depth descendant freshness or Source/target liveness is inferred.

Dynamic controls run real nested fixed-of-dynamic defaults and nonempty storage
trees, each adding two children and a root to H=[B]. Actual roots are3, children
are1/2, old alias remains0. First [0,2) to2 then recapture [2,4) to4 yields
[true,false,true,false,true,false], differing from original source data.
Typed reads, exact fresh fields/IDs, empty default children versus copied
[true]/[false] children and final output child frames are recorded. First and
second intervals touch. Six isolated second-stage reversed/source/destination
failures and both exact-end empty operations are checked as actual Option values.
Fixed/reference controls grow old [B,B,P] by three actual copied objects, root5;
first right-overlap and second left-overlap yield old parent IDs [0,1,0,0].
Original-payload freezing yields [1,0,1,0], a distinct actual heap. Old children
remain framed; fresh copied children are not claimed to alias old children.
Existing Boolean and nested immutable child certificates are reused across
actual first Some, actual three-object storage/default growth, second Some,
final old-child correspondence and root framing. No Source table is fabricated.

Focused combined closure passes71jobs. Failed proof attempts and one failed
simp-list cleanup remain raw logs; no sorry/axiom/trust shortcut is delivered.
Exact new headline guards, registration, reviews and final gate outcomes follow.
Per-file diagnostics and get_goal are unavailable; existing goal stays unchanged.
No competing server/build, budget increase, reserved implementation or integration.

Every original queue remains partial/blocked: G32 physical byte representation;
G33 all-type/default/target size-allocation failure and reserved constructors;
G34 general paths/rebinding/delete/stale-alias compilation; G35.01 full storage
copy compiler bridge; G35.02 reserved memory-storage copy prerequisite;
G35.03 general calldata/ABI/source/storage transport; G35.04 fresh deep-copy
execution; G35.05 unrestricted recursive traversal/copy liveness; G35.06 reserved
copies and V10/Source/target composition. Backfill A/B advance concrete builder
transport and fresh ID framing but remain partial. Missing fresh Source root
representation/address injectivity, recursive premises and mandatory global
registrations remain explicit. No assertion that all independent work is exhausted.

New cumulative export directory:
/workspace/v11-memory-operations-evidence/checkpoint10. Prior seals/errors/caches,
original checkout and untracked runtime TOML are preserved. Coordinator must
reconcile additive owned pins/feature IDs; reserved inventories/ledgers unchanged.


Checkpoint-ten final confirmation: v11-checkpoint10-full-01 exits0,892default
jobs,262TestSuite jobs, final SolKey377taclets/131read-bearing, annotations OK.
All29new headline outputs are kernel guarded with only the standard axioms;
owned checker passes251pins41modules. Lean4.24.0 commit
797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Lake5.0.0-src+797c613 execute;
fresh KeySort passes2jobs in v11-checkpoint10-runtime-01.log. RUNTIME_GATE_PASS
is setup evidence, not lane completion. Final sampled aggregate Lean/Lake RSS
1,570,940KiB; cgroup peak422,260,736bytes; OOMKilled=false,12GiB/no-swap child
containment,16GiB parent/OS headroom, serial Lean-j1/LEAN_NUM_THREADS1 unchanged.
Strict automation, complete committed-snapshot TestSuite trust/parity, layers,
orphans, trust, owned boundary/standard-pin, script syntax and diff gates pass.
Global docs exits1 with46findings, raw exact-base output equal; separate no-new
comparison passes. Global inventory exits1:0unsafe errors265unrecorded changes,
14inherited+251owned. Neither global failing gate is relabeled green. Exact
additive proposals are exported for coordinator reconciliation, no inventory edit.

Independent read-only finder and skeptic reviews inspected all four modules,
actual hypotheses/nonvacuity, negative controls, new-object frames, registrations
and document; neither used Lean/server/builds. Both found no remaining source or
ownership defect. Their initial final-descendant observation gap was fixed by
captureAfterCopy_new_frame and actual final_child_contents; re-review confirmed
that ID facts remain explicit and arbitrary-depth freshness is not assumed.
Kernel proofs and concrete intrinsic controls are distinct from external
compiler/EVM tests: no such external execution or complete compiler proof occurs.
Checkpoint artifacts include full commands/exits/raw failures, cumulative patch,
named-ref bundle, handoff, independent artifact reviews and checksum manifests.
Only owned new modules/allowed registrations/document are committed; runtime
TOML stays untracked. Original goal remains unfinished and unchanged.


## Checkpoint eleven: recursive transport of the published typed mirror

Parent a83ebeeab11198ad9cc20682e7bcbb6271cf47a4; pinned base unchanged.
After sealing checkpoint ten, further original-queue investigation found the
published Solidity/Theory/Typed/MemMirror.lean relation SVal.Mirrors already
records contents and ID lower bounds recursively throughout finite typed storage
trees. It preserves growth, but lacked the owned operation-side transport through
second old-object writes. CopyMirrorFrame adds transport of that EXISTING relation,
not a new value/state/interpreter/copy implementation or source correspondence.

mirrors_frame, fields_mirrors_frame and vec_mirrors_frame recurse over existing
SVal/SFields/SVec, with no depth or payload cutoff. Their explicit premise is
equal object contents at every typed identity at least n. The concrete theorem
captureAfterCopy_mirrors discharges that frame from actual captureAfterCopy's
new-object frame; the published SVal.mirrors_copyStToM supplies each node's
ID bound and initial contents. Thus the postrelation is derived, not assumed.
captureAfterDefault_mirrors instantiates actual Heap.allocDefault's typed default.
Both retain mapFree=true and the actual intermediate source bounds/capacity.
This closes recursive INTRINSIC mirror preservation for this operation case,
not the original unrestricted source/target recursive-copy compiler obligation.

Controls quantify arbitrary n for fixed arrays of reference-containing fixed
children of nonempty dynamic Boolean arrays, recording actual first checked
Some mid, actual multi-object builder and second checked Some final. The complete
published recursive mirror holds at final output for copied and default trees;
old recapture actually changes false to true. A nonzero published Person with
Account/Token reference fields exercises the nonempty SFields/struct arms and
observes final age11. An initially inhabited old-object mirror is destroyed by
the actual first overwrite: removing the fresh frame would be unsound.

Independent finder and skeptic identified the initially missing concrete struct
branch control; person_copy/person_default now supply it using published fields,
without implementing any reserved reference constructor. Focused frame passes68
jobs and refined controls pass69jobs. Failed negative-control elaboration attempts
are retained separately; all11new headline outputs have exact standard guards.
Final source review and required gate/artifact confirmation follow below.

The remaining original obligations remain partial/blocked: physical byte-memory
representation and execution; all-type/default/target allocation failure; general
paths/rebinding/delete/stale-alias compilation; reserved memory-storage copies;
general calldata/ABI/source/storage transport; fresh memory-to-memory deep-copy
realization; mapping/shadow/source/type-graph/cycle and emitted recursive traversal
coverage; fresh Source root representation/address injectivity; final reserved
copy and V10/Source/target composition. Mirrors does not by itself prove pairwise
fresh-node distinctness or address injectivity. Backfill A/B remain partial, with
this additional supported independent recursive frame clause now proved. No
claim that all further independent refinements are exhausted.

New cumulative exports: /workspace/v11-memory-operations-evidence/checkpoint11.
Checkpoint10 and all earlier sealed artifacts/errors/caches remain immutable.
Original goal unchanged/unfinished, get_goal/per-file diagnostics unavailable;
serial-j1,12GiB/no-swap and all proof/fuel/test/time budgets unchanged. No reserved
file, global ledger/inventory, Source semantics, profile or integration change.


Checkpoint-eleven final gate v11-checkpoint11-full-01 exits0:894default jobs,
262TestSuite jobs, final SolKey377taclets/131read-bearing annotations OK.
Refined source finder and skeptic both confirm the nonempty struct witness gap
is fixed, with no remaining mathematical/ownership/nonvacuity/doc defect. Neither
reviewer used Lean/server/builds. All11new kernel guards use standard axioms;
owned checker passes262pins43modules. Strict automation, complete committed
TestSuite trust/parity, layers/orphans/trust/script/diff checks pass. Global docs
still exits1,46findings raw exact-base equal; separate no-new comparison passes.
Global inventory still exits1:0unsafe errors276unrecorded=14inherited+262owned.
Additive proposals remain coordinator reconciliation; no reserved pin edit.
Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b and
Lake5.0.0-src+797c613 execute; KeySort passes2jobs in checkpoint11-runtime log.
RUNTIME_GATE_PASS is runtime/setup only, never full-lane completion.
Final sampled aggregate RSS1,602,300KiB, cgroup peak392,908,800bytes,
OOMKilled=false;12GiB/no-swap child,16GiB parent/OS headroom and serial-j1 unchanged.
These are kernel intrinsic proofs plus concrete controls, not external compiler/
EVM evidence. Final cumulative artifacts/checksums and independent artifact
receipts are exported separately after commit; all earlier seals remain intact.
Existing goal remains unchanged and unfinished; no integration is authorized.


## Checkpoint twelve: two actual builder generations and checked writes

Parent3af6f9c8885f2ccd1c6a7bb2067dfd7f08df521c; frozen base/branch unchanged.
Reproduced gap: CopyMirrorFrame preserves one mirror through one same-heap frame
or one builder/write. Published Mirrors.wk preserves growth, but no owned result
composed two actual multi-object builders with checked original-object writes
between/after them, both final recursive mirrors and cross-generation identity.
BuilderComposition now supplies that operation-side composition, not a new copy
implementation, heap/traversal semantics, Source table or compiler bridge.

captureAfterCopy_old_len derives every original typed array's intermediate length
from actual first-copy Keeps and snapshot length preservation. two_builders_success
uses those equalities to derive second bounds from original lengths, with actual
checked Some results for both writes. two_builders_none_iff classifies only the
second snapshot's reversed/source/destination failures; no target construction
failure or rollback semantics is inferred. Each builder retains mapFree=true.

two_builders_mirrors derives the first tree's intermediate mirror from actual
copy/write, weakens it through the second actual copy's Keeps, then frames it at
the ORIGINAL heap's ID threshold under the second original-destination write.
The second tree's recursive mirror comes from the published copy theorem and its
higher threshold. It also frames all earlier-generation fresh typed objects.
Cross-generation root separation follows from earlier HRef.id_lt and the second
copy's id_ge. generations_mirror_ne applies the same reasoning to any later
observed child using its derived recursive mirror bound. No final relation,
within-copy pairwise distinctness or global address/hash injectivity is assumed.

Controls record ordered actual checked results and both final mirrors for nonzero
Person/Account/Token copying followed by real nested default construction, and
for arbitrary n same-type fixed/reference/dynamic-child array copies. Final
Person fields observe11/9/7; a final default child is empty and separated from an
actual earlier Account field whose weakened identity is retained. Same-type
array roots and observed Boolean children are separated across generations;
both final children retain [true]. Empty builder payloads and exact-end empty
snapshots are inhabited. Old aliases retain ID0; changed recapture observes true
at33 whereas original index32 was false. The32/33 checks are element boundaries,
not physical byte encoding. Isolated reversed/source/destination failures remain
actual Option.none. descendant_mutation_negative performs an actual checked
write from an old false slot INTO a copied child: the parent pointer stays the
same, the child becomes false, and the later recursive mirror fails. That case
is supported by the operations, outside this framing theorem, never excluded.

Independent source reviews identified two initial evidence gaps: the Person
comment overstated explicit observations, and idle-container OOMKilled=false
could miss an exec-worker OOM. Explicit final fields and corrected wording fix
the first. The new runner records cgroup memory.events before/after every new
command (including oom/oom_kill deltas); cumulative session peak is labeled.
No source, proof or expected observation was weakened. Focused core03 passes69
jobs, refined combined01 passes70jobs, all14new headline outputs have exact guards.
Failed focused attempts remain separate logs, not relabeled passes.

Operational disk investigation: initial available1,361,448,960bytes fell to
848,969,728bytes while using retained per-gate containers. Docker uses VFS, which
copies the image filesystem per container; existing containers/caches were NOT
deleted. One new SAME-VM container v11-two-builders-session reuses the identical
12GiB/no-swap limits, user, mounts, LEAN_NUM_THREADS1, keyed cache and toolchain
for serial Lean-j1 checks under the writer lock. Creation cost170,774,528bytes;
subsequent focused checks keep availability around675MB. Initial runner source
is preserved; run-checkpoint12-gate.py uses exclusive new logs and per-exec OOM
counters. This is not a VM/thread/goal replacement or resource-budget increase.
Final full/static/resource results and artifact review follow below.

Full original-queue audit against coverage-plan: G32 remains partial for actual
nested/reference byte-addressed representation and target separation; G33 remains
partial for all in-profile default/allocation compilation and exact target size/
allocation failures (conditional intrinsic capacities do not close it); G34 remains
partial for general path/rebinding/delete/stale-alias compilation. G35.01 remains
partial: published intrinsic tree copying/recursive mirror and generation frames
are checked, not its full source/target compiler. G35.02 is blocked on the reserved
memory-storage-copy prerequisite. G35.03 remains partial for general calldata/
ABI/source/storage transport. G35.04 remains partial for fresh memory-to-memory
execution/emission and full alias/deep-copy cases. G35.05 remains partial for
Source/type-graph/cycle/mapping/shadow and emitted recursive traversal coverage;
finite map-free intrinsic mirror composition is now stronger. G35.06 is blocked
on reserved location-copy and V10/Source/target prerequisites. Backfill A/B remain
partial, with this additional supported noninterference/identity composition.
No parent or original queue is complete and no claim that all independent
refinements are exhausted. All approved shapes, refusals and budgets remain.

Global doc-count clarification: the retained raw exact-base checker output has
72missing/ambiguous rows, of which46are missing references; its FAIL footer counts
those46missing references. Earlier shorthand46findings did not count ambiguity
rows. The raw74-line output/hash remains unchanged in every sealed package.
No historical record is rewritten. Global inventory proposals remain coordinator
reconciliation, never edits to the reserved inventory/ledger/coverage manifest.

New cumulative exports: /workspace/v11-memory-operations-evidence/checkpoint12.
Every checkpoint11/earlier seal, original checkout, runtime TOML, cache and failure
is preserved. Per-file Lean RPCs and get_goal remain unavailable. Existing goal
is unfinished; no integration. Kernel evidence is distinct from external EVM/
compiler testing, Source/layout correctness and physical byte-address injectivity.


Checkpoint-twelve final confirmation v11-checkpoint12-full-01 exits0:896default
jobs,262TestSuite jobs and final SolKey377taclets/131read-bearing annotations OK.
Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b,
Lake5.0.0-src+797c613 and actual KeySort2jobPASS are retained in
v11-checkpoint12-runtime-01.log. RUNTIME_GATE_PASS remains setup evidence only.
Final sampled aggregate Lean/Lake RSS1,575,568KiB; cumulative session cgroup peak
391,729,152bytes. Final command's memory.events before/after allzero, including
zero oom/oom_kill deltas; do not infer worker health from idle PID1 OOMKilled.
12GiB/no-swap,16GiB parent/OS headroom, serial-j1 and fixed budgets unchanged.
Final full command disk availability675,328,000before/674,627,584after bytes;
no resource stop, deletion or budget expansion. Idle session is retained for
future serial checks without another VFS image copy; it runs no Lean/LSP work.

Strict automation, complete committed-snapshot TestSuite trust/parity, layers,
orphans, trust, owned boundary/pins, script syntax and diff checks pass. The owned
checker validates276standard pins45modules. Global inventory still exits1 with
0unsafe errors290unrecorded=14inherited+276owned; exact additive proposals remain
coordinator reconciliation. Global docs still exits1 with72missing/ambiguous rows
(46missing,26ambiguous), raw exact-base equal; separate no-new comparison passes.
Nothing rewrites reserved inventory/ledger/coverage records or historical seals.

Independent read-only finder and skeptic final source reviews found no remaining
mathematical/hypothesis/nonvacuity/ownership/doc defect; neither ran Lean/server/
builds. Both confirmed complete ordered array observations, explicit Person fields,
actual same-type generation separation and the checked descendant mutation
negative. Earlier evidence/comment and per-exec OOM findings are fixed and retained.
Final artifact review follows commit/export. All original Work/Backfill queues
remain partial/blocked for the exact audited prerequisites above; no full-lane,
Source/compiler/EVM or physical-byte execution result follows from kernel checks.


## Checkpoint thirteen: actual decoded Boolean transfer (G35.03, Backfill A/B)

The reproduced gap was concrete: CalldataTransport takes an existing values list
and pointwise relation; CalldataNestedChildren transports existing pointers.
Neither constructs a payload from the actual immutable decoded table. The new
CalldataTransfer module eliminates Source.Data/Val.bool, extracts a finite list
from a decoded Boolean array found in Calldata.objects, and invokes the existing
overwriteSlice with exact checked bounds. No payload or conversion-correctness
premise is supplied. Dynamic/static Source Boolean arrays and dynamic/fixed typed
heap destinations are supported. Other/missing entries, including pointer-valued
objects, return None at this adapter; this is not a new admitted-source refusal.

calldataBools_lookup and calldataBool_exact establish extraction directly from
published constructors. checkedCalldataBools_some/result/none_iff derive actual
success and exactly reversed/source/destination guard failures from the actual
runtime length. checkedCalldataBools_read supplies every immutable finite source
read and corresponding destination observation; elems gives the entire ordered
replacement. outside/frame retain exterior cells and every distinct typed object.
The initial DecodedArrayAt premise is an input lookup, not a desired output
relation. No generic preservation relation is assumed. checkedCalldataBools_keeps
also transports actual success and all old typed observations through existing
Heap.Keeps; the payload is heap-independent. allocated_transfer discharges Keeps
with a real Heap.alloc, frames its fresh parent and observes the changed child.
Structural parent preservation is not deep child-content liveness.

Controls derive their concrete representation lookup. They execute a nonuniform
changed transfer, observe exact ordered contents, distinguish wrong value/order,
frame two exterior cells and a reference-containing parent, run static Source to
fixed destination, empty/exact-end cases, missing/wrong type/location/pointer and
wrong-element entries, and independent reversed/source/destination bounds failures.
An arbitrary-length family uses only the intrinsic heap n<2^256 invariant, with no
new payload cap. A full34-element observation crosses indices32/33 as ELEMENTS,
never as a physical-byte-encoding claim. Existing operations/shapes remain intact.

Focused raw failures and the old-log collision guard are retained separately.
The collision refused to overwrite a historical log; new names use cp13. No old
error was mistaken for a current build failure or rewritten. All proof repairs
preserve statements and budgets. No Lean MCP diagnostics/get_goal are exposed;
focused serial Lake closures are used. Runtime is the retained same-VM container
v11-two-builders-session via unchanged run-checkpoint12-gate.py, no image copy or
cleanup. Parent16GiB, child12GiB/swap0, serial Lean-j1/LEAN_NUM_THREADS1 and per-exec
memory.events/OOM deltas remain enforced. Availability began673193984bytes and
remains about666MB after warm focused outputs. Prior seals remain immutable.

This advances actual primitive decoded-data transfer only. It is not ABI decoding,
Source expression execution, fresh reference construction, a target emitter,
physical byte transport, storage copying or V10/Source/target composition.
Further primitive families require their exact published numeric/representation
conversion clauses, not a guessed shared encoding. Existing finite map-free mirror
results remain separate. No external EVM/compiler test is inferred from kernel
proofs. All G32/G33/G34/G35.01/.03/.04/.05 and Backfill A/B remain PARTIAL; G35.02
and G35.06 remain BLOCKED on reserved copy/final composition prerequisites. Every
checkpoint12 queue detail above remains open; no assertion of independent-work
exhaustion or whole-lane completion. Final gate/review results follow below.


Checkpoint-thirteen final bounded run v11-checkpoint13-full-01 exits0 with898
initial/default jobs,262TestSuite jobs and final SolKey377/131 annotations OK.
Complete ordered gate stdout and per-exec receipt are retained. Peak aggregate
Lean/Lake RSS1458384KiB; session memory.peak454889472bytes is cumulative, not exec
worker RSS. memory.events before/after allzero, no OOM deltas. Disk665649152before/
665034752after bytes; fixed12GiB/no-swap and parent16GiB bounds are unchanged.
Required layers/orphans/trust/owned checker, strict automation, complete fixture
parity and script/diff checks pass. Owned checker validates300standard pins47
modules. Raw global inventory exits1 with0unsafe errors314unrecorded entries=
14inherited+300owned. Raw strict docs exits1, byte-identical to exact-base output
SHA256ea1a09c222d52d1d17953f653c087443e34e6282497f0b02cdc09aad15b7dd48;
separate no-new comparison passes. Reserved inventories remain untouched; additive
proposals are checkpoint13-proposed-axiom-pins.json for coordinator reconciliation.
Separate independent finder/skeptic source reviews found no confirmed defect and
accepted final refined source/doc hypotheses and controls without correction.
No reviewer ran Lean/server/builds. Artifact review follows commit/export.


## Checkpoint fourteen: exact uint256 decoded transfer (G35.03, Backfill A/B)

Continued independent implementation after checkpoint13: published Source.IntTy
u256 has inclusive range0..2^256-1; intrinsic PrimTy.uint.inRange uses0<=x<2^256.
The new CalldataUintTransfer proves these exact bounds and retains the SAME Int.
sourceUint and calldataUint are typed wrappers over the existing constructors;
calldataUint_exact and calldataUint_sourceUint establish the two directions.
calldataUint_values derives finite-list reconstruction for arbitrary runtime
lists, no supplied conversion-correctness premise or truncation/modulo. This is
not a scalar compiler, alternate value layer or ABI decoder.

checkedCalldataUints consumes the actual immutable table, selects unsigned256
array objects (dynamic/static), eliminates their typed leaves, captures the
runtime slice and invokes existing overwriteSlice. It does not accept a payload.
Exact some/result/none_iff/read/elems/outside/frame/no_payload/keeps theorems retain
the Boolean adapter's explicit input lookup, bounds/capacity/ID/initial extension
premises and derived output observations. The additional empty theorem proves
whole-heap identity for any valid zero interval. Other signedness/widths remain
unsupported by this adapter, never removed from the admitted Source profile.
No Source table is fabricated to represent fresh memory references.

Controls execute a nonuniform payload including0,7 and2^256-1, observe the complete
ordered Int output and immutable typed reads, reject a wrong-order result and
frame exterior cells/reference parent. Fixed decoded input into a fixed target
also retains the maximum exactly. Arbitrary typed runtime lists succeed when
the actual existing target has capacity; no added length/depth cutoff. Empty at
end and actual zero-length destination both succeed. Reversed/source/destination
checks fail separately; uint8, signed256, pointer-valued entries and missing offsets
return None. An element31/32/33 slice yields ordered0,max,7. Actual Heap.alloc
instantiates keeps and frames a fresh alias-containing parent while the old child
receives max. Fields retaining old identities do not imply child-content liveness.

Preliminary independent finder/skeptic reviews found no range/semantic/ownership
defect and requested concrete uint-specific allocation, zero-target and boundary
controls; those are now proved. Neither reviewer used Lean/server/builds. Focused
failures remain retained separately; corrections only fixed redundant decide
conversion, Fin observation normalization and primitive weakening identity.
No proof/test/resource budget changed. The same retained12GiB/no-swap serial
runtime and disk caches are reused, without deletion or another image copy.
Further signed/narrowed/other primitive representation families, general calldata
references, ABI/source expression execution, fresh reference construction, byte
transport and Source/V10/target composition remain open. No compiler/EVM run is
inferred from kernel checking. G32/G33/G34/G35.01/.03/.04/.05 and Backfill A/B are
still partial; G35.02/.06 remain blocked on reserved copy/composition prerequisites.
The complete checkpoint12/13 queue audit still applies. No original queue or
parent group is complete and no claim all independent refinements are exhausted.
Final bounded checks, source reviews and cumulative export follow below.


Checkpoint-fourteen final bounded v11-checkpoint14-full-01 exits0:900default
jobs,262TestSuite jobs, final SolKey377taclets/131read-bearing annotations OK.
Current runtime versions/KeySort2jobPASS from checkpoint13-runtime-01 remain
unchanged and retained (Lean4.24.0 commit797c613, Lake5.0.0-src+797c613).
Final full peak aggregate Lean/Lake RSS1457172KiB; cumulative session peak
454889472bytes is separately labeled, not exec-worker RSS. Per-exec memory.events
before/after allzero with0OOM deltas; enforced12GiB/no-swap and parent16GiB bounds
unchanged. Disk658968576before/658345984after bytes; no deletion or new runtime.
Layers/orphans/trust/strict automation/complete TestSuite parity/script/diff and
owned328standard pins49modules checks pass. Strict automation reports491automatic,
61step-budget,0manual,11refuted,0pending; cached timing rows are not cold rebuild
measurements. Complete fixture observations/verdicts and exclusions are unchanged.
Global inventory still FAILexit1:0unsafeerrors342unrecorded=14inherited+328owned.
Additive checkpoint14-proposed-axiom-pins.json awaits coordinator reconciliation;
reserved inventory/ledger/manifest files remain untouched. Raw strict docs still
FAILexit1 with exact-base byte-identical74line output72missing/ambiguous rows;
separate no-new comparison passes. No raw failure is relabeled green.
Both independent final source reviewers accepted the refined actual statements,
nonvacuity, complete observations, negative controls, ownership and owning document
without further defect. Artifact reviews follow commit/export. The full original
Work/Backfill audit remains partial/blocked, not completed by these two families.


## Checkpoint fifteen: composing actual decoded transfers (G35.03, Backfill A/B)

Reproduced the precise gap: existing CalldataTransfer/CalldataUintTransfer execute
one actual decoded transfer; generic capture-based sequence laws capture heap
payloads, not the immutable decoded tables. New checkedBoolSequence,
checkedUintSequence, checkedBoolUintSequence and checkedUintBoolSequence are ONLY
Option.bind of these existing operations. They accept Source.Calldata/typed heap
refs and runtime coordinates, never caller-supplied payloads or conversion proofs.
No AST, interpreter, replacement heap/allocator/decoder/emitter or semantic layer
is introduced. Reserved implementations and all Source definitions stay untouched.

result_lookup reconstructs only payloads actually extracted by a successful
operation. all_len derives every typed array length using overwriteSlice_all_len.
Sequence_some_iff exposes actual reached intermediate/final heaps. none_ordered
records first rejection short-circuit or actual firstSome plus secondNone. General
none_lookup includes missing/unsupported entries and all three runtime guard cases;
sequence_none_iff reduces second rejection to the original heap through the proved
length equality. No preservation premise is assumed. None_keeps covers arbitrary
failed lookup/bounds through initial preserving growth. Successful keeps derives
the intermediate Keeps before applying the second existing transfer theorem.
Input decoded-array lookups remain explicit representation premises for finite
Source-read laws, never desired output relations. All bounds are actual runtime
length/capacity premises, no arbitrary payload or depth admission cutoff.

Same_elems derives the complete nested replacement from both actual operations.
Second_read gives actual immutable second-source reads including overlap;
first_exterior preserves actual first-source reads outside the second destination.
Same_comm uses overwriteIntervals_comm for locally separated intervals, allowing
empty/touching cases. Other_comm and mixed_comm use overwriteTwo_comm/frame for
distinct objects. Bool/uint array ID separation follows from existing HRef/ArrTy
indices; no same-ID cross-type witness or global address injectivity is assumed.
These are sufficient local commutation cases, not new Source exclusions.

Controls execute unequal nonuniform decoded inputs and complete ordered outputs.
They distinguish reversed overlap precedence, ignored first writes and an ACTUAL
stale-source call reusing the first table as the second. Touching intervals and
different same-family objects commute with changed complete outputs; mixed Bool/
uint operations commute and retain max2^256-1 without truncation/reordering. The
reference-containing parent keeps its IDs while its Boolean child really changes.
Actual Heap.alloc discharges composed growth, frames its fresh parent and retains
both complete old-object outputs; rejection also transports through that actual
allocation. Fixed uint overlap, arbitrary runtime list families, empty/exact-end,
and element31/32/33 observations are inhabited. Missing/unsupported first versus
reached-second input and isolated first/second reversed/source/destination guards
are observed. Option observations imply no Source halt, rollback or ABI/bytecode
correctness. Initial immutable fixture tables do not represent newly allocated
Source objects and no fresh Source entry/address premise is manufactured.

Disk/runtime preflight measured656846848bytes free, parent16GiB and child12GiB/
swap0, idle retained container and no Lean workers. Small warm increments now
leave roughly649MB; no new runtime/image, deletion or RAM cache relocation.
All work uses the writer lock, serial-j1/LEAN_NUM_THREADS1 and unchanged guards.
Per-file Lean diagnostics and get_goal are unavailable; focused serial closures
are retained. Focused failures are distinct raw logs; repairs preserve statements
and observations (case normalization, explicit allocator type, dependent rewrite
ordering), never budgets or assumptions. Full final gates/reviews follow below.

Full original queue audit: G32 still needs actual nested/reference physical-byte
representation and target separation. G33 still needs all-profile constructor/
default compilation and exact target size/allocation failure; published reference
constructors stay reserved. G34 general path/rebinding/delete/stale-alias target
execution remains. G35.01 consumes published copying/Mirrors and proves frames,
not source/target copying correctness. G35.02 is blocked on reserved memory-to-
storage copying. G35.03 now composes real primitive decoded transfers, but general
families/references, calldata-to-storage, ABI/independent Source execution and
target transport remain. G35.04 fresh memory deep-copy execution/emission and full
alias classification remain. G35.05 Source/type-graph/cycle/mapping/shadow/emitted
traversal remains, beyond finite map-free intrinsic Mirrors. G35.06 is blocked on
reserved copies and V10/Source/target composition. Backfill A/B remain partial;
no claim of independent-refinement exhaustion or whole-lane completion. Exact
manifest evidence proposals remain additive coordinator reconciliation only.


Checkpoint-fifteen final v11-checkpoint15-full-01 exits0:906default jobs,
262TestSuite jobs and final SolKey377/131annotations OK. Actual runtime15 log
retains Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b,
Lake5.0.0-src+797c613 and KeySort2jobsPASS before RUNTIME_GATE_PASS.
Peak aggregate Lean/Lake RSS1454864KiB; cumulative session peak454889472bytes is
separate from exec RSS. Every new per-exec OOM delta is0. Final full disk
647204864before/646656000after bytes; fixed12GiB/swap0/parent16GiB bounds unchanged.
Layers/orphans/trust/strict automation/complete fixture parity/script/diff and
owned408standard pins55modules pass. Global inventory remains FAILexit1 with
0unsafeerrors422unrecorded=14inherited+408owned; exact additive proposal awaits
coordinator reconciliation. Strict docs remains FAILexit1 with byte-identical
exact-base74line72missing/ambiguous findings, separate no-newPASS. No reserved
inventory, ledger or manifest changed and no raw failure was relabeled green.
Both independent final source reviews found no confirmed defect; neither ran
Lean/server/builds. The new sequence is actual operation composition, not full
Source/target correctness. All original queues remain partial/blocked. Subsequent
independent child-frame transport is still worth investigating, not presumed done.


## Checkpoint sixteen: existing child correspondence after actual mixed transfers

Returned to original Backfill B/G35.03/.05 after checkpoint15 was committed,
reviewed and sealed. The existing BoolChildRepr/RefChildRepr describe actual
immutable decoded child-table entries and heap contents, but were not connected
to the new actual decoded-transfer sequence. CalldataSequenceChildren consumes
those EXISTING relations; no fresh Source entries or alternative relation/state
is introduced. ActualSome reconstructs both operations, then derives typed
object frames. Distinct ID OR an empty source interval suffices: the latter
follows from real empty overwrite identity, not a final-content premise.

BoolChildRepr.mixedSequence derives the relation at the FINAL heap. The uint
write cannot alias a Boolean child by intrinsic types. RefChildRepr.mixedSequence
frames its root by primitive/reference-array type separation and frames every
original selected Boolean leaf. Leaves may repeat/alias one another; each must
be distinct from the Boolean destination OR the first source interval empty.
This is a local sufficient frame theorem, not a new source exclusion or claim
that all supported alias writes preserve correspondence. Only Bool→uint order
and the existing two-level reference/Boolean relation are covered; arbitrary
Source graphs/deep-copy realization still remain. No reverse address injectivity,
physical bytes, compiler preservation or fresh-root Source representation is
assumed. Initial relation premises are explicit, independently inhabited, and
no desired output relation or supplied conversion proof is a premise.

Controls construct only OLD initial root/leaf Source table entries and the real
typed heap. A runtime family for every intrinsic-valid n (n<2^256, no added cap)
has n repeated aliases to one old child. Actual decoded mixed writes change a
separate Boolean object and uint object (including max2^256-1), while final root/
child correspondence and typed index observations preserve every repeated ID.
The concrete n33 index32 observation is an ELEMENT boundary, not byte encoding.
An actual aliased Boolean transfer at its empty exact end succeeds and retains
correspondence without leaf-ID separation. An actual nonempty aliased transfer
changes the represented child's contents and invalidates the initial immutable
relation whenever the root selects at least one child. A separate n0 witness
shows the root relation does not constrain an unselected child; vacuity is
explicitly confined to that empty case. No alias shape was removed from Source.

Both preliminary independent read-only reviewers found no circularity, ownership
or mathematical defect. The generic clause and nonempty witnesses avoid a mere
conditional certificate result. Neither reviewer used Lean/server/builds. The
first focused controls failure was kernel decide encountering still-folded heap
fields with runtime n; explicit fixed-field reduction fixes it without changing
any statement, bound or budget. Raw failures remain retained. Current refined
closure and exact guards precede final full checks/reviews below.

The renewed preflight retained over645MB free and reused the same capped idle
container/cache; focused outputs leave over643MB. No deletion/image creation/RAM
cache relocation or resource/proof/test budget change. All original G32/G33/G34/
G35.01/.03/.04/.05 and Backfill A/B remain partial; G35.02/.06 remain blocked.
The prior full queue audit still applies, including physical representation,
all-profile constructors/target allocation failure, general path/rebinding/delete,
general decoded/reference conversions, fresh deep copy, reserved location copies
and final V10/Source/target composition. No independent-refinement exhaustion or
whole-lane/parent completion is asserted. Exact manifest/pin proposals remain
coordinator-only reconciliation, with no reserved ledger/inventory edits.


Checkpoint-sixteen final v11-checkpoint16-full-01 exits0:908default jobs,
262TestSuite jobs, final SolKey377/131annotations OK. Actual checkpoint15 runtime
version/KeySort output remains unchanged and retained: Lean4.24.0 commit797c613,
Lake5.0.0-src+797c613, KeySort2jobsPASS. Same supported runtime/config/toolchain.
Final aggregate Lean/Lake RSS1585504KiB, cumulative session peak454889472bytes
(separate from exec RSS), all per-exec OOM deltas0. Final full disk643043328before/
642490368after bytes, enforced12GiB/no-swap/parent16GiB bounds unchanged.
Layers/orphans/trust/strict automatic/complete TestSuite parity/script/diff and
owned421standard pins57modules pass. Global inventory remains FAILexit1 with
0unsafeerrors435unrecorded=14inherited+421owned; additive pin proposals only,
reserved registry untouched. Strict docs still FAILexit1 with exact-base identical
74line72missing/ambiguous raw output; separate no-new comparison PASS. No raw
failure relabeled green, no compiler/EVM execution inferred from kernel checks.
Both final independent source reviewers accepted actual hypotheses, nonvacuity,
controls, scope/ownership and doc without confirmed defects. Artifact review
follows commit/export. Original full queue accounting remains partial/blocked;
further independent refinements are not asserted exhausted. The blocked goal is
not recreated/reset/reactivated/completed, and unavailable goal RPC is not used
as authorization to replace its original frozen assignment.


## Checkpoint seventeen: initial agreement permits nonempty aliased writes

Investigated the original Backfill A/B footprint gap: C16 permits distinct IDs or
empty intervals. No existing pointwise nonempty overwrite identity law was found
in owned modules (only empty identity). New OverwriteAgreement proves list identity
from captured payload reads equal to the INITIAL destination interval under actual
capacity, using replaceSlice_read_cases. Existing memoryOps_heap_ext and intrinsic
typed array/Subtype extensionality lift this to actual whole-heap equality for
primitive/reference arrays; a one-read disagreement refutes identity. No desired
final heap equality or child relation is a premise, no alternate heap/state layer.

BoolTransferAgrees computes its payload from actual calldataBools lookup, comparing
only INITIAL target reads. It is not a supplied payload or conversion certificate.
Successful existing checkedCalldataBools supplies real payload, source bounds and
capacity through boolTransfer_result_lookup; agreement then DERIVES heap identity.
Agreement alone need not validate bounds: every identity/frame result separately
requires actualSome. BoolChildRepr.self_agrees derives same-offset agreement from
its existing immutable decoded child table and initial contents, not a desired
postcondition. Nonempty alias preservation is now a sufficient local case beside
the unchanged distinct/empty cases; changed-payload aliases remain supported.

CalldataAgreementChildren transports BoolChildRepr and RefChildRepr to the ACTUAL
mixed output with per-selected-leaf distinct OR empty OR initial agreement. Uint/
Boolean and primitive/root separation remain intrinsic. Reverse success supplies
its real reached heaps and lengths; checkedReverse_as_forward derives capacities
and invokes EXISTING checkedBoolUintSequence_comm, then reuses the forward result.
There is no second operation interpreter or duplicate commutation implementation.
The existing two-level relation is not generalized to arbitrary recursive graphs,
and no Source/refusal/profile/target predicate or invariant is changed.

Inhabited controls use an OLD child table whose contents are false,true,false.
An ACTUAL nonempty decoded slice1..2 writes the same true value back to its ALIASED
child at offset1. Initial agreement comes from that child table; first heap identity
is proved, not supplied. A second actual uint transfer changes0 to max2^256-1 while
retaining neighbors7,1,0. Complete child/neighbor/root logical IDs and uint outputs,
all valid typed repeated-child indices, and concrete selected index0/32 at n33 are
observed in both actual execution orders. Runtime n has only intrinsic n<2^256,
no new payload/depth cutoff. A reference-valued root overwrite also instantiates
the generic whole-heap identity. One changed Boolean value produces actualSome,
false initial agreement and failed child correspondence for n>0; the old n0 empty-
footprint distinction remains explicit and all earlier counterexamples/pins stay.
These are element observations, not byte encoding or compiler/EVM execution.

Continued independent original allocator/noninterference backfill: agreement is
transported through published Heap.Keeps, then instantiated by actual Heap.alloc
with a supplied reference object. The extended nonempty Boolean step is whole-
heap identity including the new object, the mixed uint step still changes its
old target, and fresh fields retain old IDs. The existing Source table explicitly
has NO entry for that fresh root. No Source entry, fresh address injectivity,
reference constructor or default/allocation-failure compiler is manufactured.

Initial preflight measured640868352bytes free, parent16GiB, idle same supported
child12GiB/swap0, no active Lean workers and ample OS RAM. Conservative checkpoint
growth estimate8MiB (warm outputs/cache3MiB, logs/root/commit2MiB, cumulative export
3MiB) leaves over600MiB; actual growth is checked throughout. No new VFS image,
container/VM/thread, deletion/cache relocation or resource guard/budget expansion.
Per-file diagnostics/get_goal remain unavailable; focused serial-j1 closures use
the same retained runtime. Failed proof attempts and one harmless unknown-session
read poll are separately retained, never inferred successful or repeated unchanged.

Every original queue remains partial/blocked. G32 physical-byte representation,
G33 all-profile constructors/exact target allocation failures, G34 general path/
rebinding/delete/stale-alias execution, G35.01 source/target copying, G35.02 reserved
memory-storage copy, G35.03 general decoded/reference/ABI/Source/storage transport,
G35.04 fresh deep-copy execution, G35.05 full graph/traversal and G35.06 final
V10/Source/target composition remain as previously audited. Backfill A/B get this
additional precise footprint/allocation clause, not full closure or an exhaustion
claim. No new axiom, trust shortcut, exclusion or proof/test budget increase.
Final exact guards, independent reviews/gates and additive artifacts follow.

Checkpoint17 final source reviews: independent read-only finder and skeptic both
pass with no confirmed defects, no Lean/server/builds. Exact guarded focused
closure passes68jobs; final run-lean.sh passes911default/262TestSuite and final
SolKey377taclets/131read-bearing, wrapper exit0. Sampled aggregate Lean/Lake
RSS1516184KiB; cumulative-session cgroup peak454889472bytes is NOT per-exec RSS;
per-exec OOM deltas0, child12GiB/swap0 unchanged. Layers/orphans/trust/strict
automatic/complete fixture/script syntax/corruption tests and whitespace pass.
Owned exact allowlist443pins/60modules passes; proposed additive registrations
remain coordinator-only. Global inventory FAILS exit1,0unsafeerrors457unrecorded
=14inherited+443owned. Global strict docs FAILS exit1; raw74line output is
byte-identical to exact-base evidence (SHA256
ea1a09c222d52d1d17953f653c087443e34e6282497f0b02cdc09aad15b7dd48), separately
zero-new findings PASS. Neither global failure is relabeled green. Final full
gate receipt and raw commands are checkpoint17-checks.json and
v11-checkpoint17-full-01.json in the external evidence directory.

Original queue re-audit after these proofs: G32/G33/G34/G35.01/.03/.04/.05 and
BackfillA/B remain PARTIAL for the specific missing physical-byte, full constructor/
allocation-failure, general paths/rebinding/delete/stale aliases, general decoded/
reference/ABI/Source/storage transport, fresh deep-copy and full graph execution
clauses above. G35.02 remains BLOCKED on reserved memory-to-storage results and
G35.06 on reserved copy plus V10/Source/target composition. The new local interval
agreement and actual allocation application supply additional footprint precision;
they do not close any original parent or prove independent work exhausted.

## Checkpoint18: exact initial-agreement footprint (partial)

Continued original independent BackfillB/G35.03 investigation after checkpoint17:
the sufficient nonempty-alias clause lacked its necessary converse. New owned
OverwriteAgreementExact derives target equality iff INITIAL pointwise payload
agreement from actual overwriteSlice_inside at every runtime index, then lifts
the iff through boolTransfer_result_lookup's REAL payload and success bounds.
Actual Some remains a separate premise: the criterion is not a validity test for
failed calls. Primitive and reference elements use the same intrinsic typed law.

BoolChildRepr.object_eq derives SAME-child contents from two observations of the
SAME immutable table via existing DecodedBoolRead iff, without address injectivity.
Thus actual aliased Boolean-transfer child preservation iff initial computed
agreement; mixed_alias_iff derives the second uint frame intrinsically and keeps
that exact criterion although the final whole heap can materially change. Target
equality is a characterized conclusion, not an assumed preservation input. This
is not a theorem about distinct addresses, arbitrary reference graphs or fresh
Source entries. All Source profiles and aliased operations remain unchanged.

Independent finder/skeptic preliminary reviews found no mathematical defect but
both identified a missing direct mixed-iff control. Addressed with mixed_actual:
for every intrinsic-valid runtime tail n (total child length3+n), BOTH Boolean
values execute followed by an actual uint write0-to-max. Complete child output is
[value,true,false]++replicate n false and uint output[max,7]; uint object inequality
is proved. The resulting child relation iff value=false exercises the new iff
positively and negatively. n0 still has3 real child values, separate from the
checkpoint17 empty-root distinction. Separate runtime accepted/rejected controls
derive actual initial table representation and Some results. No conversion or
output relation is supplied as a premise; no fixed payload/depth cutoff is added.

Focused errors (Option-match reduction, typed list extensionality, runtime length
arithmetic and beta reduction) retain actual exit1 logs, each followed by source
repairs and distinct checks. Exact focused closure passes68jobs; nine headline/
control axiom outputs are standard. Per-file diagnostics/get_goal remain absent.
Retained runtime12GiB/swap0/16GiBparent/serial-j1 and all budgets unchanged. Measured
preflight634470400bytes and conservative3MiB incremental output/log/export budget
leave OS/disk headroom without cleanup, new runtime or sealed-file mutation.
All G32-G35/Backfill statuses and missing source/byte/target/reserved prerequisites
remain as above: no parent completion, independent-exhaustion or EVM result claim.

Checkpoint18 final independent source/doc finder and skeptic reviews both pass
after the direct mixed-control and two documentation fixes above. Exact guarded
focused68jobs and full run-lean.sh912default/262TestSuite/SolKey377/131 pass exit0;
sampled aggregate Lean/Lake RSS1458800KiB, per-exec OOM deltas0. Cumulative session
peak454889472bytes is not per-exec worker RSS. Same12GiB/no-swap/serial runtime and
all existing guards persist. Layers/orphans/trust/owned/script syntax/corruption/
strict automatic/complete fixtures/diff checks pass. Owned452standard pins across
61modules pass. Global inventory still FAILS exit1,0unsafeerrors466unrecorded
=14inherited+452owned. Strict docs still FAILS exit1, raw output byte-identical to
exact base (ea1a09c222d52d1d17953f653c087443e34e6282497f0b02cdc09aad15b7dd48);
zero-new comparison separately passes. Proposals, raw failed attempts, gates and
resource receipts stay in NEW checkpoint18 evidence, no reserved records edited.

Original queue audit remains unchanged after this second independent checkpoint:
G32/G33/G34/G35.01/.03/.04/.05 and BackfillA/B PARTIAL; G35.02 and G35.06 BLOCKED
on reserved copy and final V10/Source/target prerequisites. All exact missing
physical representation/all-type constructor/target failures/general path/delete/
rebinding/reference ABI/fresh-copy/general graph/composition clauses remain open.
This local exact iff is not full lane completion or independent-work exhaustion.

## Checkpoint19: overlapping two-write restoration (partial)

Original G35.03/.04 and BackfillA/B investigation confirmed that existing sequence
read/last-write and disjoint commutation laws did not characterize final INITIAL
footprint restoration when the first operation breaks correspondence. New owned
OverwriteRestoration defines LastWriteAgrees purely on initial contents and two
captured payloads: ALL second-written cells equal their original cells; only FIRST
cells outside the second destination equal their original cells. Existing read_cases
derives necessity/sufficiency for list, actual typed target and whole heap under
actual capacities. Second capacity follows length preservation. Primitive/reference
elements, arbitrary overlap, empty/touching intervals and runtime lengths use the
same intrinsic definitions. Existing arbitrary typed MPath observations follow the
proved heap identity. No stagewise agreement, final equality or final relation is
a premise; no alternative state/evaluator/semantics or admission cutoff is added.

CalldataRestoration reconstructs both REAL payloads, both source bounds and reached
heaps from existing checkedBoolSequence success plus boolTransfer_result_lookup;
the second capacity is derived back to the actual initial runtime length. Its
computed BoolSequenceRestores predicate reads the immutable tables, not caller-
supplied values or conversion proofs. Target/wholeheap iff and initial immutable
BoolChildRepr final restoration require no mid-heap correspondence. RefChildRepr
frames the root and permits selected repeated old aliases when either separate or
restored by this computed criterion. This is an existing two-level footprint clause,
not arbitrary fresh/recursive Source graph or compiler correctness.

Actual controls admit independently arbitrary child tail n and root alias count m
under only existing intrinsic lengths n+3<2^256 and m<2^256. First nonempty payload
[false,false] at0 changes child [false,true,false]++nfalse to [false,false,false]++nfalse
and refutes initial child correspondence. Second nonempty payload [true,false] at1
partially overlaps and restores it. The criterion is discharged against INITIAL
reads and then directly derives wholeheap identity and final child/root relations;
actual secondSome is linked to the actual first output. Complete intermediate/final
child/neighbor/rootID vectors, every valid typed repeated-root index and concrete
nonempty m33 indices0/32 are observed. n0 remains child length3, while m0 explicitly
has no selected leaf. Wrong second payload and incomplete repair separately refute
the SECOND-cell and FIRST-survivor halves; reversed order gives a different actual
final heap. Empty exact-end and touching calls execute. A reference-valued root-slot
write changes an old child ID to a neighbor and restores it by the same generic law.

Ordered failure controls record successful firstSome followed by missing second
lookup, reversed source, source overrun or destination overrun, and actual sequence
None for each. Missing-first lookup short-circuits separately. Finder and skeptic
both identified that source[0,3) at destination1 also overran at n0; fixed destination
to0 in BOTH stage/sequence observations. Explicit isolated_guards now proves source-
only valid destination at every n, reverse-only remaining bounds, and destination-
only valid source slice against the REAL reached length. None is no rollback/halt
claim. All earlier fixtures/pins and admitted shapes remain unchanged.

The preceding automatic approval-service capacity failure did not execute its
repair; one authorized recovery succeeded on the SAME model/thread/VM/policy.
Retained proof failures include controls01-04; each received an actual source
repair and distinct check. controls05 passed before independent isolation review;
refined controls06 passes71jobs with all26 new public theorem/control axiom outputs
standard. Exact guarded checks/final gates/reviews follow. Per-file MCP/get_goal
remain unavailable; existing blocked goal unchanged, no create/reset/reactivation.
Same retained capped runtime, warm outputs, writer lock, serial-j1/LEAN_NUM_THREADS1,
12GiB/no child swap under16GiBparent and all proof/time/fuel/node/TestSuite budgets
remain unchanged. Disk forecast8MiB includes outputs/logs/compact exports; actual
growth is measured throughout. No cleanup/cache relocation/new container/capacity.

Every original G32-G35/Backfill parent remains partial/blocked, with the original
physical-byte, all-type/default/target failure, path/rebinding/delete execution,
general decoded/reference/ABI/Source/storage, fresh deep-copy, unrestricted graph,
reserved copy and V10/Source/target composition obligations still open. These
logical intrinsic proofs are not compiler/EVM testing or independent-work exhaustion.

Checkpoint19 final independent source/doc finder and skeptic reviews PASS after
the isolated-source fix and explicit other-guard observations. Guarded focused71
and final run-lean.sh915default/262TestSuite/SolKey377/131 exit0. Fresh actual Lean
4.24.0(797c613)/Lake5.0.0-src+797c613 and KeySort2jobs exit0 observed. Full-gate
sampled aggregate Lean/Lake RSS1503380KiB,0OOMevent deltas; cumulative session
cgroup peak454889472bytes is NOT per-exec worker RSS. Retained child12GiB/swap0,
parent16GiB, hostswap0 and all guards unchanged. Layers/orphans/trust/strict
automatic/complete fixtures/script syntax/corruption/diff pass; owned478standard
pins64modules pass. Raw global inventory FAILS exit1,0unsafeerrors492unrecorded
=14inherited+478owned. Raw global strict docs FAILS exit1 with exact-base byte-
identical complete output SHA256
ea1a09c222d52d1d17953f653c087443e34e6282497f0b02cdc09aad15b7dd48; separately
zeroNEWfindings PASS. Reserved global inventory/ledger/manifest remain untouched.
All original queue statuses remain partial/blocked; no entire-assignment or
independent-exhaustion claim follows. Precise new pin proposals and full commands
are in external checkpoint19 evidence and additive artifact handoff.

## Checkpoint20: actual heap-source recapture restoration (partial)

Continued distinct original G35.04/BackfillA/B work after checkpoint19: decoded
source tables are immutable, but an actual memory snapshot's second payload can
change after the first write. Existing captureTwice provided ordered reads and
sufficient noninterference/commutation, not this exact restoration application.
New owned RecaptureRestoration applies checkpoint19 overwriteIntervals_eq_self_iff
to the existing actual captureTwice with p=sliceElems(initial) and q=sliceElems
(actual captureOverwrite intermediate). Initial source/destination bounds remain explicit premises; slice lengths derive
both payload capacities and length preservation transports the second source
bounds/capacity to the intermediate. No desired payload equality or final relation
is assumed. recapturedPayload_read derives each q read from INITIAL
source cells via the existing first-write read_cases, allowing recapture inside
the first destination. Actual checked Some(initial) iff the same computed criterion
requires explicit valid source/destination bounds, not a successful-poststate
premise. No second operation interpreter or replacement copy semantics is added.

For every intrinsic-valid runtime tail n, initial [true,false,false]++nfalse becomes
[true,true,false]++nfalse after actual source0..1→destination1; old child-table
correspondence is false there. Actual second snapshot captures intermediate1..3
as [true,false] and writes at0, restoring the full initial heap and old child
representation. Its corresponding INITIAL source slice is [false,false]. Freezing
that source produces complete [false,false,false]++nfalse and a different final
heap, refuting a substituted original-snapshot implementation. Controls include
actual firstSome, reached secondSome and actual composedSome(initial); full
intermediate/final child and neighbor vectors. Both initial-source branches of
recapturedPayload_read are directly instantiated at selected indices0/1. Runtime
n0 still has3 nonempty elements, and n+3<2^256 is only existing intrinsic object
validity. Generic laws cover primitive/reference elements without payload/depth
cutoff. Existing earlier reference/fixed/alias/bounds/empty fixtures stay intact.

Separate preliminary finder/skeptic reviews found no mathematical defect and
requested explicit reached-second, full frozen/final vectors and direct both-
branch controls; all supplied and focused72jobs pass, eight public axiom outputs
standard. New exact guards/final checks/reviews follow. The same retained capped
runtime, serial-j1/LEAN_NUM_THREADS1, fixed budgets, writer lock and keyed outputs
remain; conservative measured4MiB incremental disk forecast leaves ample headroom
without cleanup/new runtime/capacity change. No Source entry/decoder/exclusion,
fresh/deep copy, ABI/compiler/EVM or arbitrary graph claim. All original queues
and missing physical-byte/target/default/path/source/reserved prerequisites remain
partial/blocked, with no assertion that independent assigned work is exhausted.

Checkpoint20 final separate independent source/doc finder and skeptic PASS, with
all requested control/bounds-wording refinements verified. Guarded72jobs and
final full run-lean.sh916default/262TestSuite/SolKey377/131 exit0. Fresh actual
Lean4.24.0(797c613)/Lake5.0.0-src+797c613 and KeySort2jobs pass. Aggregate sampled
Lean/Lake RSS1471952KiB, per-exec OOM deltas0; cumulative session peak454889472bytes
is not per-exec RSS. Retained12GiB/no childswap, parent16GiB/hostswap0, serial-j1
and all original limits unchanged. Layers/orphans/trust/strictautomatic/complete
fixtures/script syntax/corruption/diff PASS. Owned486standard pins65modules PASS.
Raw global inventory FAIL exit1,0unsafeerrors500unrecorded=14inherited+486owned.
Raw strict docs FAIL exit1, complete output byte-identical to exactbase
ea1a09c222d52d1d17953f653c087443e34e6282497f0b02cdc09aad15b7dd48; separately
zeroNEWfindings PASS. No reserved inventory/ledger/manifest edited.

Original queue re-audit: G32/G33/G34/G35.01/.03/.04/.05 and BackfillA/B stay PARTIAL;
G35.02/.06 BLOCKED on reserved copying and final V10/Source/target prerequisites.
Intrinsic same-object snapshots and local restoration now cover changed intermediate
recapture too, but physical byte representation, all-profile/default/target failure,
general path/delete/rebinding execution, general decoded/reference/ABI/Source/storage
transport, fresh deep-copy, arbitrary Source graph/emitted traversal and full final
composition remain open. Further original independent clauses are not declared
exhausted. Existing persistent goal remains unchanged and unfinished; no integration.

## Checkpoint21: finite runtime snapshot schedules and provenance (partial)

Original G35.04/BackfillA-B investigation confirmed existing captureTwice and
checkedCaptureSequence cover exactly two calls. New owned SnapshotSchedule uses
List/Option composition of EXISTING checkedCaptureOverwrite at each ACTUAL reached
heap, on one existing intrinsically typed array/ref. SnapshotArgs abbreviates the
existing Nat(start,stop,destination) tuple only: no AST/opcode/IR, value, state,
copy evaluator or Source semantics is added. No public schedule length cap or
fresh/deep-copy assumption. CapturesValid checks every original source/destination
bound, independent of run/restoration. All actual typed array lengths survive, so
those bounds derive success at each intermediate; success iff the input bounds.
Exact None identifies the FIRST invalid reached call after a real successful
prefix; an equivalent original-bounds prefix theorem derives that actual heap.
No suffix heap or halt/rollback behavior is invented. Actual arbitrary reached
steps, all-other-object frames, append/Option associativity and singleton laws
are proved. runCaptures_two recovers existing checkedCaptureSequence exactly,
including failures, rather than replacing/weakening the old two-step APIs.

SnapshotProvenance defines observation-only backwards index data: map the last
destination cell to its prior source, then recursively through earlier calls;
exterior indices stay unchanged. It does not evaluate values/heaps. The actual
successful run reads INITIAL elements at this computed index, for every Nat
index, with valid-index preservation and out-of-bounds exterior identity. Target
and wholeheap restoration iff computed INITIAL reads agree, NOT provenance-index
identity or supplied final equality/relation. BoolChildRepr final correspondence
has the same iff from its independently inhabited initial immutable child table,
with no stagewise representation or payload equality assumption.

Runtime restoreCycles constructs input lists of length2*copies for every Nat
copies; bounds and provenance derive actual success/restoration. Object tail n
has only intrinsic total length n+3<2^256. C20 actual first-step witnesses are
reused: [true,false,false]++nfalse -> [true,true,false]++nfalse (initial child
representation false), actual recapture repairs it. Whole initial heap and old
child table are restored for arbitrarily many cycles; this is not an assumed
run relation. cycle_origin maps1to2, demonstrating restored CONTENTS do not require
identity provenance. Three material writes additionally produce ordered vectors
[T,F,F] -> [T,T,F] -> [T,F,F] -> [F,F,F], with runtime tails/neighbors retained.
Reversed order and frozen-initial-source alternatives give complete wrong vectors;
the frozen negative is recovered from the existing checked two-step instance.
Empty/singleton, exact-end empty and touching destinations execute. A successful
three-step changed prefix reaches a genuine heap before an invalid destination
and supplied suffix; None exposes no suffix heap. Earlier failed proofs retained.

Dynamic AND fixed reference-valued arrays run the SAME schedule adapter at every
copy count. Initial old refs [left,right,right] become [left,left,right] before
actual recapture restores them. Complete old-ID vectors and distinct child content
vectors are observed at intermediate/final heaps; both children framed. Fixed
length3 witnesses close generic ArrTy coverage without implementing a constructor.
Runtime dynamic tails and concrete n33/index32 selections retain old identities;
these are element indices, not byte encoding. Repeated old aliases are supported,
with no address/hash-injectivity, fresh Source table or full graph-copy claim.

Separate independent read-only finder/skeptic preliminary/refined source reviews
found no mathematical/ownership defect. Planned nonprimitive/fixed validation was
supplied and accepted. Focused refinements fixed empty-proof syntax, capacity
projection arithmetic, membership/tuple normalization, endpoint reflexivity and
fixed-length reduction; raw exit1 attempts remain. Refined combined closure76jobs
passes with43 standard public theorem/control axiom outputs, now exactly guarded.
Per-file Lean MCP/get_goal unavailable; existing blocked persistent goal unchanged.
Writer lock, existing retained12GiB/no-child-swap runtime under16GiBparent/hostswap0,
serial-j1/LEAN_NUM_THREADS1, proof/fuel/node/TestSuite/time guards and keyed warm
outputs stay unchanged. No new runtime/image/cachecopy/cleanup/capacity change.
Conservative measured12MiB output/log/export forecast is checked throughout.

All original G32-G35 and Backfill parents remain partial/blocked: finite intrinsic
operation composition is NOT recursive Source graph traversal, emitted loops,
fresh/deep-copy execution, physical bytes, all-profile defaults/target failures,
general path/delete/rebinding or general ABI/reference/storage/Source transport.
Reserved memory-to-storage and V10/Source/target composition stay open. No parent
or goal completion or exhaustion of independent original clauses is claimed.

Checkpoint21 final separate independent source/doc reviews PASS. Guarded focused76
and unchanged full run-lean.sh920default/262TestSuite/SolKey377/131 exit0. Fresh
actual Lean4.24.0(797c613)/Lake5.0.0-src+797c613 and KeySort2jobs PASS. Sampled
aggregate Lean/Lake RSS1458972KiB,0OOMevent deltas; cumulative session cgroup
peak458653696bytes is NOT per-exec worker RSS. Same12GiB/no childswap,16GiBparent/
hostswap0, serial-j1 and original guards persist. Layers/orphans/trust/strict
automatic/complete fixtures/script syntax/corruption/diff PASS. Owned529standard
pins69modules PASS. Raw global inventory FAIL exit1,0unsafeerrors543unrecorded
=14inherited+529owned. Raw strict docs FAIL exit1, complete output byte-identical
to exactbase ea1a09c222d52d1d17953f653c087443e34e6282497f0b02cdc09aad15b7dd48;
zeroNEWcomparison separately PASS. Exact additive owned proposals are external
evidence only; no reserved global inventory/ledger/manifest changed.

Original queue re-audit: G32/G33/G34/G35.01/.03/.04/.05 and BackfillA/B remain PARTIAL;
G35.02/.06 BLOCKED on reserved copy/final V10-Source-target prerequisites. Arbitrary
finite same-object intrinsic schedules now have full provenance, bounds and local
restoration laws; this does not supply physical bytes/all-profile default/target
failures/general paths/delete/rebinding/general ABI-reference-storage-Source/fresh
deep-copy/recursive Source graph or emitted-loop correctness. Further original
operation/growth/application clauses are not declared exhausted. Persistent goal
unchanged/unfinished; no integration.

## Checkpoint22: finite-schedule growth and actual interstage allocation (partial)

Continued independently justified original G33/G35.04/BackfillA-B application
after checkpoint21: existing checked-step Keeps proves growth, but no finite
schedule extension/application existed. New SnapshotScheduleGrowth derives actual
run success and final Keeps through arbitrary finite schedules by the published
checkedCaptureOverwrite_keeps at each REAL changed intermediate. Initial prefix
Keeps is explicit, independent of run/restoration; actual Heap.alloc discharges
it. None transports iff because original bounds use preserved lengths. Actual
allocation after a successful arbitrary prefix derives its reached heap from
runCaptures_split_some, then transports the arbitrary remaining tail. No desired
final preservation, frozen payloads or mid-representation are assumed. Fresh
object own fields frame by actual old_ne_fresh and runCaptures_frame; this is
not a proof of deep referenced-child liveness or an allocation constructor.

Primitive runtime control performs a meaningful first write, proves its immutable
child-table representation FALSE, actually allocates supplied parent[r,r] on that
reached heap, then repair ++ restoreCycles(copies) ++ repair for arbitrary Nat
copies. Full initial/mid/final child vectors are inherited from actual checked
instances; old child ends[F,F,F]++nfalse while new parent's old-ID fields0,0 and
neighbor[F,T] frame. Fresh-vs-old separation and NO Source entry for the fresh
root are explicit. This uses Heap.alloc with supplied MObj only, not reference
construction/default/compiler/target-failure implementations.

Finder requested explicit allocated failure prefix and broken-mid relation; both
supplied. allocated_failure now returns actual allocated three-step prefixSome,
its reached invalid destination callNone and full sequenceNone, with no suffix
heap/rollback. Skeptic requested nonprimitive weakening: reference_allocated runs
actual allocated arbitrary runtime cycles plus actual first-copy control. Full
weakened old reference vectors change[left,right,right] to[left,left,right] at
firstOut and restore in the full run; new parent fields retain old root IDs2,2
at both outputs; distinct old child content vectors frame. For copies1, literal
checked secondSome is linked to the ACTUAL firstOut. Nontrivial HRef weakening,
recapture and own-fields versus child-content boundaries are independently
inhabited, not assumed output relations or fresh Source representations.

Separate independent read-only finder/skeptic refined reviews accept all controls
with no mathematical/ownership defect. Focused03 passes77jobs, all7public outputs
standard; exact guards/final checks follow. Raw failed02 attempt retained (private
fixture rewrite matching and Lean reserved identifier), actual source repaired.
Same existing capped serial runtime, warm outputs, writer lock and all budgets;
measured4MiB small-module/log/compact-export forecast, no new runtime/cache copies/
cleanup/capacity change. Every original queue remains partial/blocked and all
physical-byte/all-profile default/target failure/general path-delete-rebinding/
ABI-reference-storage-Source/fresh deep-copy/recursive graph/reserved-copy/final
V10-Source-target obligations stay open. No exhaustion or whole-lane claim.

Checkpoint22 final independent source/doc finder/skeptic PASS after explicit
allocated-prefix/midnegative/nonprimitive-weakening controls. Guarded77jobs and
unchanged full run-lean.sh921default/262TestSuite/SolKey377/131 exit0. Fresh actual
Lean4.24.0(797c613)/Lake5.0.0-src+797c613 and KeySort2jobs PASS. Aggregate sampled
Lean/Lake RSS1779724KiB; per-exec OOM deltas0; cumulative whole-session
cgroup peak2160848896bytes is not per-exec RSS. Same12GiB/no childswap under16GiB
parent/hostswap0, serial-j1 and all proof/time/fuel/node/TestSuite guards unchanged.
Layers/orphans/trust/strictautomatic/complete fixtures/script syntax/corruption/diff
PASS. Owned536standard pins70modules PASS. Raw global inventory FAIL exit1,0unsafe
errors550unrecorded=14inherited+536owned. Strict docs FAIL exit1, complete findings
byte-identical to exactbase ea1a09c222d52d1d17953f653c087443e34e6282497f0b02cdc09aad15b7dd48;
zeroNEWcomparison separately PASS. Reserved global records untouched.

As requested, supported optional artifact cache is now OFF in the UNTRACKED runtime
TOML; original enabled config snapshot retained in new evidence, old sealed runtime
configs unchanged. Warm regular .olean files reused and all caches/toolchains kept
in place, no copying/cleanup. Cache-off final gate produced ~24MiB additional build/
link output, exceeding the initial4MiB small-module forecast; raw disk receipts
retain this measured overrun. No capacity/guard/budget change; measured remaining
~587MB supports compact additive export. Actual export headroom is recorded before
writes. All original queues remain PARTIAL/BLOCKED, including physical bytes/all-
profile defaults/target failures/general paths/delete/rebinding/ABI-reference-
storage-Source/fresh deep-copy/recursive graph/reserved copy/final V10-target
composition. Neither independent exhaustion nor full goal completion is claimed.


## Checkpoint twenty-three: decoded initialization and finite recapture

Source scan reproduced the missing application: `runCaptures` appeared only in
schedule/provenance/growth/control modules; decoded compositions handled two
writes or Bool/uint, not a decoded transfer followed by an arbitrary runtime
schedule. New owned `CalldataSchedule` composes the EXISTING
`checkedCalldataBools` and `runCaptures` by Option.bind at the ACTUAL intermediate.
No payload/conversion proof, output relation, stagewise correspondence, AST,
interpreter, decoder or Source profile change is an operation input.

`checkedBoolCaptures_some` exposes both actual reached calls;
`checkedBoolCaptures_success` derives schedule validity against ORIGINAL length
using the real transfer's all-object length law. Initial decoded failure is
classified by existing `boolTransfer_none_lookup` (missing/unsupported table,
reversed slice/source/destination overflow); `checkedBoolCaptures_none` exposes
that initial failure OR actual decoded Some followed by a real successful prefix
and its first reached failed call, with no suffix heap/rollback assertion.
`checkedBoolCaptures_read` extracts the actual immutable table payload and proves
ALL final reads are initial replaceSlice reads at captureOrigin;
`checkedBoolCaptures_source_read` connects origins inside the decoded footprint
to exact published DecodedArrayRead observations. All-array lengths and unrelated
typed objects are framed. `checkedBoolCaptures_restore` and
`BoolChildRepr.calldata_schedule_iff` give exact INITIAL-value criteria, not
final heap/representation premises; an INITIAL old child table relation is
explicit only in the child theorem.

Controls execute decoded [true] into old [true,false,false] plus arbitrary
runtime tail, giving [true,true,false] and FALSE old correspondence; actual
recapture [1,3) to0 repairs the child, followed by arbitrarily many real restoring
cycles. They retain complete initial/intermediate/final/neighbor vectors and IDs,
independently prove the initial extraction/provenance criterion (without using a
run or desired final relation), then apply its sufficiency. New full-read and
exact immutable-source-read laws are directly exercised. Successful ignored-
repair gives a wrong vector and false initial criterion; frozen INITIAL payload
substitution separately gives a wrong vector distinct from actual recapture;
missing/reversed/source-overrun/destination-overrun initial failures, successful
nonempty prefix before later invalid call, empty/exact-end, and element32 controls
remain explicit. Earlier fixed/reference-valued, boundary, wrong-order and alias
fixtures remain unchanged and checked; this Boolean composition does not claim a
new general reference conversion.

Independent source finder and skeptic both requested replacing a criterion
roundtrip with an INITIAL-only proof and adding successful nonrestoration and
direct new-read controls. These findings were repaired. Focused failed attempts
are retained separately; exact standard axiom guards and final gates recorded in
the new checkpoint23 evidence. All original G32/G33/G34/G35.01-.06 and Backfill A/B
parents remain PARTIAL/BLOCKED; no exhaustion/full-lane claim. Physical bytes,
all-profile defaults/target allocation failures, general path/rebinding/delete,
general ABI/reference/storage transport, fresh deep-copy, recursive Source graphs,
reserved memory-to-storage and final Source/V10/target composition stay open.

Runtime preflight recorded585322496 available bytes and40MiB conservative growth
allowance based on previous24182784-byte gate growth plus modules/logs/export;
residual stayed above512MiB. Same existing runtime/cache, optional artifact cache
OFF, child12GiB/no-swap under16GiB parent and serial Lean-j1/LEAN_NUM_THREADS=1;
no proof/time/test/resource budget increase or deletion/relocation. Per-file MCP
and get_goal unavailable; focused serial closures used, existing goal unchanged.

Final source finder accepted all refinements; skeptic accepted proofs/controls
and requested the frozen-negative wording above be distinguished from the false
criterion for the actual ignored-repair operation; wording corrected. Final
bounded wrapper passed:923 default jobs /262 TestSuite /SolKey377 taclets and131
read-bearing, exit0. Full gate resource receipt retains actual sampled aggregate
Lean/Lake RSS and cumulative session peak separately, with zero OOM events.
22 new guarded public laws/controls give558 standard-only owned pins across72
modules. Raw strict docs and global inventory outcomes are retained separately
from complete exact-base no-new comparison and owned additive-pin validation.

Actual final checks: layers/orphans/trust/lane/strict automatic/complete fixtures/
script syntax and corruption controls PASS. Global docs FAIL exit1, complete
exact-base findings byte-identical (separate zeroNEW PASS); global inventory FAIL
exit1,0unsafeerrors572unrecorded=14inherited+558owned. Additive owned registration
proposal exported for coordinator reconciliation, reserved records untouched.
Final sampled aggregate Lean/Lake RSS1549648KiB, cumulative session cgroup peak
2160848896bytes,0OOMevents. Full gate incremental disk184320bytes, safely below
40MiB preflight allowance; actual runtime Lean4.24.0/Lake5.0.0-src+797c613 and
KeySort2jobs PASS. No external compiler/EVM evidence inferred from kernel/SolKey.

Original-queue reassessment: G32 still lacks the reserved physical-byte bridge;
G33 supplied/default/multi-object intrinsic growth adapters do not establish
all-profile construction/target failure/stack-tail execution. G34 typed path and
local alias laws do not implement general source-to-target rebinding/delete.
G35.01 consumes published map-free intrinsic storage-tree copying/Mirrors but
lacks source/target/liveness realization; G35.02 remains reserved/unpublished.
G35.03 now supplies actual decoded Boolean initialization plus arbitrary finite
memory recapture, but not general reference/ABI/calldata-to-storage conversion.
G35.04 finite actual shallow snapshot scheduling does not implement fresh deep
copy or emitted loops. G35.05 finite map-free Mirrors and index traversal do not
close recursive Source graphs/maps/shadows/cycles/emitted traversal. G35.06
reserved-copy/V10/Source/target composition stays blocked. Backfill A/B advanced,
not complete or exhausted. Further owned primitive-family or preserving-context
applications may remain; this checkpoint makes no independent-exhaustion claim.


## Checkpoint twenty-four: decoded schedules in actual allocated contexts

After checkpoint23, source inspection confirmed its new decoded-initialized
schedule had no preserving-context/interstage-allocator application. Existing
finite schedule growth and decoded-write Keeps were separate. Owned new
`CalldataScheduleGrowth` composes those EXISTING laws at the actual reached mid.
`checkedBoolCaptures_keeps` transports actual decoded Some and arbitrary finite
actual recaptures through explicit independent INITIAL Keeps, deriving final
Keeps. `checkedBoolCaptures_none_keeps` proves identical rejection through that
context, with an explicit existing DecodedArrayAt certificate; it does NOT claim
to handle missing/unsupported source objects under that certificate. Original
missing-object adapter rejection remains covered by checkpoint23. No final
preservation, payload conversion, representation or address-injectivity premise
is smuggled into either statement.

`checkedBoolCaptures_interstage_alloc` needs only actual composition Some and a
supplied intrinsic MObj. It extracts the REAL decoded output, invokes published
Heap.alloc on that output, transports the arbitrary reached-heap tail through
Heap.keeps_alloc and derives final Keeps/fresh own-field framing. No allocator,
reference constructor, Source table entry or second copy semantics is defined.

Inhabited arbitrary n/copies controls execute initial TFF runtime-tail heap ->
decodedTTF with false old child representation ->actual allocation of parent
[r,r] on that changed mid ->recapture TFF and arbitrary restoring cycles. They
observe complete child/neighbor vectors, fresh parent IDs[0,0] and old/fresh root
inequality. A separate actual INITIAL allocation directly exercises the new
positive composition Keeps theorem, with final Keeps, complete vectors and fresh
own fields. Rejection control exposes actual allocated decoded Some, nonempty
repair-prefix Some, reached invalid-step None and full None. These were required
by BOTH independent source reviewers and added before final review. New exact
standard-only guards cover all six public laws/controls. Earlier failed map/
weakening diagnostics remain retained; no failed elaboration is a deliverable.

Fresh parent fields retaining old child identities do not establish deep child
liveness. No Source/ABI/compiler/EVM behavior, physical bytes, all-profile default
construction or target allocation failure follows. Original G32/G33/G34/G35.01-
.06/Backfill A-B remain PARTIAL/BLOCKED; upstream/reserved proofs and raw mandatory
global failures remain open. Original queue reassessment in checkpoint23 remains
applicable; this is another actual context application, not an exhaustion claim.

Preflight measured581980160 available bytes;32MiB allowance uses prior24182784-
byte gate plus8MiB modules/logs/export, residual above512MiB. Same existing capped
runtime, optional artifact cache OFF, child12GiB/no-swap, serial Lean-j1 and
LEAN_NUM_THREADS1; all files/caches/seals/proof/test/time budgets preserved.

Final independent read-only finder and skeptic both accepted the refined source
and document: initial-allocation positive uses the NEW composition theorem;
allocated rejection exposes all reached stages; no outstanding source finding.
Actual guarded closure80jobs and full wrapper924default/262TestSuite/SolKey377
and131read-bearing PASS exit0. Strict/layers/orphans/trust/complete fixtures/
script syntax/corruption controls PASS;564standard-only pins across73modules.
Raw global docs FAIL1 with complete exact-base byte equality (separate noNEW
PASS); raw global inventory FAIL1,578unrecorded=14inherited+564owned,0unsafeerrors.
Proposals remain additive for coordinator reconciliation, reserved records intact.
Actual Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs PASS. Full sampled aggregate
Lean/Lake RSS1599592KiB, cumulative session cgroup peak2160848896bytes,0OOMevents;
full disk increment192512bytes, safely within32MiB allowance. All original queues
remain partial/blocked with the exact prerequisites enumerated above, no claim
that all independent work is exhausted or the frozen assignment is completed.


## Checkpoint twenty-five: actual decoded uint256 finite schedules

Reproduced missing family: owned `runCaptures` composition existed for Boolean
initialization, not uint256, despite published checkedCalldataUints extraction/
read/length/frame/Keeps and generic typed SnapshotSchedule/Provenance. New owned
CalldataUintSchedule, CalldataUintScheduleGrowth and controls reuse those EXISTING
operations and proofs. No evaluator, decoder, AST/IR, heap/value semantics,
payload input, conversion-correctness or desired postrelation is introduced.

`checkedUintCaptures` is actual checkedCalldataUints.bind runCaptures at its REAL
output. `checkedUintCaptures_some` exposes reached heaps; success is derived from
actual transfer and ORIGINAL lengths; `checkedUintCaptures_success_lookup`
further gives EXACT actual calldataUints lookup plus source/destination bounds
and CapturesValid on ORIGINAL length. `checkedUintCaptures_none` distinguishes
initial rejection from actual decoded Some, successful prefix and first reached
failed call; underlying uintTransfer_none_lookup classifies missing/unsupported
objects and independent reversed/source/destination guards. No suffix heap or
Source halt/rollback is claimed. ALL final reads use actual extracted payload
and captureOrigin; interior provenance produces published DecodedArrayRead with
sourceUint and exact uint range, not a guessed encoding. Whole-heap restoration
iff compares computed INITIAL values; lengths and other typed objects frame.

Growth success/rejection require independent INITIAL Keeps and actual existing
DecodedArrayAt certificate; rejection under that certificate does not cover a
missing decoded table. Actual interstage allocation needs only successful actual
composition and a supplied existing MObj, allocates on REAL changed decoded mid,
and derives final Keeps plus fresh own-field frame. Fresh parent fields retaining
old aliases do not establish deep-child liveness or fresh Source representation.

Controls derive immutable uint input representation from existing uints/uint_repr.
Initial [7,8,8] plus arbitrary maximum-word tail ->actual decoded[9] at index1 ->
[7,9,8] ->actual index2-to1 recapture ->[7,8,8], with arbitrary runtime repetitions
and no schedule/payload cap. An INITIAL-only payload/provenance proof discharges
exact restoration, then the actual run is reconstructed from input bounds. Both
dynamic and supported fixed arrays expose actual decoded Some, reached schedule
Some and complete contents. Neighbors retain [maximum,0,1]; reference-containing
parent fields retain repeated root IDs[0,0]. Explicit maximum contents/read/value
2^256-1 rule out accidental truncation; element32 is an element observation only.

The restoring fixture reads UNCHANGED index2, so cannot distinguish frozen input
from reached input. Separate changed-source recapture reads decoded index1 into0,
giving actual[9,9,8]; substituting frozen initial8 gives[8,9,8], proved unequal,
with full actual neighbor/parent observations. Skipped repair is actual Some with
wrong[7,9,8]. Empty/exact-end, independent missing/unsupported/reversed/source/
destination failures and actual decodedSome/nonemptyrepairprefixSome/reachedbad
None/fullNone remain explicit. Actual interstage and initial allocation controls
observe fresh fields[0,1,0]/old-fresh inequality/full child-neighbor vectors;
allocated rejection exposes each actual reached stage. Both independent source
reviewers requested direct initial-allocation success/rejection and explicit
maximum; those controls were added. Exact guards cover all33public laws/controls.

Preflight579198976 available bytes,32MiB allowance based on prior24182784-byte
cache-off gate plus8MiB source/log/export, residual above512MiB. Existing runtime,
child12GiB/no-swap under16GiB parent, Lean-j1/LEAN_NUM_THREADS1, warm keyed outputs
preserved. Optional cache OFF in TOML AND actual exec environment LAKE_CACHE_DIR
empty/LAKE_ARTIFACT_CACHE=false (tested/recorded); no cleanup/relocation/image copy.
Per-file Lean MCP/get_goal unavailable; serial focused closure used, goal unchanged.
Earlier failed focused diagnostics retained; no sorryAx deliverable or budget rise.

Original G32/G33/G34/G35.01-.06 and Backfill A/B remain PARTIAL/BLOCKED. This adds
one published primitive family, not general Source/ABI/reference/storage/physical
bytes/fresh deep-copy/compiler semantics. All-profile defaults/target failures,
general path/rebinding/delete, recursive Source graph, reserved memory-to-storage
and final V10/Source/target composition remain named open. No independent-work
exhaustion, lane completion or compiler/EVM test result is inferred.

Final independent read-only finder and skeptic accepted all refined source/doc
and33exact guards, actual initial-allocation success and reached failure controls,
explicit maximum and discriminating changed-source negative. No outstanding
source finding. Actual guarded80jobs and final wrapper927default/262TestSuite/
SolKey377taclets131read-bearing PASS exit0. Strict/layer/orphan/trust/complete
fixtures/script syntax/corruption controls PASS;597standard-only pins76modules.
Raw global docs FAIL1, complete raw findings byte-identical to exact base (separate
zeroNEW PASS); inventory FAIL1,611unrecorded=14inherited+597owned,0unsafeerrors.
Reserved global records untouched; precise additive proposals exported.

Runtime Lean4.24.0/Lake5.0.0-src+797c613 and KeySort2jobs actual PASS. Initial
versions attempt could not acquire nonblocking writer lock while serial script
checks were still running (exit1, helper not launched); retained receipt, waited
for checks then uniquely named runtime02 passed. No active gate was interrupted.
Final full sampled aggregate Lean/Lake RSS1437488KiB, cumulative session cgroup
peak2160848896bytes,zeroOOMevents; disk increment192512bytes, within32MiB forecast.
Explicit cache-off exec environment propagated in focused/full/runtime commands.

Original queue reassessment: published typed schedule/uint transfer now compose
with actual immutable inputs/context/allocation; this remains primitive-family
operation evidence. G32 physical bytes, G33 all-profile constructors/target
allocation failure, G34 general path/rebinding/delete target execution, G35.01
full storage/source/target realization, G35.02 reserved memory-storage prerequisite,
G35.03 general ABI/reference/calldata-storage transport, G35.04 fresh deep-copy/
emitted-loop execution, G35.05 recursive Source graph/maps/shadows/cycles traversal,
and G35.06 final V10/Source/target composition remain open. Backfill A/B advanced
but not complete or exhausted. No full-lane closure or external compiler/EVM
result is inferred. Existing blocked goal preserved unchanged/uncompleted.


## Checkpoint twenty-six: mixed decoded initialization and two finite schedules

Reproduced concrete missing application: MixedCalldataSequence had actual Bool/
uint decoded operations and component finite schedules existed separately, but
no mixed initializer followed by arbitrary reached-heap schedules on BOTH typed
destinations. New owned MixedCalldataSchedules composes EXISTING
checkedBoolUintSequence.bind runCaptures(Bool).bind runCaptures(uint), never a new
AST/IR/interpreter, copy evaluator, value/heap semantics or decoder. Both refs
have distinct LOGICAL IDs by published bool_uint_transfer_ne; no same-ID cross-
type witness, physical-disjointness or profile restriction is assumed.

checkedMixedCaptures_some exposes REAL Bool decoded output, uint decoded output,
Bool schedule output and final uint schedule output. Original all-object lengths
are derived across each actual step. Exact input-side success_lookup requires
actual calldataBools/calldataUints lookup, source SliceBounds, ORIGINAL capacities
and ORIGINAL-length CapturesValid lists. Payloads are extracted, never operation
inputs or correctness premises. none_first expands four SHORT-CIRCUIT failure
positions: Bool decoded None; reached uint decoded None after BoolSome; first
actual Bool schedule failed step after a real prefix; first actual uint schedule
failed step after whole Bool schedule and real uint prefix. No unexecuted suffix
heap, Source halt or rollback is invented.

ALL final reads for BOTH destinations are INITIAL replaceSlice reads at their
computed captureOrigin. Joint whole-heap restoration iff requires BOTH computed
INITIAL-content agreements, not desired final equality or stagewise preservation.
Other typed objects and lengths frame, including reference-containing parents;
parent fields retaining IDs do not imply unchanged dereferenced children. New
transport derives exact immutable decoded Source reads for both provenance maps,
uses explicit existing DecodedArrayAt certificates and independent INITIAL Keeps
for growth, and allocates supplied MObj on the actual BOTH-decoded changed heap
before the two schedules. Fresh own fields frame without deep-child liveness or
fresh Source representation/address injectivity.

Controls use ONE actual Source.Calldata table with Boolean object at7 and uint256
object at9; raw byte list empty imposes no ABI decoder correctness. INITIAL Bool
[T,F,F]/uint[7,8,8] plus runtime tails ->Bool decode TTF/uintold ->both decoded TTF/
798 ->Bool repaired TFF/uint798 ->both repaired TFF/788. Five-stage FULL ordered
vectors and every-stage neighbor[0,max,1], Boolean parent IDs[0,0] and uint parent
IDs[1,1] are retained. Independent INITIAL-only criteria reconstruct success then
prove restoration, without a criterion roundtrip or run/postrelation premise.
Dynamic/fixed arrays support arbitrary runtime repair repetition counts; intrinsic
n+3<2^256 is existing object validity only, no added admission/schedule cap.

Selective skipped Bool repair successfully leaves TTF while uint is restored;
changed-source recapture (1,2,0) on BOTH arrays gives actual TTF/998, versus frozen
INITIAL reads FTF/898. Both source-read laws are directly applied at origins inside
the decoded footprints. Initial missing/reversed/source/destination guards on
BOTH transfers and actual successful prefixes before late Bool AND uint rejection
are explicit. Empty/exact-end and element32 observations remain element-level.
Actual decoded zero and maximum uint BOTH retain complete Boolean/uint/neighbor
vectors; max=2^256-1, no guessed encoding/truncation premise. Direct initial Keeps
application uses real Heap.alloc; actual after-both-decoded allocation records both
changed children, actual schedule calls, complete final vectors and fresh parent
IDs[0,0],freshid5. Nonrestoring changed-run length vector[n+3,n+3,3,2,2] exercises
all-object length transport including fixed parents. Earlier expected controls
are unchanged.35new public laws/controls carry exact standard-only axiom guards.

Independent read-only finder/skeptic preliminary review found no core defect;
both required direct BOTH source reads, initial and after-both-decoded allocation,
all four rejection positions, and selective/frozen negatives on the COMPOSED run.
These were implemented. Focused extraction diagnostics exposed literal Fin1
rewrites versus list-length indexing; concrete equalities over existing values
resolved them without conversion assumptions. Explicit Keeps certificate binding
was corrected; all failed receipts retained, no failed elaboration deliverable.
Final independent source/artifact reviews and gates recorded in checkpoint26.

Preflight575193088 available bytes,32MiB forecast based on prior24182784-byte gate
plus8MiB source/log/compact exports; residual541638656 above512MiB. SAME existing
runtime, child12GiB/no-swap under16GiB parent, serial Lean-j1/LEAN_NUM_THREADS1,
optional cache OFF in TOML and actual LAKE_CACHE_DIR empty/LAKE_ARTIFACT_CACHE=false;
all source/caches/toolchains/seals and proof/fuel/node/stack/time/TestSuite budgets
preserved. Per-file Lean MCP/get_goal unavailable; serial focused closures used,
existing blocked goal unchanged. Original G32-G35 and Backfill A/B remain partial/
blocked; physical bytes/all-profile constructors/target failures/general path-
delete-rebinding/general ABI-reference-storage/fresh deep-copy/recursive Source
graph/reserved memory-to-storage/final V10-Source-target obligations stay open.
No independent-work exhaustion, full-lane or compiler/EVM correctness is inferred.

Final independent read-only finder and skeptic accepted refined source/doc and
all35guards: explicit both source-read laws, four rejection positions, independent
joint initial criterion, selective/frozen negatives, full five-stage vectors and
initial/after-both-decoded allocation. No outstanding source finding. Actual
86guardedjobs/full930default/262TestSuite/SolKey377taclets131read-bearing PASS exit0.
Strict/layer/orphan/trust/complete fixtures/script syntax/corruption checks PASS;
632owned standard-only pins79modules. Raw global docs FAIL1 with COMPLETE exact-
base byte equality (separate noNEW PASS); inventory FAIL1,646unrecorded14inherited+
632owned,zero unsafeerrors. Reserved records unchanged; additive proposals exported.

Actual Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs PASS. Full sampled aggregate
Lean/Lake RSS1452176KiB; cumulative session peak2160848896bytes;zeroOOMevents.
Full disk increment188416bytes within32MiB envelope; prefull parent/child/OS and
remaining forecast evidence retained. Warm caches and every previous seal/error
preserved; optional cache OFF in TOML and propagated exec environment.

Original queue reassessment remains exact: G32 physical-byte representation/
bridge and target frames open; G33 all-profile default/reference construction and
target allocation failures/stack-tail execution open; G34 general path/rebinding/
delete/stale-alias compilation open; G35.01 full source/target storage-copy
realization/liveness open; G35.02 reserved memory-to-storage prerequisite blocked;
G35.03 general ABI/reference/calldata-storage/source transport open; G35.04 fresh
memory deep-copy/emitted loops open; G35.05 recursive Source graphs/maps/shadows/
cycles/emitted traversal open; G35.06 reserved-copy and final V10/Source/target
composition blocked. Backfill A/B advanced, not complete or exhausted. This is
actual intrinsic mixed composition, not final compiler/EVM/bytecode correctness.
Existing blocked goal unchanged/uncompleted; no full-lane completion claim.


## Checkpoint twenty-seven: per-child mixed footprint precision

After sealed checkpoint26, a concrete original Backfill B/G35.03 correspondence
clause remained: joint whole-heap restoration requires BOTH arrays to restore,
whereas an OLD Boolean child can be restored while uint remains changed. No
existing owned mixed-child law supplied that precise case. New owned
MixedChildFootprint derives exact per-destination iff from the EXISTING mixed
read law and actual immutable payload uniqueness; neither criterion assumes a
final relation, stagewise preservation or restoration of the OTHER destination.
`BoolChildRepr.mixed_schedule_iff` consumes ONLY an explicit INITIAL old immutable
child table relation and the actual successful composed operation, then reduces
to the independently computed Boolean INITIAL criterion. This is the existing
Bool-child observer, not a new recursive graph/value/state semantics.

Inhabited actual controls use published same mixed input7/9. The old observer
is independently inhabited by existing bools(old n)/cdRef7 BEFORE execution;
no fresh Source entry or address injectivity is manufactured. Real decoded Bool
and uint writes change TFF/788 to TTF/798. Boolean recaptures repair TFF while
uint schedule is empty, retaining798. The OLD Boolean child relation is true by
its INITIAL-only criterion while the whole heap differs and the uint criterion
is false by the new uint iff. Same inputs with both schedules empty execute Some
with TTF/798 and false old Boolean child correspondence. Both complete destination
vectors and repeated-parent IDs[0,0] are retained; arbitrary runtime n/copies use
existing intrinsic object validity only. No false premise that unchanged parent
fields imply unchanged descendants, general child graphs, fresh deep-copy,
physical bytes, ABI/compiler/EVM or Source execution is asserted.

Both independent read-only source reviewers found no mathematical/ownership
issue in the precise clause and meaningful nonvacuous controls. Focused diagnostics
required explicit inclusion of the ACTUAL run premise in section theorems and
proper value normalization; those were fixed without weakening statements.
Five public laws/controls carry exact standard-only guards; prior errors/seals
remain retained. Original queues remain partial/blocked with the exact upstream
and reserved prerequisites enumerated in checkpoint26, not exhausted or complete.

Storage bound now uses16MiB for ONE small module, unchanged executable roots/
cache/toolchain and four actual warm full gates188416..192512bytes, <=4MiB compact
exports plus module/log/safety allowance. This changes no fixed resource/OS guard:
preflight569888768bytes,residual553111552 above512MiB; cacheOFF/child12GiB-no-swap/
parent16GiB/serialLean-j1/LEAN_NUM_THREADS1 and all proof/time/test budgets remain.
No file/cache/seal deletion, relocation, runtime replacement or capacity change.

Final independent finder and skeptic read-only source/doc review accepted actual
run premises explicitly included, precise per-object/old-child boundary, five
standard guards and nonvacuous executed controls. No remaining source finding.
Actual87guardedjobs/full931default/262TestSuite/SolKey377taclets131read-bearing
PASS exit0. Strict/layer/orphan/trust/complete fixtures/script/corruption checks
PASS;637standard-only pins80modules. Raw global docs FAIL1, COMPLETE exact-base
byte equality/noNEW separately PASS; raw inventory FAIL1,651unrecorded14inherited+
637owned,zero unsafeerrors. Proposed additive reconciliation remains unintegrated.
Actual Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs PASS. Full sampled aggregate
Lean/Lake RSS1592876KiB,cumulative session peak2160848896bytes,zeroOOMevents;
188416byte full disk increment, within documented16MiB warm-route bound. No
resource/proof/stack/time/test guard change, deletion or cache/source relocation.
All original G32-G35/Backfill A/B parents remain partial/blocked; typed local
observer precision is not recursive Source graph/fresh deep-copy/byte-memory/
all-profile-default/target-failure/path-delete-rebinding/reserved-copy/final
Source-V10-target closure. Existing goal unchanged and unfinished, no exhaustion
or compiler/EVM claim.


## Checkpoint twenty-eight: existing nested observer after mixed schedules

Reproduced missing clause: RefChildRepr.mixedSequence/mixedSequence_agrees covered
transfer-only sequences, while the new actual checkedMixedCaptures had only a
direct BoolChildRepr footprint application. New owned MixedNestedFootprint uses
EXISTING RefChildRepr, BoolChildRepr, Heap/HRef/ArrTy and actual mixed operations;
no graph semantics, state/value layer, copy algorithm, decoder or public cutoff.

checkedMixedCaptures_ref_root_frame derives root identity from intrinsic primitive/
reference-array separation. RefChildRepr.mixed_schedule_iff is PRECISE in BOTH
directions: given an independently inhabited INITIAL old nested relation and an
ACTUAL successful run, final old nested correspondence iff every INITIAL selected
leaf whose LOGICAL ID aliases the Bool destination meets the computed INITIAL
Boolean payload/provenance criterion. Other leaves use actual frame; uint/Bool-
leaf separation is type-derived. Repeated descendants are permitted; no pairwise/
global address injectivity, Uint restoration, whole-heap equality, stagewise or
final desired child relation is a premise. Necessity follows from the existing
old-child object equality observer and unchanged root membership; sufficiency
uses per-object restoration only for aliases. No extra reverse-direction premise.

RefChildRepr.mixed_schedule_index_bool derives the postrelation and ORIGINAL
outer-bound transport, then calls the EXISTING index_bool/index APIs. It observes
real outer pointers and inner Bool contents at the final heap, not root IDs alone.
This is the published finite two-level observer, not unrestricted recursive
Source graph/cycle/map/shadow correspondence or fresh deep-copy compilation.

Controls independently populate OLD tables at7/8 for Boolean children,10 for
root[r,other,r] plus runtime repetitions of other, and11 for a NONEMPTY root
containing only other. Old root and leaf correspondences are proved BEFORE
execution; these are given existing objects, no Source entries for new memory.
Actual input is the existing combined decoded table7/9. Actual Bool/uint writes
change TFF/788 ->TTF/788 ->TTF/798; actual Bool recapture repairs TFF while Uint
stays798. Full five-stage arrays, unchanged other-child FT and BOTH root ID
vectors are explicit. The actual both-decoded intermediate has FALSE old nested
correspondence; the final aliased root is TRUE via an INITIAL-only criterion.

SAME old table/root and successful both-schedules-empty run yields TTF/798,
identical root fields, FALSE selected-root relation and a concrete wrong inner
read: OLD decoded false at child7/index1 versus actual some true. Under that SAME
nonrestoring run the NONEMPTY disjoint root remains represented; no selected
alias means no Bool restoration obligation, not an admission restriction or an
empty-root vacuity. Positive reads invoke the NEW composed index adapter and
existing index_bool: outer0 and2 select repeatedr, outer1 selects other, inner1
reads false/true respectively with actual OLD decoded observations. Outer and
selected-child endpoint Option None/decoded-read rejection and outer element32
(nonempty runtime tail) are retained without Source halt/rollback or byte claims.

Both independent read-only preliminary reviewers found no core defect and asked
that these actual skipped/disjoint/read/bound cases be completed; they now are.
Focused core alias-elimination naming and endpoint reflexivity errors were fixed
without statement/bound changes; every failed receipt retained. Ten new public
laws/controls have exact standard-only axiom guards. Initial tables/layouts/types,
observations and all previous fixture vectors are preserved.

Preflight566722560bytes,16MiB warm-route source/module/log/export/safety bound,
residual549945344bytes above512MiB. Same capped runtime, child12GiB/no swap under
16GiB parent with OS headroom, Lean-j1/LEAN_NUM_THREADS1 and unchanged proof/fuel/
node/stack/time/TestSuite guards. Artifact cache OFF in TOML and actual exec
LAKE_CACHE_DIR empty/LAKE_ARTIFACT_CACHE=false; keyed warm outputs and every old
file/cache/seal retained, no replacement/deletion/relocation or capacity change.
Per-file Lean MCP/get_goal unavailable; serial focused closures used, existing
goal unchanged. Original G32-G35 and Backfill A/B remain PARTIAL/BLOCKED with all
physical-byte/all-profile-default/target-failure/general-path-delete-rebinding/
ABI-reference-storage/fresh-deep-copy/recursive-Source/reserved-memory-storage/
final V10-Source-target obligations explicitly open; no exhaustion/full lane or
external compiler/EVM correctness is inferred.

Final independent read-only finder/skeptic source/doc review accepted precise
necessity/sufficiency, derived root/leaf separation, complete alias/disjoint/
staged/read/endpoint controls and ten exact guards; no outstanding source finding.
Actual89guardedjobs/full933default/262TestSuite/SolKey377taclets131read-bearing
PASS exit0. Strict/layer/orphan/trust/complete fixtures/script/corruption controls
PASS;647owned standard-only pins82modules. Raw global docs FAIL1 with COMPLETE
exact-base byte equality/noNEW separately PASS; raw inventory FAIL1,661unrecorded
14inherited+647owned,zero unsafeerrors. Additive proposals exported; reserved
inventories/manifests/generated ledgers remain untouched.

Actual Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs PASS. Full sampled aggregate
Lean/Lake RSS1443848KiB,cumulative session peak2160848896bytes,zeroOOMevents;
188416byte full disk increment within16MiB measured warm route. All proof/fuel/
node/stack/time/TestSuite/resource guards preserved, cache OFF in actual exec.

Original full-queue reassessment after this observer application: G32 still lacks
physical-byte/heap representation and emitted target frames; G33 all-profile
constructors/defaults/target size-allocation failures and stack-tail execution
remain open; G34 general path/rebinding/delete/stale-alias compilation open;
G35.01 published intrinsic storage-tree transport is partial without full Source/
target/liveness realization; G35.02 reserved memory-to-storage owner prerequisite
blocked; G35.03 now has this existing two-level OLD observer application, NOT
general ABI/reference conversion/calldata-storage/Source execution; G35.04 lacks
fresh deep-copy/emitted loops; G35.05 general recursive Source graphs/maps/shadows/
cycles/emitted traversal open; G35.06 final reserved-copy/V10/Source/target chain
blocked. Backfill A/B advanced, not complete or exhausted. No source profile,
refusal, invariant, expected vector or predicate was weakened to fit the proof.
Existing blocked goal unchanged/uncompleted, no compiler/EVM or lane closure claim.


### Checkpoint29: reflection and real mixed-allocation nested observer

Parent25161394ec3245006894c588521f96f2096ceffc, exact frozen base unchanged.
`MixedNestedGrowth` proves BoolChildRepr.grow_iff and RefChildRepr.grow_iff:
actual Keeps reflects as well as preserves the SAME OLD finite observer. Root
fields map old typed refs; primitive leaf contents weaken identically. No reverse
address injectivity, new source entries or fresh-root representation is assumed.
`RefChildRepr.mixed_alloc_iff` consumes actual checkedMixedCaptures success and
published checkedMixedCaptures_alloc, allocating a supplied MObj on the ACTUAL
both-decoded intermediate before reached recaptures. Final old nested relation
is equivalent to the independently computed INITIAL selected-alias Bool criterion.
No uint restoration, desired final relation, whole-heap equality or stagewise
correspondence is a premise. Fresh own fields frame, not descendant liveness.

Existing C28 fixtures are reused, not reconstructed: arbitrary runtime n/copies,
repeated selected aliases and nonempty disjoint root, original intrinsic n+3
validity only. allocated_repair executes decoded Bool/uint initialization, then
actual allocation of reference-containing [r,r,other], then actual repair. Old
nested relation remains FALSE after allocation alone and TRUE after repair;
Boolean TTF becomes TFF, uint798 remains changed. Fresh own IDs[0,0,1] stay fixed;
actual weakened outer/inner indices and OLD decoded outer+inner reads agree.
allocated_skip uses SAME old table/real allocation: selected nested relation
FALSE, disjoint nonempty root TRUE, actual inner true contradicts OLD false.
All original C28 five-stage/neighbour/root/child vectors, endpoints, element32,
lookup/bounds failures and previous controls remain unchanged and checked.

Five new public laws/controls have exact standard-only guards. Focused core PASS,
controls01/02/03 FAIL retained (dependent weakening reductions/prefix placeholder),
controls04 PASS and guarded01 PASS91jobs after actual repairs without statement
or bound changes. Finder and skeptic independently accepted source/proof controls,
no Lean/server/builds by reviewers. Per-file MCP/get_goal unavailable; existing
blocked goal unchanged. No physical bytes/ABI/Source/compiler/EVM/deep-copy claim.

Preflight562831360bytes,16MiB warm-route forecast,residual546054144 above unchanged
512MiB reserve. Same runtime/cache identity, child12GiB/no-swap under16GiB parent,
OS headroom, serial Lean-j1/LEAN_NUM_THREADS1. Optional cache OFF in TOML and actual
exec; all old files/caches/seals/failures preserved. Original G32/G33/G34/G35.01,
.03/.04/.05 and Backfill A/B remain PARTIAL; G35.02/.06 BLOCKED. All named physical
byte/default/target-failure/general-path/ABI-reference-storage/fresh-deep-copy/
recursive-Source/reserved-copy/Source-V10-target obligations remain open. This
application does not establish original-lane completion or independent exhaustion.

Final C29 guarded91jobs/full934default/262TestSuite/SolKey377/131 PASS exit0;
actual Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs PASS. Five new standard pins,
cumulative652owned/83modules; global inventory FAIL1,666unrecorded=14inherited+
652owned,zero unsafeerrors. Raw strict docs FAIL1; COMPLETE exact-base bytes
identical/noNEW separately PASS. Initial script route inside retained runtime
lacked git (trust1/docs127/diff127), raw logs retained; repaired supported host
script route PASS trust/layers/orphans/strict/fixtures/corruption/script checks.
No container/toolchain replacement or policy bypass. Independent final reviewers
accepted proofs/controls and requested cumulative heading twenty-nine, corrected.
Full sampled Lean/Lake RSS1460752KiB,cumulative sessionpeak2160848896bytes,zeroOOM;
188416byte full increment within16MiB envelope. Source/target/physical/general
recursive and reserved-owner obligations remain as above, goal unchanged.


### Checkpoint30: recursive mirrors through arbitrary actual schedules

Parentedb60d4d04830dc9f7c6e30b96ffe63b2bdc7461; exact frozen base unchanged.
CopyMirrorSchedule derives recursive fresh-node frames from runCaptures_frame,
old destination id_lt and original H.length freshness. runCaptures_mirrors uses
an independently established INITIAL mirror and explicit destination-below-bound;
copy_schedule_mirrors/default_schedule_mirrors discharge those premises using
published mirrors_copyStToM and actual copyStToM/allocDefault, with mapFree kept.
No desired final mirror, whole-heap equality or fixed depth/shape/schedule cutoff.
copy_schedule_transport lifts an actual successful OLD run through the REAL
builder via published Keeps, and proves complete recursive mirror and all fresh
object frames at reached output. copy_schedule_none_first exposes the actual
successful prefix, first failing reached call and mirror ONLY at that prefix;
Option failure is not Source rollback/halt. two_builder_schedules_mirrors composes
two actual recursive builders with arbitrary successful old-root schedules between
and after them, using existing Mirrors.wk and derived frames, no new traversal.

Controls REUSE existing fixtures. Real checked prefix changes TFFF to TTFF before
nested fixed/dynamic copy/default construction. Nonempty reached tail changes old
array to TTTF, followed by arbitrary runtime exact-end empty operations; complete
initial/changed/copied/final vectors and old/fresh root identity/structural frame
proved. Nonzero Person/Account/Token fields11/9/7 survive. Existing two-builder
Person/default operation outputs are directly recovered through the NEW schedule
composition, with arbitrary runtime empty suffix, preserving existing element32,
zero/nonzero family/descendant reads, identity and field fixtures.

Finder requested direct use of the NEW failure iff: late_failure now applies
copy_schedule_none_first to real nonempty changed prefix then invalid(0,5,0)
(overruns BOTH source and destination capacity4, not an isolated-source claim).
Skeptic requested TWO material post-builder writes: reached_changed_source executes
actualSome1,2,2 then actualSome2,3,3, giving complete TTFF→TTTF→TTTT vectors and
final mirror. Initial builder source2=false but actual final destination3=true;
this concrete negative distinguishes frozen initialization from actual recapture.
Existing descendant_mutation_negative still executes a write INTO a copied leaf,
keeps parent identity yet falsifies recursive mirror. Old-destination separation
is derived from freshness; this is a local theorem case, never profile exclusion.

Thirteen new exact standard-only guards. Focused core PASS86, pair PASS88;
controls01..08 failures retained (endpoint reflexivity, opaque/dependent context
reductions and explicit Keeps/list proof arguments), controls09 PASS87 after
repairs without changing expected vectors/bounds. Failed elaboration sorryAx is
not accepted: final guards require exact standard-only sets. No proof/fuel/node/
stack/time/TestSuite budget changes, no reserved source edit or new semantics.

Preflight559394816bytes;16MiB small keyed warm-route forecast leaves542617600,
above unchanged512MiB reserve. Same idle capped runtime child12GiB/no swap under
16GiB parent with OS headroom, serial Lean-j1/LEAN_NUM_THREADS1, artifact cacheOFF
in runtimeTOML AND actualexec emptyLAKE_CACHE_DIR/LAKE_ARTIFACT_CACHE=false. All old
files/caches/seals/failures retained. Per-file MCP/get_goal unavailable; existing
blocked goal unchanged. All original G32/G33/G34/G35.01/.03/.04/.05 and BackfillA/B
PARTIAL, G35.02/.06 BLOCKED. Physical byte representation, all-profile constructors/
target failures, general paths/rebinding/delete, ABI/reference/storage, fresh
memory deep-copy/emitted loops, recursive Source graphs and reserved memory-storage/
final V10-Source-target composition remain open. No exhaustion or compiler/EVM claim.

C30 final independent finder/skeptic source/doc reviews ACCEPTED after requested
failure-iff application and two-material changed-source control were added. No
remaining source/ownership finding. Guarded closures PASS87/88, full935default/
262TestSuite/SolKey377/131 exit0; actual Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs
PASS. Strict/trust/layer/orphan/completefixture/script/corruption controls PASS;
665owned standard pins84modules. Raw docsFAIL1 complete exact-base byte equality
separately PASS, SHAea1a09c222d52d1d17953f653c087443e34e6282497f0b02cdc09aad15b7dd48.
Raw global inventory FAIL1,679unrecorded=14inherited+665owned,zero unsafe errors;
additive coordinator proposals exported, reserved records untouched.
Full sampled aggregate Lean/Lake RSS1520240KiB,cumulative sessionpeak2160848896bytes,
zeroOOMevents;188416byte fullincrement within16MiB forecast. No guard/budget change.

Full original queue reassessment: G32 physical-byte representation/target frames
remain missing; G33 all-profile constructors/defaults/target failure/stack-tail
execution remain open; G34 general path/rebinding/delete/stale-alias compilation
open; G35.01 now includes arbitrary old-root schedule transport of published
map-free recursive Mirrors, but independent Source/target/liveness realization
still open. G35.02 reserved memory-to-storage blocked; G35.03 general families/
reference/ABI/calldata-storage/Source open; G35.04 fresh memory deep-copy/emitted
loops open; G35.05 general recursive Source graphs/maps/shadows/cycles/emitted
traversal open; G35.06 reserved-copy/V10/Source/target composition blocked.
Backfill A/B advanced, not complete/exhausted. No new admission shape or profile
restriction, no external compiler/EVM validation or whole-assignment claim.


### Checkpoint31: published prerequisites and independent Source memory

Original assignment/base fb379ae20f10e2c92113453ddd9d40d8f2efbe09 retained as ancestor.
ParentC30a8ae632c994157445db289394dbdd60c7640ec98 is preserved. User authorized
synchronization with published origin/master2fe1f8932f96be15b00df03ba2cde46f64a87758;
FETCH_HEAD and origin/master matched exactly. Merge only on isolated assigned
branch; no push/default-branch merge/PR/unpublished import. Three mechanical
append conflicts in Solidity.lean/docsREADME/modulemap retained BOTH blocks.
Independent finder/skeptic sync reviews checked incoming owner blobs identical to
publication and all84 preexisting owned modules identical to C30. Existing live
checkout is not in prior absolute-path seals; runtimeTOML remains untracked.

New Source.Eval/Machine/WellTyped/ValueProgress/ExprProgress/StmtProgress are REAL
published independent semantics/progress. The OLD blanket assertion that execution
is unavailable is superseded. Their docs retain partial Source coverage: value/
call-fragment progress has explicit fragment/domain/call premises, NotStuck allows
bounds panic, and MemOK needs reference typing/top shape/bare inner values. This
checkpoint uses actual memory-operation execution and published allocRef_mem',
not an assertion of whole SourceSpec/Source slice compiler completeness.

SourceMemory defines only a typed local INITIAL object representation and a
Source.Data array constructor, no new heap/value/evaluator/allocator. source_bool_read
and source_bool_bounds prove actual Source.memElem run results and unchanged state;
read_iff relates actual Source.readLoc(.mem) to the intrinsic typed index. Bounds
are the actual .revert(panicData.index), not Option rejection re-labelled halt.
schedule_read_iff composes actual independent Source reads at computed INITIAL
origin with actual reached runCaptures final observations. source_bool_alloc is
actual published Source.allocRef execution; source_bool_alloc_memOK consumes
allocRef_mem' with DataOK/Top/Inner discharged for bare Bool elements. copy_schedule
connects this Source observation to C30's ACTUAL recursive mapFree copy builder
and arbitrary reached old-root recaptures: final complete Mirrors AND read iff
are conclusions. Initial local representation, actualSome and mapFree remain
explicit; no desired final relation/evaluator equality/fresh Source graph premise.
This is observation transport, NOT compilation of a Source copy loop or bytecode.

Controls construct Source states ONLY as actual allocRef outputs. Independently
inhabited MemOK/SourceBoolMemoryAt precede the intrinsic copy. Arbitrary n/copies
(existing n+3<2^256 validity only) exercise nonprimitive recursive copies, actual
reached0→1 then changed1→2 captures, complete initial/copied/final TFF→TFF→TTT
vectors with runtime false tails, untouched neighborFT, actual Source origin0true
and wrong-frozen-origin1false. Source state remains unchanged during reads; the
Source copy program is NOT claimed to execute. Empty Source allocation/read,
exact runtime endpoint Source panic + intrinsicNone, wrong type and dangling
Source stuck controls distinguish the failure mechanisms. Element32 uses36old
Source/target elements and actual nonprimitive builder/schedule; large-tree
family remains generic. A literal tree34 witness exceeded200000heartbeats; kept
raw failure, used direct general bridge with small nonprimitive tree for same
old-element32 observations, no budget change. Every failed elaboration retained.
Thirteen new public laws/controls pinned to exact standard-only axiom sets.

Storage preflight originally555655168bytes; exactpublic fetch ~7MiB. User allowed
narrow stopped task cache-layer maintenance. Audited ten v11-builder-controls
containers: STOPPED,SizeRw0,diff only mount placeholders, source/evidence/cache
externalworkspacebind. Preserved10logs/state/mount/diff metadata before removing
only those10IDs; reclaimed~1.7GiB, runningruntime/images/all source/cache/seals
untouched. No globalprune/newcontainer/relocation/limit change. Same12GiB/no-swap
child under16GiB parent, OS headroom, serial Lean-j1/LEAN_NUM_THREADS1, cacheOFF
actualexec andTOML; sourceprogress25jobs and newguardedclosure use existing warm
outputs. Full new-public gate forecast1GiB plus128MiBlogs/artifacts/safety, reserve
512MiB; >2.1GiB available after focused closure. Per-file MCP/get_goal unavailable;
existing assignment unchanged, no goal recreation/reactivation/completion.

G32 physical bytes/target frames, G33 all-profile/target allocation failures,
G34 general path/write/rebinding/delete compilation, G35.01 deep Source/target
copy/liveness, G35.02 reserved memory-storage, G35.03 general reference/ABI/storage
copy execution, G35.04 fresh memory deep-copy/emitted loops, G35.05 recursive Source
graphs and G35.06 full V10/Source/target chain remain OPEN. New source availability
is consumed for the supported local read/allocation case; earlier holds are not
repeated as a blanket excuse. Backfill A/B advanced, not exhausted or complete.

C31 final synchronized gate:1067 default jobs,262 TestSuite jobs, final SolKey377/131, wrapper exit0. Peak sampled aggregate Lean/Lake RSS11432472KiB, cumulative child peak12884901888bytes, memory.max event delta479, OOM/kill deltas0. The existing cap was reached and enforced; no limit/budget change. Complete strict timing check is recorded separately. Raw docs exit1/current83findings exactly equal new public baseline;11incoming findings relative original frozen72 remain a FAILED original no-new gate, not V11 regressions. Global inventory exit1:1037unrecorded=359public inherited+678owned,0unsafe; scoped678standardpins/86modules pass independently. Global whitespace exit2 matches public inherited Source/Horizon debt; owned-vs-public whitespace passes.

## Checkpoint thirty-two: independent Source read/write and actual intrinsic capture

Reproduced a distinct supported original G34/G35.04/BackfillA-B clause: C31
observes initial Source reads but does not execute Source writes. SourceWrite
composes EXISTING readLoc then writeLoc at the actual reached Source state.
source_bool_write proves published memSet's exact state/heap.write with canonical
updated typed Data; no second allocator/state/evaluator. capture_singleton_elems
derives actual captured payload from the intrinsic source slot and exact target
list.set; no caller-supplied payload or conversion oracle. SourceBoolMemoryAt.copy
derives actual checkedCaptureOverwrite Some, actual Source composed Some and
final local representation from INITIAL representation and two runtime bounds.
copy_memOK consumes published writeLoc_memOK after the actual read; no desired
final invariant premise. source_bool_write_bounds/copy_bounds derive actual
Source index panic and OptionNone separately, with first-read short circuit and
bad-write-after-successful-read cases, no invented rollback/suffix heap.

Controls reuse C31's independently allocated Source state, existing intrinsic
heap and initial MemOK. Both Source and target actually execute0→1 then changed
1→2, with complete old/mid/final TFFtail/TTFtail/TTTtail, complete Source object
contents, untouched target neighborFT, both reached MemOK, original read1false
versus reached read1true/finalread2true and frozen-sourcefalse negative, IDs0/1.
Runtime n is uncapped beyond existing n+3<2^256 object validity. Independent bad
source and destination exact-end outcomes retain successful read0 before bad
write. Actual element32 changes false→true and retains neighbor. All prior
nonprimitive/default/copy/schedule/empty/alias fixtures and exact pins remain.
Nine new public laws/controls carry exact standard-only axiom guards.

Focused failed elaborations are retained: redundant simplification, dependent
Data-array congruence/index casts, Hoare run reduction and dependent list rewrite
motives were repaired. No theorem, observation or premise weakened, no heartbeat/
fuel/node/stack/time budget changed; no deliverable sorryAx. Same runtime/lock,
12GiB/no-swap child and16GiBparent, serialLean-j1/cacheOFF; preflight1.72GiB free
and64MiB warm-build/log/export envelope with unchanged512MiB reserve.

This is actual independent Source primitive operation transport, not compilation
of resolved syntax or a Source slice loop. G32 physical bytes/target frames, G33
all-profile construction/target failure, G34 general path/rebinding/delete/stale
alias compilation, G35.01 general Source/target copying/liveness, G35.02 reserved
memory-storage, G35.03 general ABI/reference/calldata-storage/target, G35.04 fresh
deep-copy/emitted loops, G35.05 recursive Source graphs and G35.06 final V10/Source/
target chain remain open. Backfill A/B advanced, not exhausted or complete.

C32 guarded closure109jobs PASS; final unchanged run-lean.sh1068default/262Suite/
SolKey377/131 exit0. Strict automatic, fixture/layer/orphan/trust/lane687standard
pins/87modules/script corruption pass. Warm final gate233472bytes disk growth,
peak aggregateRSS1675360KiB, no new memory.max/OOM/kill events; cumulative session
peak12GiB belongs to earlier C31 cold gate. Separate source finder/skeptic accept
with no defect; neighbor framing explicitly intrinsic-only. Raw docs1 exactly
public baseline83 findings, original no-new remainsFAIL for11incoming; raw global
inventory1:1046unrecorded=359publicinherited+687owned,0unsafe. Reserved inventories
unchanged. Complete gate/resource/review receipts and additive proposals retained.
