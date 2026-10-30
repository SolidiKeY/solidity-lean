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

| Item | Status | Remaining obligation / owner boundary |
|---|---|---|
| G32 | partial | Intrinsic heap-object framing/noninterference components here; typed heap-to-byte representation and final separation transport still need the reserved byte-memory bridge and actual target interfaces. |
| G33 | partial | Old-slice allocation/default-construction extension and fresh-vs-alias identity proved using published constructors. All-type construction/defaults, exact target allocation failures and stack/frame transport remain; reference constructors stay with reserved owners. |
| G34 | partial | Typed slice coordinate/read/overwrite adapters and identity controls proved. General paths/rebinding/delete, stale aliases and nonprimitive source/target compilation remain; existing MemoryCompile/MemoryObjects queues untouched. |
| G35.01 | partial/reserved prerequisite | Published intrinsic storage-copy old-slice/local preservation and fresh-root transport consumed. Storage-to-memory target compiler/representation/liveness relation still required from owners. |
| G35.02 | open/reserved prerequisite | Memory-storage-copy owner retains implementation, tail clearing and mapping obligations. |
| G35.03 | partial | Independent endpoint/captured-read laws only. Actual immutable calldata-to-memory/storage transport and source relation remain. |
| G35.04 | partial | Actual intrinsic shallow overwrite, original-heap snapshot and overlap/framing laws proved. Target emitter, language alias/deep-copy classification and fresh deep-copy transport remain. |
| G35.05 | open | Generic runtime typed recursive traversal for every approved shape, deep child-content traversal and target simulation remain; context/heap extension for these adapters is proved. No fixed cutoff is introduced to claim coverage. |
| G35.06 | blocked | Requires all preceding copies plus V10/source/target composition; no V07–V10 unpublished lane imported. |
| Backfill A | partial | Bounds, snapshot/overlap, allocator-extension and heap-write framing components proved. Actual calldata adapters, byte word-boundary transport and their target noninterference remain. |
| Backfill B | partial | Nested typed alias/growth/read/overwrite witnesses and coordinate composition proved. Context extension and intrinsic storage-tree/memory growth/overwrite combinations proved. Generic recursive child traversal and full storage/calldata/memory source/target identity composition remain. |

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

### Remaining published-interface blockers

The exact pinned `Evm/MemoryObjects.lean` relations use `Machine.mem : Nat → Word`,
one word per element and dynamic headers. `MemoryObjectCompile.StmtFrag` and
construction certificates prove only their published fragments. Neither gives
this lane a range-copy byte emitter/bridge. G04 R31 records the missing
byte-addressed memory; R25 records the still-explicit allocator-capacity premise
and missing generated panic check. `AllocationInput` and `GrowsAllocator` in `Evm/MemoryObjectAllocator.lean` retain those capacity hypotheses. This lane cannot erase
them or count operation-side naturality as exact allocation-failure compilation.

`Source/State.lean` publishes immutable decoded tables and typed array fields,
but `Source/TypingExamples.lean` explicitly defers source slice execution to S02.
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
