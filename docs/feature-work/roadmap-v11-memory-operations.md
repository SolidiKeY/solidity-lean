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
