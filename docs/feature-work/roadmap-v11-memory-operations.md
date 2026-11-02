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

Current cumulative accounting through checkpoint forty-nine. Earlier checkpoint
narratives retain their historical observations and gate outcomes.

| Item | Status | Remaining obligation / owner boundary |
|---|---|---|
| G32 | partial | Intrinsic heap-object framing/noninterference and supported Source primitive delete-to-symbolic-word frame components here; typed heap-to-byte representation and final separation transport still need the reserved byte-memory bridge and actual target interfaces. |
| G33 | partial | Old-slice allocation/default-construction extension and fresh-vs-alias identity proved using published constructors; supported actual Source Boolean allocation/zero-default and resolved declaration with a fresh typed local, intrinsic and word fresh-root/old-object framing, and enlarged-context MemOK preservation now checked. All-type construction/defaults, exact target allocation failures and stack/frame transport remain; reference constructors stay with reserved owners. |
| G34 | partial | Typed slice coordinate/read/overwrite adapters, identity controls and actual supported Source memory reads, single-element read/write-to-intrinsic-copy and primitive delete-to-clearT transitions plus resolved Source local-index deletion and Boolean assignment expression/statements plus actual reached RItems/intrinsic-program/word sequencing and selected reference-local rebinding with parallel pointer identity proved. General paths/rebinding/delete, stale aliases and nonprimitive source/target compilation remain; existing MemoryCompile/MemoryObjects queues untouched. |
| G35.01 | partial | Published intrinsic multi-object storage copying and recursive Mirrors are consumed; interleaved builder/snapshot mirror frames are proved here. Source/target compiler, physical representation and full liveness composition remain. |
| G35.02 | blocked | Memory-storage-copy owner retains implementation, tail clearing and mapping obligations. |
| G35.03 | partial | Actual decoded Boolean/uint256 table-to-existing-memory transfer, exact runtime guards, ordered reads, frames and growth are proved, including actual ordered two-transfer composition and local commutation. General families/reference construction, calldata-to-storage, ABI decoding, general Source copy/program execution and target transport remain. |
| G35.04 | partial | Actual intrinsic shallow overwrite, original-heap snapshot and overlap/framing laws proved. Target emitter, language alias/deep-copy classification and fresh deep-copy transport remain. |
| G35.05 | partial | Published finite map-free recursive Mirrors are transported through actual multi-generation builder/snapshot operations with typed generation separation. Source/type-graph/cycle/mapping/shadow coverage and emitted traversal/deep-copy realization remain; no fixed cutoff is introduced. |
| G35.06 | blocked | Requires all preceding copies plus V10/source/target composition; no V07–V10 unpublished lane imported. |
| Backfill A | partial | Runtime bounds, same-object intervals, ordered recapture, real allocator extension, Boolean/uint256 decoded transfer and element-boundary controls are proved. General family/physical-byte/target transport remains. |
| Backfill B | partial | Typed nested alias/growth/path and multi-generation recursive intrinsic mirror/identity composition are proved. All-profile fresh-root Source representation (supported Bool default root checked), general graph/deep-copy realization and mixed-location Source/target composition remain. |

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

## Checkpoint thirty-three: independent Source delete and intrinsic clearT

Original G34/BackfillA-B investigation found published Source.deleteLoc obtains
its primitive default via zeroVal, while actual intrinsic TRun.clearT uses
PrimTy.dflt through Heap.writeAddr. SourceDelete connects these EXISTING
operations. write_addr reuses C32 exact Source write, deriving actual intrinsic
address write and final local representation from initial lookup and bounds.
delete_addr uses the actual Boolean default, no supplied payload. clearT further
proves the ACTUAL typed-state intrinsic transition σ.withHeap out with identity
context extension, rather than only an arbitrary resulting relation. Initial
representation, valid intrinsic uint index and positive existing Source fuel
(fuel+1) are explicit. Published deleteLoc_memOK is consumed on actual success.
No final relation/MemOK/desired preservation is a premise.

Controls reuse independently allocated Source state and MemOK. Actual first
Source copy0→1 plus intrinsic checked capture materially changes TFFtail→TTFtail;
actual Source delete and intrinsic clearT then yield TFFtail. Complete Source
changed/final object contents, full three intrinsic vectors, neighborFT before/
after, typed local uint7 and OLD memory aliasr, both reached MemOK, innerreadtrue
thenfalse, and stale-true negative are retained. Runtime n remains uncapped
beyond existing intrinsic n+3<2^256. Fuel0 at the actual changed state TIMEOUTS
before write; positive-fuel endpoint panics with actual intrinsic writeAddrNone.
Timeout is not mapped to OptionNone or invented rollback. All prior element32,
nonprimitive builder, snapshot and bounds controls remain unchanged. Eight new
public laws/controls have exact standard-only guards.

Focused failed checks retained opaque len/address-match and definitional heap
equality proof issues, repaired without statement/observation/budget changes.
Same idle runtime/lock/cacheOFF/serial-j1/12GiB-no-swap child/16GiBparent and512MiB
reserve; available1.70GiB before64MiB warm route forecast. No source/cache/seal
deletion, new container or fuel/proof/node/time/TestSuite budget increase.

This advances actual independent primitive memory delete/path transport; it does
not compile resolved Source syntax, implement reserved reference deletion, prove
physical bytes or emitted target semantics. G32 physical representation, G33
all-profile defaults/target failure, G34 general paths/reference rebinding/delete/
stale aliases and target execution, G35.01 Source/target deep-copy/liveness,
G35.02 reserved copy, G35.03 general ABI/reference/storage, G35.04 fresh deep copy/
emitted loops, G35.05 recursive Source graphs and G35.06 final composition remain
open. BackfillA/B advanced, not complete or exhausted.

C33 final guarded110jobs, full1069default/262TestSuite/SolKey377/131 exit0.
Strict automatic, complete fixture, layer/orphan/trust, lane695standardpins/
88modules and script corruption pass. Final warm gate225280bytes disk growth,
aggregateRSS1545204KiB, no new memory.max/OOM/kill events. Raw docs1 still complete
public83byteequal, originalfrozenno-newFAIL11incoming; globalinventory1 remains
1054unrecorded=359publicinherited+695owned,0unsafe. These remain failed global
gates; coordinator additive reconciliation proposed only. Independent source
finder/skeptic accepted with no defect. All previous seals retained.

## Checkpoint thirty-four: independent Source delete to published word target

Original G32/G34/Backfill investigation found the actual published
Evm.Memory.deleteLocalValue_correct certificate. It was already available and
consumed read-only; no reserved Evm compiler file or implementation duplicated.
SourceDeleteTarget composes C33's ACTUAL Source.deleteLoc and intrinsic writeAddr/
clearT/deleteMem with that certificate. Initial local SourceBoolMemoryAt, initial
Evm.Memory.StateRepr, initialized typed memory local, actual index expression
evaluation/bound and the EXISTING compiler valIn fragment premise are explicit.
The index-code contract is derived via published val_sim, NOT assumed target
preservation. Actual intrinsic Some and deleteMem success, independent Source
Some, compiled run Some, final local Source relation, full final word StateRepr,
stack equality and existing allocator framing are conclusions. Positive existing
Source fuel remains explicit, not an altered run limit.

Bounds theorem derives actual Source index panic/state identity and actual
symbolic target revert from the same initial representations and out-of-bounds
index. These are SEPARATE exact observations: it does not equate Source panic
bytes to emitted returndata. General Source syntax, physical bytes, executable
bytecode and external EVM/compiler testing remain outside this certificate.

Controls independently construct the complete initial StateRepr: live Bool array
TFF at wordbase16 with header3, pointerlocalcell1=16, allocatorcell0=20, sentinel
cell5=99, stacktail42, no unproved initial/final representation assumption. Source
state is actual allocRef(TFF) output, independently MemOK. Direct general theorem
application executes Source/intrinsic/compiled deletion oftrue tofalse, complete
intrinsicTFF→FFF and source reads true→false; wordvector positions0,1,5,16,17,18,19
changes[20,16,99,3,1,0,0]→[20,16,99,3,0,0,0], stack42 preserved and stale1 excluded.
Actual endpoint3 Source panic and compiled revert are proved; fuel0 separately
timeouts. All earlier runtime, element32, nonprimitive and mixed-copy fixtures
remain unchanged. Four new public laws/controls pinned standard-only.

Retained failures include initial witness length/binder proof repairs and three
closed-machine raw-run conversions hitting unchanged200000heartbeats with
12GiB cap pressure (max-eventdeltas529/37/6, noOOM/kill). No resource stop hidden or
budget raised. A parameterized machine helper consumes published run_append/
arrayAddrStack lemmas and explicit pointer/header facts, then instantiates SAME
concrete fixture and all cells/stack observations. Passing fullfocused152jobs
peakRSS907432KiB, no new cap/OOMevents. Exact same runtime/cacheOFF/j1/parent/
child/reserve; preflight1689575424bytes and64MiB warm route forecast.

This closes a supported independent Source-operation→intrinsic→symbolic-word
application, not G32/G34 or a whole source compiler. General shapes, resolved
Source programs, physical byte/returndata transport, all-profile constructors/
target allocation failures, reference rebinding/delete, deep-copy/emitted loops/
recursive graphs, reserved memory-storage and final V10/Source/target chain remain
open. All original parents stay partial/blocked; Backfill advanced, not exhausted.

C34 final152guardedjobs and1071default/262TestSuite/SolKey377/131 wrapperexit0.
Strict automatic, complete fixture, layer/orphan/trust, lane699standardpins/
90modules, script corruption pass. Warm finalgate225280bytes disk growth, sampled
aggregateRSS1603364KiB, no new memory.max/OOM/kill events; older C31/C34failures
caused cumulative12GiBpeak and1051maxevents, all retained. Raw docs1 complete
public83byteequal/originalfrozenno-newFAIL11incoming; globalinventory1 remains
1058unrecorded=359publicinherited+699owned,0unsafe. Reserved global records unchanged.
Source finder/skeptic accepted actual hypotheses/nonvacuity/ownership/controls
with no defect. No global debt or lane completion waiver.

## Checkpoint thirty-five: actual default constructor and fresh identities

Reproduced original G33/BackfillA-B gap: C31 allocRef uses an explicit Data value,
not Source.zeroVal. SourceDefault now executes published zeroVal for dynamic Bool
array at existing fuel+2 and derives its ACTUAL allocRef empty object/returned
address. Existing fuel0 and1 timeout unchanged-state; quantified fuel+2 is the
actual operation input, not a raised interpreter/proof/test budget or profile
exclusion. Initial MemOK yields reached MemOK/RefOK via published constructor
proof. Actual Heap.allocDefault gives fresh empty-root SourceBoolMemoryAt, Keeps
and root lower ID bound. default_frame derives old represented contents through
BOTH builders, old typed IDs unchanged, actual new logical ID≠old ID and Source
fresh address≠old address from lookup/allocation facts. No global/reverse address
injectivity, final relation or liveness premise invented.

source_bool_default_word consumes published newArray_correct and
defaultArray_eq_allocate: actual intrinsic default declaration and compiled
allocator run, new complete word StateRepr/allocator/stack frame and fresh local
Source relation are conclusions. INITIAL word StateRepr/StructAllocatorRepr,
positive framebase, next-local capacity and cursor+1<W stay explicit. No new
allocator/emitter/reference constructor implementation. Dynamic empty primitive
case only; full all-profile/nested/default/size-failure obligations remain open.

Concrete existingTFF/sourceallocated state and independently proved allocator
provide a nontrivial old object. Actual Source default returnsfreshaddress1,
intrinsicHeap.allocDefault and actual default-declaration roots are empty;
the latter has freshID1 vsOLD0 and the former has derived fresh-root separation. Complete old/new Source tables TFF/TFF/empty, intrinsicvectors
TFF/TFF/empty, actual allocator-growth representation and MemOK, empty-root read0
panic, old pointer16 and newpointer20 are proved. Wordpositions0,1,2,5,16,17,18,19,20
become[21,16,20,99,3,1,0,0,0], preserving old header/elements/sentinel/stack42 and
advancing allocator to21. Same actual constructor program supplies the intrinsic
and word applications; no desired outcome assumed. Cross-growth observations
explicitly name the reached heap typing, preserving dependent indices.

A discriminating boundary consumes ACTUAL allocateArray_run: cursor=W-1/size0
still succeeds in the symbolic word model and wraps freecursor to0, violating
FreeMemory8 at0. It does NOT prove a physical EVM failure/revert; physical memory/
gas transport and checked allocation failures remain prerequisites. Source fuel2
constructor succeeds while0/1 timeout, all observations retained. No source
profile shape/resource case removed to fit the positive capacity certificate.
Read-only MemoryCompile and MemoryObjectConstructionCompile likewise require
reached capacity hypotheses; their premise is not discharged by this adapter.

Retained focused failures were published lemma argument order, dependent Sigma/
list congruence and missing explicit reached heap typing in a heterogeneous
observation vector; repaired without dropping values/weakening statements or
raising budgets. Final focused155jobs pass; nine new public standard-only guards.
Same runtime/lock/cacheOFF/serial-j1/12GiB-no-swap/16GiBparent; preflight1669353472
bytes,64MiB warm build/log/export forecast and unchanged512MiB reserve.

All original parents remain partial/blocked: G32 byte representation/returndata/
physical pipeline, G33 all-profile constructors/checked size-allocation failures,
G34 general Source paths/reference rebinding/delete, G35.01/.03/.04/.05 general
ABI/reference/storage/deep-copy/emitted traversal/recursive Source graph/liveness,
G35.02 reserved memory-storage and G35.06 final V10/Source/target composition open.
No wholelane/Source-syntax/externalcompiler/EVM claim; Backfill not exhausted.

C35 guarded155jobs and full1072default/262TestSuite/SolKey377/131 exit0.
Strict automatic, complete fixture, layer/orphan/trust, lane708standardpins/
91modules and script corruption pass. Final warm gate229376bytes growth, sampled
aggregateRSS1706320KiB, no new cap/OOM/kill events. Raw docs1 completepublic83equal/
originalfrozenno-newFAIL11incoming, globalinventory1:1067unrecorded=359inherited+
708owned,0unsafe. No global gate waiver; reserved registry unchanged. Both source
reviews accepted with no defect. All prior seals/failures retained.

## Checkpoint thirty-six: resolved Source indexed deletion syntax

Reproduced the remaining G34/Backfill application: C34 composed Source.deleteLoc,
not resolved RExpr/RStmt execution. SourceIndexedDelete now uses the EXISTING
typed Source local/index/delete syntax and actual evalE/evalLoc/execS interpreters.
Published amount_ok discharges the supported index operation domain. Initial
Source root/index locals and intrinsic root/index locals are aligned explicitly;
actual Source location evaluation, intrinsic Stmt.run deletion and compiled word
code success/final local heap relation/MemOK/stack/allocator preservation follow.
No evaluation oracle, desired final relation or Source syntax semantics was added.
The unchanged heapObj run proof is exposed to compose actual length/location runs.

Actual Source expression statements use EM.sub and return their reached typed
locals; deletion preserves those locals. Runtime index and two repeated Source
aliases are inhabited using the actual previously allocated TFF Source heap.
The intrinsic target has a real uint local compiled to mload, rather than an
index literal. Complete TFF→FFF vectors, Source statement normal return, other
alias ID0, final false read, word cells[0,1,2,5,16,17,18,19] becoming
[20,16,0,99,3,0,0,0] and stack42 are proved for both declared pipelines.
An exact endpoint runtime local is rejected during Source location evaluation,
before deleting. Source panic and symbolic word revert are separate observations,
not an encoded returndata/ABI or Source rollback equivalence.

The generic source/target theorem quantifies runtime index and object length with
existing validity only. Bool dynamic-array primitive selection remains explicit;
this does not establish all resolved Source programs, progress/calls/admission,
general reference paths/rebinding/delete, physical bytes or an entire compiler.
All original G32/G33/G34/G35.01/.03/.04/.05 parents and BackfillA/B stay partial;
G35.02 reserved memory-storage and G35.06 final V10/Source/target chain stay blocked.
All-profile construction/checked allocation failures, general ABI/reference/storage
transport, fresh deep-copy/emitted traversal and recursive Source graphs remain
open. No profiles/refusals/target predicates/budgets changed.

Retained C36 core01/03/05 and controls01 elaboration failures were repaired by
explicit monad reductions and published typed heap length unfolding, without
weakening statements. Controls02/03 pass158jobs with standard-only axiom output;
exact guard/final gates and independent reviews are recorded in the new handoff.
Preflight1649508352bytes,96MiB build/log/export envelope and unchanged512MiB
reserve; same capped serial cacheOFF runtime. Historical raw docs/inventory gates
remain failures, public-baseline equality is separate from frozen-base11incoming
findings. No compiler/EVM external execution claim.

C36 final guarded158jobs/full1073default/262Suite/SolKey377/131 exit0.
Strict automatic, complete fixture, layer/orphan/trust, lane723standardpins/
92modules and script-corruption controls pass. Final sampled aggregateRSS
1715168KiB,221184bytes warm disk growth, zero new memory.max/OOM/kill events.
Raw docs1 matches complete83public findings; frozen no-new remainsFAIL11incoming.
Raw globalinventory1:1082unrecorded=359publicinherited+723owned,0unsafe.
Independent finder found missing runtime-index WORD endpoint coverage; fixed with
actual index3 StateRepr and direct resolved_delete_word_bounds application. Both
source reviews accepted final hypotheses/control/ownership/scope without further
defects. Standard-only guards cover all15new public laws/controls; prior failures
and seals retained. No wholelane/physical-byte/SourceSpec completion claimed.

## Checkpoint thirty-seven: resolved default declaration statement

A full owned-source scan found C35 executes Source.zeroVal, but no result runs
resolved RStmt.declVar and returns its new typed local. SourceDeclaration now
executes the EXISTING execS/EM.sub/zeroVal operations. General success/error
composition exposes the actual reached heap; errors retain that heap rather
than assuming rollback. Source horizon is the published semantic parameter,
not a new admission or evaluation-depth cap. The whole horizon family stays.

source_bool_declaration_word composes actual dynamic Bool zeroVal with C35's
published intrinsic default declaration and word allocator certificate. The
actual resolved declaration returns a fresh reference CONS local; final
SourceBoolMemoryAt and full MemOK in that enlarged local context derive from
the actual constructor's RefOK/MemOK, not assumed postconditions. Initial word
StateRepr/StructAllocatorRepr, positive base, next-local frame capacity and
cursor+1<W remain explicit. General constructors/checked allocation failure
and full source admission/progress/call correctness are not discharged.

Both declared pipelines execute inhabited oldTFF/freshEmpty construction. The
new statement witness is identified with the EXISTING complete constructor
witness by equality of actual zeroVal runs, so all Source tables/intrinsic
vectors/word observations refer to the SAME reached heap, not two unrelated
existentials. Full SourceTFF/TFF/empty, intrinsicTFF/TFF/empty, oldID0/newID1,
oldpointer16/new20/free21, sentinel99/stack42 and wordcells
[21,16,20,99,3,1,0,0,0] are retained. New typed reference local is returned and
MemOK proved. All horizons0..2 timeout on the same nonempty old heap without
fabricating a local; no target-failure/physical-EVM conclusion follows.

Core01's dependent cons-value type ambiguity was fixed by explicit EXISTING
Source.Val type, no representation/refusal/predicate/budget change. Core02
and controls01 pass147/160jobs with exact standard-only axiom output; six new
public guards. Same capped warm serial cacheOFF runtime, preflight1621446656
bytes,96MiB warm build/log/export forecast and unchanged512MiB reserve.
Independent preliminary source finder/skeptic accepted actual interpreter and
initial/final hypotheses/nonvacuity/linked vectors/limits without defect; final
guard/gate/artifact receipts are separate.

All original queue parents remain partial/blocked: physical-byte/general heap
representation, all-profile construction/checked target allocation failures,
general paths/reference rebinding/delete, ABI/reference/storage transfer, fresh
deep-copy/emitted traversal/recursive Source graphs, reserved memory-storage
and final V10/Source/target composition remain open. No new semantics/compiler
or external EVM evidence and no queue exhaustion claim. Raw docs/inventory
failures remain failures; public-equal versus frozen11incoming separate.

C37 final guarded160jobs/full1074default/262Suite/SolKey377/131 exit0.
Strict automatic, complete fixture, layer/orphan/trust, lane729standardpins/
93modules and script-corruption controls pass. Final sampled aggregateRSS
1548392KiB,352256bytes warm disk growth, zero new memory.max/OOM/kill events.
Raw docs1 matches complete83public findings; frozen no-new remainsFAIL11incoming.
Raw globalinventory1:1088unrecorded=359publicinherited+729owned,0unsafe.
Both independent source reviews accepted final guards/proof/control/scope; finder
caught stale cumulative-checkpoint heading, corrected to37 with supported source
syntax/typed-local additions. No remaining source defect. Original wholelane
and externalcompiler/EVM obligations remain unfinished; seals retained.

## Checkpoint thirty-eight: resolved indexed assignment with actual RHS

Reproduced original G34/Backfill gap: C32 handles source location writes and
C36 handles resolved delete, but no owned result executed RExpr.assign. The
existing published Source evaluator reads RHS first, then receiver/index, then
writeLoc; the existing word writeLocalCode emits RHS, pointer, index. New
SourceAssignment composes exactly these operations, with INITIAL local RHS,
index and receiver alignment. No alternate assignment evaluator/IR/typed state,
conversion, payload oracle or emitter added. Local operands are pure: this
does NOT establish arbitrary effectful RHS/LHS order equivalence.

resolved_assign_word derives actual Source evalE and execS expression statement,
actual intrinsic Stmt.assignMem and published word writeLocal_correct run,
writeAddr success, final SourceBoolMemoryAt/MemOK/typed locals/word StateRepr/
stack/allocator. Initial SourceMemOK/heap relation, wordStateRepr/localalignment
and actual runtime index bound stay explicit. Helper actual write-run premise
is discharged by headline using published writeAddr/Sourcewrite adapter. Source
MemOK preservation consumes published writeLoc_memOK, not assumed preservation.
Bounds derive actual Source location panic and word revert separately from
initial runtime values, not returndata encoding or Source rollback semantics.

Inhabited bothpipeline controls add real uint index1 and Bool RHStrue locals to
oldTFF target/Source state with repeated Source aliases. Actual Source expression
returns true and expression statement normal oldlocals; intrinsic TFF→TTF and
actual other-alias read1true derived from reachedheap. Complete word positions
[0,1,2,3,5,16,17,18,19] become[20,16,1,1,99,3,1,1,0], stack42 preserved. This
materially distinguishes ignored/stale false RHS, default/deletezero and wrong
constantindex0. Runtime endpoint3 independently inhabits StateRepr and directly
applies resolved_assign_word_bounds for BOTH Sourcepanic and compiledrevert.
All older source/constructor/delete/copy/reference/32/endpoint fixtures retained.

Core01 monad/implicitcontract/pure reductions and core02 redundant solved-goal
tactic failures retained; core03 passes147jobs. Controls01 missing explicit
primitive Bool type on published consVal was fixed without changing statements;
controls02 passes161jobs, six new public exact standard-only guards. Same idle
capped warm serial cacheOFF runtime, preflight1601703936bytes,96MiB forecast/
unchanged512MiBreserve. No budgets/profile/refusal/predicate/axiom changes.

Original G32/G33/G34/G35.01/.03/.04/.05 and both Backfills remain partial; G35.02
reserved memory-storage and G35.06 final chain blocked. Physical bytes/general
representation, all-profile constructors/checked target allocation failures,
general reference paths/rebinding/delete and ABI/reference/storage/freshdeepcopy/
emitted traversal/recursive Source graphs/whole Source-V10-target chain remain
unfinished. No external compiler/EVM or wholelane claim. Public source progress
interfaces are consumed read-only; complete SourceSpec/admission not inferred.

C38 final guarded161jobs/full1075default/262Suite/SolKey377/131 exit0.
Strict automatic, complete fixture, layer/orphan/trust, lane735standardpins/
94modules and script-corruption controls pass. Final sampled aggregateRSS
1605780KiB,225280bytes warm disk growth, zero new memory.max/OOM/kill events.
Raw docs1 matches complete83public findings; frozen no-new remainsFAIL11incoming.
Raw globalinventory1:1094unrecorded=359publicinherited+735owned,0unsafe.
Independent finder and skeptic accepted final six guards/proof/controls/docs and
pure-local scope with no confirmed defect. All prior seals/failures retained.
All original queue parents stay partial/blocked; no wholelane, externalcompiler/
EVM or independent-queue-exhaustion claim.

## Checkpoint thirty-nine: actual reached statement sequencing

Reproduced the investigated G34/BackfillB gap: C38 proves one resolved assignment
and C36 one delete, not an RItems program consuming their actual intermediate.
Existing execItems cons spends one semantic horizon per item; the first statement
in these certificates runs at horizon+5, second at horizon+4, entire list at
horizon+6. No budget/admission/fuel-depth restriction is introduced. Actual
Source.execItems, intrinsic Prog.run_cons_ok and word run_append_ok are composed,
with no new AST/interpreter/emitter/state semantics.

resolved_assign_delete_word and resolved_delete_assign_word derive both executed
steps and actual complete Source RItems/intrinsic Prog/word concatenation. The
SECOND certificate receives first reached SourceBoolMemoryAt/MemOK, intrinsic
withHeap and word StateRepr. Both bounds are INITIAL inputs; the reached second
bound is DERIVED from actual first writeAddr success/typed length preservation.
Initial locals alignment transports through derived unchanged locals. Final
local heap relation/MemOK/word StateRepr/aliases/stack and allocator compose; no
final relation, stagewise preservation or independent initial-state second run
is assumed. indexedWrite_elems/frame use EXISTING intrinsic typed operations,
quantified primitive/reference element families and arbitrary other object types.
They preserve structural fields, not deep child-content liveness or byte memory.

resolved_assign_delete_reject derives actual successful changed prefix followed
by second endpoint failure. Source error retains the ACTUAL reached prefix globals;
intrinsic program errors and word sequence reverts, with no unexecuted suffix
heap fabricated. Panic payload and word revert are separate observations, not
returndata/ABI/rollback equivalence. Generic actual-statement success/error
composition helpers are discharged in these concrete operation applications.

Both declared pipelines execute same-cell TFF→TTF→TFF versus TFF→TFF→TTF from
the SAME input, with real uint-index and Bool-RHS locals. Each control exposes
both writeAddrSome and Source statement Some steps plus Source RItems, intrinsic
program and each reached/concatenated word run. Complete heap and word vectors
are retained; otherAlias actually resolves to mem(0,1) and reads final false/true.
sequence_order_counterexample derives actual noncommutation (word18=0 vs1), not
a final-agreement premise. Distinct runtime deletion index0 gives TFF→TTF→FTF
while retaining assignment at1, untouched locals/header/sentinel99/stack42.
Endpoint3 follows a successful TTF prefix and exposes exact Source/intrinsic/word
rejections plus prefix heap/word vectors. Horizon5 likewise completes material
assignment then times out resolving delete, whereas0 times out before writing.
Source timeout is not target gas/failure/rollback. Pure local operands only; no
arbitrary effectful RHS/LHS ordering or whole compiler claim.

Core01 opaque withHeap length rewrite was repaired by exposing the actual heap;
core02/03/04 pass. Controls01 nested tactic layout and controls03 Fin0/address17
equality failures retained, fixed without changing observations. Controls05
strengthened statements with explicit actual prefix runs, eliminating unused
existential; controls06 passes162jobs. Eighteen new public exact standard-only
guards, same capped serial cacheOFF runtime, preflight1581473792bytes/96MiB
warm source/build/log/export forecast and unchanged512MiB reserve. Separate
preliminary finder/skeptic accepted actual reached sequencing/horizons/failures/
nonvacuity/purelocal scope without defect; final guarded/full/artifact receipts
remain separately recorded.

The existing goal is BLOCKED and unchanged by this authorized recovery turn;
no goal reset/reactivation/completion or competing continuation. Original G32–G35
and BackfillA/B remain partial/blocked. All-profile constructors/checked target
failures, general paths/reference rebinding/delete, physical bytes, ABI/reference/
storage/freshdeepcopy/recursive Source graphs, reserved memory-storage and final
V10/Source/target chain remain open. Raw docs/inventory failures are retained;
public-zero-new and frozen-base11incoming comparison stay distinct.

C39 final guarded162jobs/full1076default/262Suite/SolKey377/131 exit0.
Strict automatic, complete fixture, layer/orphan/trust, lane753standardpins/
95modules and script-corruption controls pass. Final sampled aggregateRSS
1692392KiB,229376bytes warm disk growth, zero new memory.max/OOM/kill events.
Raw docs1 matches complete83public findings; frozen no-new remainsFAIL11incoming.
Raw globalinventory1:1112unrecorded=359publicinherited+753owned,0unsafe.
Separate final finder/skeptic source reviews accepted 18exactguards, explicit
actual stageSome witnesses and same-input ordercounterexample with no defect.
Goal remains blocked, this authorized implementation turn is not reactivation.
Original queues and all prior seals/failures preserved; no wholelane claim.

## Checkpoint forty: nonprimitive reference-local rebinding

After C39, investigated actual Source.assign local reference/writeLoc.local and
published Evm.Memory.aliasLocal_correct/RefArrayStateRepr.setMem, not an absent
Source execution premise. New SourceAlias executes EXISTING typed Source local
assignment and expression statement, intrinsic Stmt.rebindMem and published word
aliasLocalCode. Initial Source local pointer/address, target typed HRef binding,
SourceMemOK, existing target mapFree and full RefArrayStateRepr are explicit.
Both heaps stay unchanged; new bindings/MemOK/full reference-array word ownership/
stack/allocator derive from existing operations. No distinctness premise: same
local/self-alias is supported. No fresh/deep copy or constructor implementation.

Precise boundary: Source STy/address and intrinsic RefTy/HRef parameters are
independent, so generic theorem is PARALLEL INITIAL-POINTER IDENTITY TRANSPORT,
not a cross-layer type-graph/deep-content representation theorem. It copies the
actual initial paired pointers on each side and preserves any initial heap
observations by unchanged heaps. It does not supply missing full graph/source
compiler alignment, reverse/global address injectivity or liveness premises.
The concrete nonprimitive witness independently aligns real nested input tables
and contents; it does not turn this generic parallel theorem into whole lowering.
Existing mapFree is retained, not a new admission exclusion or all-profile repair.

Independently inhabited intrinsic heap has childID0=TFF, old parentID1=[child0],
new parentID2=[child0,child0]. Actual Source allocRef calls create the matching
child and two parents, with DataOK/Top/Inner and MemOK structurally discharged.
No reference-constructor algorithm is implemented. Full primitive and reference
array word ownership, interval separation and initial allocator free32 are proved.
Actual Source/target operation changes dstID1→2 and pointer24→28, while backupID1/
pointer24 remains. Complete old/new pointer bindings, both parents' child-ID
lists and Source tables, intrinsic child TFF/TFF and all14 word cells are retained:
[32,24,24,28,99,3,1,0,0,1,16,2,16,16]→
[32,24,28,28,99,3,1,0,0,1,16,2,16,16].
Actual Source parent lengths2 versus backup1 and two-level parent→child reads
(memRef0 then true/false) derive from these reached tables. Heap/root counts3
unchanged, stale pointer24 is NOT the new destination, stack42 and concrete
allocator preserved. Self-alias gives exact same Source/target state and word
machine; semantic horizons0/1 timeout. These are not target gas/physical-byte
or general effectful ordering/ABI/compiler claims.

Core01 unavailable get-set lemma name repaired to actual TEnv.get_set; fixture01
opaque Heap.len reductions repaired explicitly; controls01 dependent Source type
length/child observation and self-alias cell specialization repaired without
weakening statements. Core02/fixture02/controls02/03 pass. Seven new public exact
standard guards; generic locals-get/set has NO axioms. Same capped warm serial
cacheOFF runtime; preflight1558994944bytes/96MiB forecast/unchanged512MiB reserve.
Separate preliminary finder/skeptic accepted actual semantics/initial hypotheses/
nonvacuity/parallel-identity boundary without defect; their suggested concrete
allocator application is now included rather than leaving a vacuous conditional.

Original G32–G35 and BackfillA/B remain partial/blocked: general type-graph memory
representation/paths, all-profile constructors/checked target allocation failures,
ABI/reference/storage/freshdeepcopy/recursiveSourcegraphs/physicalbytes, reserved
memory-storage and final V10/Source/target composition stay open. Raw docs/pins
remain actual failures, owned proposals separate. Existing goal BLOCKED and
untouched by this authorized turn; no reset/reactivation/completion/newgoal.

C40 final guarded158jobs/full1078default/262Suite/SolKey377/131 exit0.
Strict automatic, complete fixture, layer/orphan/trust, lane760standardpins/
97modules and script-corruption controls pass. Final sampled aggregateRSS
1551556KiB,233472bytes warm disk growth, zero new memory.max/OOM/kill events.
Raw docs1 matches complete83public findings; frozen no-new remainsFAIL11incoming.
Raw globalinventory1:1119unrecorded=359publicinherited+760owned,0unsafe.
Separate final finder/skeptic source reviews accepted sevenexactguards, concrete
allocator preservation and precise parallel-identity/graph-relation boundary
with no remaining defect. All old seals/rawfailures retained. Existing goal
BLOCKEDunchanged; authorizedturn progress is not goalreactivation/completion.
Original fullqueue remains partialblocked, no exhaustion/wholelane claim.


### C41 — initial aligned nested memory and actual alias observations

C40 deliberately kept Source and target initial identities independent. The new
`SourceNestedMemory` adapter supplies an INITIAL relation for the supported
existing dynamic memory parent-reference-array → Boolean-child shape:
`SourceBoolRefsAt` requires the actual Source heap parent table to contain the
actual intrinsic parent's selected child addresses, and actual Boolean child
contents for every selected child. It permits arbitrary runtime list lengths,
repeated/shared children and empty parents. It assumes no global address
injectivity, final representation, stagewise preservation or liveness. Distinct
Boolean observations derive local address separation (`child_address_ne`).

Nineteen laws derive actual Source length/index/read and resolved nested evalE
observations, exact parent/child bounds, and matching published RefArrayStateRepr
parent-pointer/Boolean cells and readArrayCode results for the SAME selected
child. `alias_word` executes existing source_alias_word and derives the reached
nested relation from unchanged Source/intrinsic heaps, with actual Source expr
and statement, intrinsic rebindMem, symbolic-word alias run, MemOK, ownership,
stack tail and allocator preservation. The two word load observations are
SEPARATE published loads, not a compiled nested-expression program.

Eight controls independently inhabit old=[left], new=[left,right,left], empty=[],
left=[true,false,false], right=[false,true,false] using real Source allocRef and
published full reference-array word ownership. Both pipeline values are quantified
in actual alias/nested evalE controls: rebinding selects right/false; stale old
binding fails at parent index1; choosing left gives true. Complete initial Source
tables, intrinsic arrays, identities, before/after word cells, shared identities,
untouched neighbour/free-pointer/stack are retained. Self-alias, exact endpoints,
actual resolved nested child failure and an arbitrary-list actual Source initial
witness are included; only intrinsic array validity bounds are required.

Independent read-only finder and skeptic preliminary reviews found no core defect;
both requested the now-added actual nested child-endpoint syntax control. No
reserved Source/Evm owner file or existing fixture vector was edited. All 27 new
public laws/controls have exact standard-only axiom guards. Per-file Lean MCP is
unavailable; bounded serial focused closure is used. C41 failures remain in unique
logs (dependent elimination/type annotation/opaque-heap/self-alias extensionality
repairs); no failed theorem or sorryAx is a deliverable.

Resource preflight retained the 512MiB reserve and forecast 96MiB source/warm
outputs/logs/compact exports against 1537122304 available bytes. Existing capped
runtime child12GiB/swap0 and parent16GiB remain unchanged. Actual child CPU quota
is unlimited (parent4 CPUs), so ALL C41 heavy execs additionally use taskset -c0
for inherited one-CPU affinity, alongside LEAN_NUM_THREADS1/Lean-j1. Optional
artifact cache stays OFF. Cumulative historical memory.max1051/session peak12GiB
are not per-exec measurements; new commands record their own RSS/event deltas.

This is finite supported initial observation and unchanged-heap alias transport,
not arbitrary recursive Source graphs, mutation alias reflection, physical bytes,
ABI, emitted nested paths, compiler/EVM testing or full-lane closure. Every original
G32/G33/G34/G35.01-.06 and Backfill A/B remains partial/blocked as before; reserved
memory-storage and final V10/Source/target prerequisites remain open. Raw global
docs/inventory failures and eleven incoming frozen-base docs findings are not
waived. Existing goal remains BLOCKED, unchanged by this authorized turn.

C41 final guarded159jobs/full1080default/262Suite/SolKey377/131 exit0.
Fresh Lean4.24.0/Lake5.0.0-src+797c613 and KeySort2jobs pass. Strict automatic,
complete fixture, layer/orphan/trust, script syntax/corruption and scoped
787standardpins/99modules pass. Final full sampled aggregateRSS1550404KiB,
233472bytes disk growth, zero new memory.max/OOM/kill events. Raw docs1 has
complete83findings identical to published baseline; frozen no-new remainsFAIL
11incoming, ownednew0. Raw inventory1:1146unrecorded=359publicinherited+787owned,
0unsafe. Exact owned proposals are external additive evidence, not globalpass.
Both independent source reviewers accepted proofs/controls and requested a
cumulative heading correction (fixed forty-one); their requested direct nested
child-endpoint control passed. A guard-format mismatch failure is retained;
all final exact axiom sets passed. Existing fixture vectors remain unmodified.


### C42 — actual selected-child reference rebinding

Continued original G34/BackfillB after C41 rather than stopping at its seal.
Published MemoryRefArrayPaths/Statements already proves RefPtrFrag.index,
run_of_eval and rebind, including actual index failure. `SourceNestedSelect`
consumes those existing certificates read-only, composing their existing code
with one local store; it introduces no path compiler, decoder, interpreter or
value/state layer. Six public laws connect actual independent Source
`dst = parent[index]` evaluation and statement execution to the actual intrinsic
rebindMem indexed path and a SINGLE existing word pointer-path/load/store run.
This improves on C41's separate observation loads, without claiming a compiled
arbitrary nested read program or the complete compiler pipeline.

Inputs are INITIAL SourceBoolRefsAt, Source parent/index local alignment,
actual intrinsic parent index Some child, Source MemOK and published full
RefArrayStateRepr/valIn fragment support. The selected payload is computed by the
actual Source table and intrinsic path; no final relation, conversion or graph
correctness premise is supplied. Derive reached Source child and parent observer,
MemOK, intrinsic/Source destination bindings, full word ownership, stack and
allocator. Bounds derive Source RHS failure before the local write, intrinsic
revert and actual whole word code revert separately. Insufficient horizons0..2
are actual timeouts for pure local operands; no proof/fuel budget is enlarged.

Three controls extend the SAME independently inhabited C41 fixture with one old
Boolean reference local pointing at left. Both pipelines execute actual indexed
selection of newParent[1], changing that local left→right and pointer16→24, then
derive the actual selected false read versus retained left true. Source expr and
statement, intrinsic indexed rebind, whole word sequence, complete C41 cells,
new local/parent/child pointer cells, heaps, neighbour and stack are checked.
Endpoint parent index3 rejects with old local/pointer unchanged; actual fixture
horizons0..2 time out. All C41 and older observation vectors/guards remain
verbatim. Arbitrary runtime lengths/indices remain those of the generic typed
interfaces; this concrete fixture is not an admission restriction.

Initial C42 implicit-contract/method-receiver errors are retained as actual
failed focused logs. Exact standard-only axiom guards, final gates and separate
read-only finder/skeptic source/artifact reviews are required. General reference
mutation alias reflection, physical bytes, all-profile constructors/target
failures, deep copy/ABI/storage/emitted loops/recursive Source graphs, reserved
memory-storage and final V10/Source/target remain open; queues partial/blocked,
no exhaustion or whole-lane claim. Existing blocked goal is unchanged.

C42 final guarded164jobs/full1081default/262Suite/SolKey377/131 exit0.
Fresh Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs and actual cacheOFF confirmed.
Strict automatic,complete fixtures,layers/orphans/trust,script syntax/corruption,
796standardpins/100modules pass. Full sampled aggregateRSS1563564KiB,
225280bytes disk growth,zero new memory.max/OOM/kill events. Parent16GiB and
child12GiB/swap0 remain unchanged; actual all heavy execs taskset-c0/threads1/j1.
Raw docs1 remains complete83publicfindings identical; frozen no-newFAIL11incoming,
ownednew0. Raw inventory1:1155unrecorded=359inherited+796owned,0unsafe,notgreen.
Both independent read-only source reviews passed without confirmed defects;
C42 heading forty-two verified. No original queue/goal completion or exhaustion.


### C43 — selected-child mutation and exact finite graph frame

Continued original G32/G34/BackfillB beyond C42. Actual Source.Heap.write_other,
intrinsic Heap.get_set_ne and published RefArrayStateRepr.setPrimitive /
writeArray_correct support a concrete selected-child write application. Three
laws in SourceNestedMutation derive parent/child Source address inequality from
INITIAL differently typed tables, then perform the existing Source.writeLoc and
intrinsic Heap.writeAddr and reconstruct the entire finite SourceBoolRefsAt
observer after the write. Source MemOK is derived from published writeLoc_memOK.
The word law certifies the SAME actual write with existing writeArrayCode and
full reference-array ownership after setPrimitive; it does not duplicate a copy,
constructor, path compiler, state or interpreter.

A sufficient INITIAL local footprint condition says each selected child whose
logical ID differs from the written child has a different Source address from
THAT child. Repeated written-child identities are allowed; other children need
not be pairwise distinct. This is neither global injectivity, a desired final
relation nor a source-profile restriction. Independent reviewers correctly noted
it is not universally necessary: no-op writes can preserve agreement without
separation. The module wording now explicitly says sufficient. General graph
mutation requires establishing the appropriate initial alias relation, still open.

Four controls retain every C41/C42/earlier vector. The actual shared left write
TFF→FFF updates both repeated selections in parent[left,right,left], while right
FTF, all parent IDs/fields, old aliases, neighbour/free-pointer/stack remain.
Actual Source/intrinsic/word execution and complete resulting word cells are
checked. A generic actual Source builder witness instantiates the theorem for
arbitrary runtime lists containing the written leaf, with only intrinsic length
validity. Empty/no-selected-member is outside that selected-member theorem only,
not an excluded source shape. Exact child endpoint3 produces Source panic,
intrinsic None and word revert, without a fabricated successful suffix heap.

The negative uses actual Source allocRef, initial Source MemOK and independently
inhabited read correspondence: two DISTINCT intrinsic children TFF/TFF share one
Source address. A material write makes the Source cell FFF, intrinsic left FFF
and right TFF. Source MemOK remains true, parent pointers stay fixed, but the old
nested correspondence is false by an actual wrong inner read. This proves the
initial read observer alone cannot justify every mutation; it is not an exclusion
or an assertion that the sufficient separation premise is necessary for no-ops.

Scope: selected explicit Source child location plus published word base/read/write
certificate, not resolved nested-write syntax or composed pointer-path-to-write
compiler closure. Arbitrary recursive graphs/physical bytes/deep-copy/ABI/general
storage/source/V10/target/reserved memory-storage obligations remain open. All
original Work/Backfill parents partial/blocked; blocked goal unchanged. Focused
failures are retained, no proof/resource budget or old fixture changed.

C43 guarded165/full1082default/262Suite/SolKey377/131 exit0. Fresh versions and
KeySort2jobs pass with artifactcacheOFF. Strict automatic,completefixture,
layer/orphan/trust,script syntax/corruption,803standardpins/101modules pass.
Full sampled aggregateRSS1734280KiB,disk229376bytes,new max/OOM/kill events0.
Raw docs1 COMPLETE83public findings identical; frozen no-newFAIL11incoming,
ownednew0. Raw inventory1:1162unrecorded=359inherited+803owned,0unsafe,notgreen.
Finder/skeptic final source reviews accepted real material collapsed-alias
counterexample, runtime lists and full positive frames; sufficient-vs-necessary
wording correction applied. No remaining confirmed defects. Prior focused
failures/format mismatches remain evidence, final guards contain no sorryAx.


### C44 — actual nested Source assignment and whole word path-to-write

The C43 handoff left resolved nested-write syntax and the composed pointer path
open. Source/Eval assign/evalLoc, SourceNestedMemory.eval_parent_read,
RefPtrFrag.index/run_of_eval, simple_sim, arrayStack_append_eq and C43's actual
write_child_word now discharge this supported application read-only. The new
owned SourceNestedAssignment module composes existing operations, introducing
no new AST/interpreter, heap/value layer, path compiler or constructor.

Eight public laws derive actual Source evalLoc(parent[i][j]), actual RHS-first
Source evalE assignment and expr statement, the intrinsic nested assignMem and
the WHOLE word sequence: compile current RHS, published parent/index pointer
path, compile current child index, existing writeArrayStackCode. Source actual
writeLoc is exposed as a reached witness. INITIAL table/content correspondence,
Source/target locals and actual parent Some child plus child bounds, Source
MemOK and full RefArrayStateRepr suffice; C43's sufficient INITIAL selected-leaf
alias footprint remains explicit. No final relation or write outcome is assumed.
Derive final finite observer, MemOK, full reference ownership, unchanged locals,
parent fields, stack and any existing allocator. No global/pairwise injection or
new source exclusion is introduced. Pure local operands do not establish general
side-effectful evaluation-order equivalence.

Parent rejection short-circuits before child index execution and needs no child
alignment premise. Child rejection reaches the real selected child. Both derive
actual Source panic bytes, intrinsic revert and whole word revert as SEPARATE
observations, no invented successful suffix/rollback. Horizons0..3 are actual
unchanged-state timeouts; success uses horizon+4 expression and horizon+5 stmt,
without changing any engine/proof/test/time budget or source profile.

Six controls extend the independently inhabited C41-C43 fixture; every prior
body/vector/guard is retained verbatim. Main parent[0][1]=true materially changes
shared left TFF→TTF, rightFTF unchanged. Actual Source location/expression/stmt,
intrinsic assignment, whole code, parent/repeated IDs, two-level reads, complete
word cells/neighbour/free-pointer/stack and derived observer are checked. Swapped
current indices select right and yield leftTFF/rightTTF and DIFFERENT word cells;
stale old parent index1 actually rejects. Current false RHS gives false output,
leftTFF/rightFTF and different destination word, so stale true payload/ignored
stack input cannot satisfy the controls. Ordered Source RHS/parent and word
RHS→pointer→index→write prefixes preserve the actual stack payload. Independent
parent/child endpoints and low horizons run the SAME assignment. Allocator
preservation has a real cursor48 initial/final StructAllocatorRepr witness, not
just a conditional with no inhabitant.

Per-file MCP/goal APIs unavailable; existing bounded serial focused checks used,
no goal mutation/recreation/reactivation. Initial focused errors (Except.pure
reduction, fixture annotations/parentheses/shadowed names, explicit word-base
rewrite) retained in distinct logs; final laws have exact standard-only guards.
Resource preflight:1472573440bytes,96MiB growth forecast,512MiB reserve; same
child12GiB/swap0 under parent16GiB, actual inherited CPU0 affinity, threads1/j1,
artifact cacheOFF, no source/cache/seal deletion or replacement runtime.

This closes only the supported finite resolved nested assignment application.
General references/graphs/effectful operands/delete/rebinding, physical bytes,
all-profile constructors/checked target failures, deep-copy/emitted loops/ABI/
storage, reserved memory-storage and final V10/Source/target remain open. All
original Work/Backfill parents remain partial/blocked, no exhaustion or goal
completion claim. Required final gates and independent source/artifact reviews
remain distinct from external compiler/EVM testing.

C44 final guarded166/full1083default/262Suite/SolKey377/131 exit0. Actual fresh
Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs/cacheOFF verified. Strict automatic,
completefixture,layers/orphans/trust,script syntax/corruption,817standardpins/
102modules pass. Full aggregate sampledRSS1647268KiB,disk225280bytes,new max/OOM/
kill events0. Raw docs1 COMPLETE83publicfindings byte-identical; frozen no-new
FAIL11incoming/ownednew0. Raw inventory1:1176unrecorded=359inherited+817owned,
0unsafe,notglobalpass. Independent finder/skeptic source reviews pass all eight
laws/six meaningful controls with no confirmedremainingdefect. Every earlier
vector/guard/seal/failure retained. Existing goal remains BLOCKED unchanged.


### C45 — actual reached nested-write program composition

Continued original G34/BackfillB after sealing C44. SourceNestedSequence consumes
C44 plus existing SourceSequence RItems/Prog composition and Heap.len_writeAddr.
Two public laws execute the SECOND nested assignment at the FIRST actual Source,
intrinsic and word output. Derive the second parent lookup/alias footprint from
the first parent-field frame, second bounds from original bounds plus actual
length preservation, Source local alignment from unchanged locals, and carry
Source MemOK/finite observer/full RefArrayStateRepr. No second initial-state run
or desired reached relation is assumed. Source RItems horizon+7 executes first
stmt horizon+6 and second horizon+5; intrinsic Prog and appended whole word code
execute the same pair. Actual primitive write and machine-prefix identities are
exposed. Final locals/parent/stack and existing allocator are preserved.

Late-invalid-second law derives the REACHED rejection using the same interfaces,
including actual prefix heap/Source state/word machine and its observer/MemOK.
The actual Source error globals contain the changed prefix. Intrinsic/word
reversion provides no successful suffix heap; no Source/EVM rollback equivalence
or halt/returndata representation is invented.

Three controls retain every prior fixture/vector/guard verbatim. With current
parent index2 selecting the repeated left child, actual writes at child1 then
child2 give TFF→TTF→TTT, while rightFTF and all parent IDs, neighbour/free-pointer/
stack stay framed. Actual RItems, Prog, both word stages and concatenation have
complete ordered Source tables, child vectors and 22-cell word vectors; the
cursor48 allocator instance is applied. Executing the actual SECOND operation
on the INITIAL state instead gives TFT and a different word18, proving it cannot
replace reached-state composition. This is a frozen INITIAL STATE negative,
not frozen RHS recapture: the pure local RHS remains true. A separate nonempty
changed TFF→TFT prefix followed by child endpoint3 rejection verifies Source
error state and both intrinsic/word failures, without fabricating a suffix.

Scope remains two actual writes to the same selected child, arbitrary existing
runtime bounds/indices and sufficient initial local alias footprint, pure local
operands and the finite parent→Bool-child observer. Not arbitrary programs,
recursive Source graphs, physical bytes, ABI/deep-copy/emitted loops/wholepipeline.
Original G32/G33/G34/G35.01-.06 and Backfill A/B remain partial/blocked, no queue
exhaustion or goal completion. Same runtime/caches/caps/CPU0/threads1/Lean-j1,
cacheOFF and all proof/fuel/node/test/time budgets unchanged. New focused proofs
pass without changing existing semantics or expected observations.

C45 guarded169/full1084default/262Suite/SolKey377/131 exit0, fresh actual versions
and KeySort2jobs/cacheOFF pass. Strict automatic/completefixtures/layer/orphan/
trust/script syntax+corruption/822standardpins103modules pass. Full sampled
aggregateRSS1633328KiB,disk229376bytes,new max/OOM/kill events0. Raw docs1 remains
COMPLETE83publicfindings byte-identical; frozen no-newFAIL11incoming,ownednew0.
Raw inventory1:1181unrecorded=359inherited+822owned,0unsafe,notglobalpass.
Both independent read-only finder/skeptic source reviews pass without confirmed
remaining defect. Frozen INITIAL STATE wording verified; oldvectors/seals/raw
failures preserved. No new C45 Lean attempt failed; original goal BLOCKEDunchanged.


### C46 — actual resolved nested delete with independent default and unit return

Continued original G34/BackfillB after C45. SourceNestedDelete consumes existing
Source.delete/zeroVal/deleteLoc, C44 nested location, C43 whole finite mutation
frame and published RefPtrFrag/primitive word-array clear. Five laws prove actual
Source nested delete evalE and expr statement with Source.RVal.unit, intrinsic
nested deleteMem and the WHOLE constant-zero→pointer-path→child-index→write code.
No Boolean RHS ghost/local is needed: false comes from independent Source zeroVal
and existing intrinsic default, not emitted-target execution or a supplied value.
No alternate allocator/decoder/interpreter/path compiler or owner code is added.

INITIAL existing nested correspondence, actual root/index alignment and parent
Some child, runtime child bound, Source MemOK/full RefArrayStateRepr and the same
sufficient INITIAL selected footprint derive final finite observer/MemOK/word
ownership, unchanged locals/parent/stack and existing allocator. The condition is
not globally injective or universally necessary, and changes no source profile.
Parent and child rejection plus low horizons0..3 are proved independently; Source
panic bytes, intrinsic revert and word revert remain distinct, no suffix heap or
Source/target rollback equivalence fabricated.

Two controls use the ACTUAL C45 reached TTT child, then delete child2 to TTF,
retaining earlierchild1true/rightFTF and sharedparentIDs[0,1,0]. Source unit-return
expression and stmt, intrinsic clear, whole delete code and THREE-operation word
append all execute; complete Source child tables/reads, 22wordcells/neighbour/
freepointer/stack and cursor48 allocator are derived. The current Boolean RHS
local remains true while the cleared word becomes zero, discriminating delete
from accidentally reusing assignment's RHS. Both actual nested-delete endpoints
and insufficient horizons are checked in both pipelines. Every earlier control
body/vector/guard stays verbatim apart from one new owned import.

Per-file Lean MCP unavailable, bounded serial focused checks used. Initial C46
notation/dependent location/typed delete arity-inference failures remain retained;
final exact standard-only guards required. Same VM/runtime/12GiB-noswap/CPU0/
threads1/j1/cacheOFF and all original proof/fuel/node/TestSuite/time budgets.
This supports primitive Bool leaves in the finite nested shape, not recursive
reference-container deletion/general graphs/physical bytes/ABI/deepcopy/whole
Source/V10/target. All original Work/Backfill parents partial/blocked, existing
blocked goal unchanged, no completion or independent-exhaustion assertion.

C46 guarded170/full1085default/262Suite/SolKey377/131 exit0. Fresh actual versions/
KeySort2jobs/cacheOFF pass. Strict automatic/completefixtures/layer/orphan/trust/
script syntax+corruption/829standardpins104modules pass. Full sampled aggregate
RSS1598884KiB,disk241664bytes,new max/OOM/kill events0. Raw docs1 COMPLETE83public
findings byte-identical; frozen no-newFAIL11incoming,ownednew0. Raw inventory1:
1188unrecorded=359inherited+829owned,0unsafe,notglobalpass. Both independent source
reviews pass without confirmed remaining defects. Proposed current feature IDs:
memoryLocation,memoryAliasing,rangeAccess,deleteExpression (supported-case evidence
only, no parent/feature completion). Every older vector/guard/seal/failure retained.
Original goal remains BLOCKED unchanged; no independent-exhaustion claim.


### C47 — parent reference-slot redirection and reached nested mutation

Investigated original G34/BackfillB gap against actual published Source.memSet/
assign, RefArrayRepr.write/set and RefArrayStateRepr.setReference: prior local
rebinding and primitive child writes did not update a parent reference slot.
SourceReferenceWrite derives the canonical new parent table from INITIAL runtime
contents and the already represented child's identity. SourceReferenceAssignment
proves actual RHS-first resolved Source evalLoc/evalE/expr-statement, intrinsic
assignMem and the WHOLE existing reference-pointer/index/writeArrayStack sequence.
No new pointer compiler, allocator, evaluator, decoder, value/state or deep-copy
operation is introduced. Both Source and target execute independently.

INITIAL SourceBoolRefsAt, the supplied existing child's INITIAL SourceBoolMemoryAt,
aligned parent/RHS/index locals, real runtime bound, MemOK and published full
RefArrayStateRepr derive the reached observer/MemOK/full word ownership, exact
parent elements, every Boolean intrinsic object and every INITIAL represented
Source Boolean alias (even a removed child). Source locals, ex (world/transient/
storage/journal), events/logs/fnLocals remain unchanged. Parent/Boolean address
separation follows incompatible existing typed tables, not global injectivity.
Other reference parents are not globally framed without their own local address
facts. The finite observer does not establish arbitrary Source graph liveness.

The old StructAllocatorRepr owns primitive/struct intervals, not reference arrays.
reference_slot_allocator therefore explicitly needs THIS parent interval below
its cursor, alongside actual reference ownership and successful slot bound. This
is a local allocator theorem premise, not an admitted-source restriction. A real
cursor48 fixture discharges it and the subsequent reached primitive delete frame.

The C41-C46 populated fixture is preserved verbatim. Actual assignment redirects
parent entry0: [left,right,left] -> [right,right,left], preserving both child tables
TFF/FTF and old parent[left]. Then actual reached nested read sees right=false;
reached nested delete of right[1] yields FFF while left TFF and its retained aliases
remain unchanged. Complete ordered Source parent/child tables, IDs, 22 wordcells,
RHS pointer cell, neighbours/freepointer/stack, Source context and allocator are
checked under BOTH pipelines. Separate controls show successful same-pointer
redirection, true parent endpoint Source panic versus intrinsic None/word revert,
low horizons0..2 and stale-pointer/wrong-child/initial-state reuse negatives.
The runtime repetition family constructs actual Source inputs and executes the
write for arbitrary n+1 < 2^256, no new payload/depth admission cutoff; this bound
is intrinsic validity and indices32 are not physical-byte encoding.

Per-file Lean MCP and goal RPCs unavailable; bounded serial focused closure used,
existing goal BLOCKED unchanged. All failed type/irreducible/dependent guard and
exact-axiom formatting attempts are retained; final guarded closure passes172jobs
with14 new exact standard-only pins. Allocator frame uses propext/Quot.sound;
other new public results use the existing standard trio, no sorryAx deliverable.
Original budgets/12GiB-noswap/CPU0/threads1/Lean-j1/cacheOFF unchanged. This is
supported pointer rebinding, not fresh construction, deep-copy, physical bytes,
ABI/emitted EVM/general graph/whole Source-V10-target proof. ALL original queues
remain partial/blocked; no whole-lane or independent-exhaustion claim.


C47 finder/skeptic source reviews found no mathematical defect; both identified
one overprecise runtime comment (index0 write in a33-element parent is not an
index32 selection). Corrected to retained entry32; no proof/fixture change. Bound
controls certify actual Source syntax, intrinsic writeAddr None and existing
writeArrayCode revert, not a generic whole referenceWriteCode rejection theorem.
A refined full rerun follows this comment correction; first full pass retained.


C47 refined full02:1087default/262Suite/SolKey377/131 exit0; fresh actual
Lean4.24.0/Lake5.0.0-src+797c613 and KeySort2jobs/cacheOFF pass. Strict automatic,
completefixtures, layer/orphan/trust, lane/script corruption and843standardpins
106modules pass. Full02 aggregateRSS1719508KiB,disk253952bytes,new max/OOM/kill
0; historical session peaks/events remain separately retained. Raw docs1 still
COMPLETE83findings byte-identical to public; frozen no-newFAIL11incoming,ownednew0.
Raw inventory1:1202unrecorded=359publicinherited+843owned,0unsafe,notglobalpass.
All2506 prior seal records verified unchanged. Every earlier fixture body/guard
verbatim verified. Finder/skeptic source mathematical PASS and comment fix applied;
committed artifact review follows. Original goal BLOCKED, all original queues
partial/blocked, no independent-exhaustion or external compiler/EVM test claim.


### C48 — actual parent-redirection/nested-delete programs and reached rejection

Continued original G34/BackfillB after committed/sealed C47 rather than stopping
at its separate operation witnesses. SourceReferenceSequence consumes the SAME
actual resolved assignment and nested delete certificates to prove Source RItems
execution, intrinsic Prog and complete appended word code from INITIAL facts.
The second selected identity is derived from the first actual list.set/get_self,
its child capacity from the first real Boolean object frame, and its footprint
from initial membership-in-set. No initial-parent pointer is frozen as the second
selection, no desired postrelation or stagewise preservation is assumed.

INITIAL parent/new-child correspondence, pure aligned locals, actual first bound
and new-child bound, MemOK/full word state are explicit. Successful child mutation
uses the same sufficient INITIAL local selected-footprint condition; transport
includes the newly installed self alias. This condition is not necessary in all
no-op/removed-child cases and is not a source restriction. Actual late child-bound
error needs NO such footprint because it does not mutate the child. Source
statements use horizons n+6 and n+5, RItems n+7, matching published fuel-consuming
cons rules; intrinsic Prog and word append use their actual reached states.

The final finite observer/MemOK/full word representation, parent fields and old
locals/stack are derived. Allocator composition preserves the explicit initial
live-parent interval<=cursor bound (the older allocator does not own reference
parents). The populated control directly applies THIS returned composed allocator
clause to the inhabited cursor48 initial allocator, not a supplied final frame.

Three controls quantify BOTH pipelines and retain every earlier control/body/
vector/guard verbatim. Real RItems/prog redirection then right-child clear preserves
left and parent[1,1,0], checks all INITIAL/redirected/final leaf vectors and all
22 wordcells/neighbour/freepointer/RHS/stack. A true invalid second index3 follows
successful pointer16->24 redirection, exposes redirected Source globals and full
initial/reached word/leaf vectors, but no successful suffix heap. A separate
horizon6 control actually completes redirection then times out in reached delete;
the unfuelled word program still succeeds. Timeout, panic, intrinsic/word revert
and successful execution are deliberately DISTINCT observed results, with no
fabricated timeout/revert/rollback equivalence or changed budget.

Generic2laws and3controls exact standard-only guards pass in173-job closure.
Per-file Lean MCP unavailable; first allocator heap-equality and control uint
RefOK/ReprV failures retained, final successful checks use unchanged bounds.
Same runtime/caches/12GiB-noswap/CPU0/threads1/j1/cacheOFF, no reset/newgoal/runtime,
owner edits or integration. Original G32/G33/G34/G35.01-.06 and BackfillA/B remain
partial/blocked. This is finite Bool-reference parent program composition, not
arbitrary graph/delete/reference-copy/physical-byte/ABI/emitted loop/whole Source
or Source-V10-target closure. No independent-exhaustion claim.


C48 final173guarded/full1088default/262Suite/SolKey377/131 exit0; fresh actual
Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs/cacheOFF pass. Strict automatic,
completefixtures, layer/orphan/trust, script corruption and848standardpins107mods
pass. Full aggregateRSS1569740KiB,disk245760bytes,new max/OOM/kill events0;
cumulative historical session peaks/events retained separately. Both source
finder/skeptic PASS, allocator-control suggestion applied, no confirmed remaining
defect. All2591 C47 seals verified unchanged and previous control prefix exact.
Raw docs1 COMPLETE83publicfindings byte-identical; frozen no-newFAIL11incoming,
ownednew0. Global inventory1:1207unrecorded=359publicinherited+848owned,0unsafe,
notglobalpass. Original goal BLOCKED unchanged, all Work/Backfill parents partial
or blocked. No Source/physical-byte/general graph/compiler/EVM completion claim.


### C49 — initial named struct layout and reached reference-field assignment

Continued original G32/G34/BackfillB using actual published Source.Resolved.member,
Source.evalE/evalLoc.member, Source.memSet Data.struct/DataList.setNth and existing
Heap.setField/MFields/MemoryRefWrite. Prior SourceBoolRefsAt covers a reference-array
parent, not named typed struct fields. New SourceBoolStructLayout checks actual
E.structFields names/positions/types against actual intrinsic named structDef;
SourceBoolStructAt independently observes existing Source Data.struct/DataList,
primitive uint tag and selected Boolean child contents. It is not a compiler or
postpreservation relation. The supported shape is exactly tag:uint at position0
and child:bool[] at position1, not an admitted-source restriction.

Actual Source member reads, setNth pointer write and resolved RHS-first assignment
expression/statement derive reached correspondence from INITIAL layout, parent/
new-child tables, local alignment, Source MemOK and existing word StateRepr.
The published intrinsic MPath.var mapFree premise is EXPLICIT, not assumed from
an unavailable whole profile theorem. Heap.setField supplies the typed pointer
update; published writeReference_correct, StateRepr.setReference,
RefFieldsRepr.setReference and StructAllocatorRepr.setReference supply whole word
code/ownership/stack/allocator. No pointer/compiler/allocator/reference-constructor
implementation or Source/Evm owner code is changed or duplicated.

Derived frames retain primitive tag, ALL intrinsic Boolean child objects and ALL
initially represented Source Boolean aliases, including the old deselected child;
Source locals/ex(world/transient/storage/journal)/events/logs/fnLocals remain fixed.
Struct-vs-Boolean table types derive needed address separation; no global injection
or graph liveness hypothesis appears. Existing struct allocator ownership supplies
its real live-interval framing; unlike array parents no extra invented cursor
premise is needed here. This does not prove all-profile allocation/capacity failure.

The populated actual Source declaration FlagBox and intrinsic spelled struct have
tag7, old TFF child and new FTF child, distinct addresses/IDs and shared parent
locals. Both pipelines execute member assignment, primitive/child reads and whole
word code; published PtrFrag.field runs follow initial16->reached24 through root
and retained self alias. A second actual assignment through that self alias stores
the already current pointer. Complete initial/intermediate/final Source tables,
logical IDs/leaf vectors and16 wordcells retain tag7, both children, neighbour99,
freepointer48, stack42 and actual allocator. Heap.next stays3, no deep-copy claim.
Wrong declaration names/positions and field types cannot supply typed member
evidence; raw wrong-type/missing-field reads are Source stuck, NOT fabricated
index panic/word revert. Low horizons0..2 are actual Source timeout observations.

runtime_children independently builds actual initial Source/intrinsic tables and
MemOK for arbitrary xs/ys with existing intrinsic length<2^256 validity, executes
the pointer write and proves EVERY valid read of both old/new child arrays. Empty
and element32 cases are covered by the runtime quantification without a payload/
depth cutoff. Universal fixed word layout is not claimed: the general word theorem
retains actual space/ownership premises. No physical-byte/ABI/Source-graph/emitted
copy correctness follows from these typed logical and symbolic-word observations.

Per-file Lean MCP unavailable; serial focused closure175jobs passes20 new exact
standard-trio axiom guards. Earlier namespace/typed cast/record/source declaration/
proof elaboration/guard-format failures retained. Source/word core stays below
elaborators, all old fixtures/guards unchanged. Full original G32/G33/G34/G35.01-.06
and both Backfill queues remain partial/blocked; no goal completion/exhaustion.


C49 final175guarded/full1091default/262Suite/SolKey377/131 exit0; actual fresh
Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs/cacheOFF pass. Strict/completefixtures/
layer/orphan/trust/script corruption and868standardpins110modules pass. Both
independent source reviews PASS, no confirmed remaining defect. Full aggregate
RSS1569540KiB,disk258048bytes,new max/OOM/kill events0; historical cumulative
peaks/events separate. All2643 old seal records verified; entire old Source nested
controls/guards unchanged. Raw docs1 COMPLETE83publicfindings byte-identical,
frozen no-newFAIL11incoming,ownednew0; global inventory1:1227unrecorded=
359publicinherited+868owned,0unsafe,notglobalpass. Original goal BLOCKED unchanged;
whole Work/Backfill scope partial/blocked, no independent-exhaustion assertion.


### C50: reached struct-member selection into an alias local

SourceStructAlias derives the selected existing Boolean child from INITIAL
SourceBoolStructAt and the actual intrinsic named field. Its actual Source
member-expression/local assignment, intrinsic rebindMem and whole published
PtrFrag.field/rebind word sequence select that same child; both heaps stay
unchanged. Explicit initial root alignment, mapFree, MemOK and StateRepr remain.
No initial destination-pointer agreement or final representation is assumed.

Controls select initial left into a local initially holding right, then compose
the actual C49 reference-field assignment with a reached member selection into
the retained old-left local. Actual Source RItems6, intrinsic Prog and full word
append derive right from the reached field. Complete three-stage word vectors,
local identities, both child vectors, Source reads, stack and allocator distinguish
stale destination/root/initial-state selection. Low-horizon rejection is actual
Source timeout; no unsupported panic or rollback claim. All C49 controls/guards
remain unchanged apart from one import and this appended family.

Serial focused closure176jobs passes seven new exact standard-only guards.
Earlier control proof-elaboration failures remain retained. Per-file Lean MCP
is unavailable. This is supported pure-local/two-field struct correspondence,
not arbitrary graphs, physical bytes, Source ABI, deep copy or compiler/EVM
execution. All original G32-G35.01-.06 and Backfill A/B parents remain partial
or blocked; fifty component checkpoints do not complete the lane or goal.

C50 final guarded176/full1092default/262Suite/SolKey377/131 exit0; fresh
Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs/cacheOFF pass. Strict/complete
fixtures/trust/layer/orphan/lane/script corruption pass;875standardpins111modules,
seven new exact standard-trio laws/controls. Independent finder/skeptic source
reviews PASS. Full aggregate RSS1567288KiB, new max/OOM/kill events0. All2713
C49 seal records unchanged; old controls prefix independently compared unchanged.
Raw docs1 retains83 complete public-identical findings; separate publiczero-new0,
frozen no-newFAIL11incoming. Raw inventory1 remains1234unrecorded=359public
inherited+875owned,0unsafe; coordinator additive proposal is not a globalpass.
All original queue parents remain partial/blocked, existing goal BLOCKED unchanged.
Further actual member-to-child index/write/delete applications remain to investigate;
C50 proves reached local selection, not general struct-child content execution.


### C51: actual struct-member-selected child indexing and mutation

SourceStructChild consumes INITIAL SourceBoolStructAt: the SAME existing
logical child comes from the actual named intrinsic field and Source declaration
member position/type. Source member/index location and read/assignment syntax
execute independently; published PtrFrag.field/readArray/writeArray compose the
whole symbolic-word code. Root alignment, mapFree, MemOK, StateRepr and admitted
core target operand valIn/eval agreements remain explicit. No desired reached
representation, global address injection or new interpreter/compiler is supplied.

Actual mutation derives parent/primitive-tag/pointer framing from typed struct
versus array identity and actual Source object types. ALL other intrinsic objects
frame; Source framing covers DIFFERENT addresses. Distinct logical identities
collapsing to one Source address are not silently treated as disjoint. Selected
child correspondence/MemOK, locals/ex/events/logs/fnLocals, stack and allocator
follow actual operations; no deep-copy/liveness/physical-byte claim follows.

Controls use the existing independent populated fixture under both pipelines:
actual C49 reference assignment then C50 member selection, followed by actual
member-index assignment/statement on the REACHED state. Whole three-operation
word append and four complete word vectors show RIGHT FTF->TTF while LEFT TFF,
old alias0, tag7, neighbour99, cursor48 and stack42 remain. Source prefix calls
and final statement are explicit; this is not a three-statement Source RItems
composition theorem. Wrong initial child/stale member and skipped/wrong-child
mutation negatives discriminate the new result. Source panic bytes, intrinsic
None and symbolic-word revert remain separate observations; low-horizon read
timeout has no fabricated successful suffix/rollback.

Arbitrary runtime valid-index member reads execute before/after actual reference
assignment, including index32 WHEN valid. A separate actual runtime endpoint
location/assignment failure covers empty children too: valid-index quantification
alone would be vacuous there. Finder review identified this distinction; the
explicit endpoint application fixes it. No public payload/depth cutoff exists
beyond existing intrinsic validity. General word certificates retain real space/
ownership; no fixed fixture layout is claimed for arbitrary runtime lengths.

Focused guarded177jobs passes13 new exact standard-trio laws/controls. Earlier
failed reductions, one original-budget heartbeat stop and guard-rejected
elaboration-generated sorryAx attempts remain raw evidence; no budget/trust
shortcut was used. Per-file Lean MCP unavailable; existing serial capped closure
used. All C50 fixtures/guards unchanged except import/append. Fifty-one partial
component checkpoints do not close G32-G35 or Backfill A/B. Physical bytes, all-
profile construction/target failure, general reference graphs/paths/delete, ABI/
storage/deep-copy/emitted loops/reserved copying/final V10-Source-target remain
open. Existing goal BLOCKED unchanged, no exhaustion/completion assertion.

C51 final guarded177/full1093default/262Suite/SolKey377/131 exit0; fresh
Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs/cacheOFF pass. Strict/complete
fixtures/trust/layer/orphan/lane/script corruption pass;888standardpins112modules,
13 new exact standard-trio laws/controls. Independent finder/skeptic source
reviews PASS after fixing the runtime-empty coverage distinction. Full aggregate
RSS1631452KiB, new max/OOM/kill events0; cumulative historicalpeak separate.
All2765 C50 seal records verified unchanged; entire C50 control prefix unchanged.
Raw docs1 retains83 complete public-identical findings, separate publiczero-new0;
frozen no-newFAIL11incoming. Raw inventory1 remains1247unrecorded=359public
inherited+888owned,0unsafe; precise additive proposals do not make globalpass.
Existing goal remains BLOCKED unchanged; all original queue parents unfinished.
Next supported investigation: actual delete through the named member-selected
child using published Source.deleteLoc and existing word primitive-write/default
certificates. C51 assignment does not discharge that general deletion/path task.


### C52: actual named-member-selected Boolean child deletion

SourceStructDelete composes existing Source .delete syntax and member/index
evalLoc with published positive-fuel primitive zeroVal/deleteLoc. It returns
actual unit, not an assumed default-write result. The selected identity comes
from INITIAL SourceBoolStructAt; no independent desired child/postrelation is
supplied. Intrinsic Stmt.deleteMem uses the published primitive-delete/default-
assignment equality; WHOLE PtrFrag.field/index/default-write code executes with
explicit root/index alignment, mapFree, MemOK, StateRepr/space and valIn premises.
No Source RHS variable or invented default/conversion oracle is needed.

Actual writes derive parent/tag/pointer/selected-leaf correspondence, MemOK,
locals/ex/events/logs/fnLocals, stack and allocator preservation. ALL other
intrinsic objects frame; Source objects frame at DIFFERENT addresses. No global
injection, graph liveness, physical-byte or recursive-container-delete theorem
is claimed. General rejection separately proves actual Source panic bytes,
intrinsic None/Stmt revert and whole symbolic-word revert, with no suffix heap
or Source/target rollback equivalence. Low-horizon Source timeout is separate.

The inhabited control consumes C51's REAL changed mid after reference-field
replacement, member selection and Boolean mutation: selected RIGHT TTF clears
to FTF; retained LEFT TFF/localalias0 remains. Explicit reached Source prefix
calls/final deletion expression+statement, four-operation word append and FIVE
complete word vectors retain tag7/neighbour99/cursor48/stack42/actual allocator.
This is not a four-statement Source RItems theorem. An actual wrong retained-
local deletion clears LEFT instead, keeps RIGHT TTF and differs from correct
deletion; skipped deletion differs too. All previous vectors/guards are verbatim
apart from one import and the appended families.

Runtime valid-index applications consume an ACTUAL reference-write output for
arbitrary xs/ys intrinsic-valid lengths, execute Source delete and read false
at the chosen index. A separate actual runtime endpoint panic/intrinsic None
application includes EMPTY children; this is not inferred from vacuous valid-
index quantification. General word theorems retain real word-space premises;
no fixed fixture address layout is asserted for arbitrary runtime payloads.

Focused closure178jobs passes nine new exact standard-trio guards; initial
published-constructor/type/default/dependent-match proof failures remain retained.
No budgets or axioms changed. Independent finder/skeptic source/control reviews
PASS, no confirmed remaining defect. Lean MCP unavailable; existing serial
bounded runtime used, optional artifact cacheOFF. G32-G35.01-.06 and both
Backfill queues remain partial/blocked; physical bytes/all-profile construction/
target failures/general types/recursive graphs/ABI/storage/deep-copy/reserved
copy/final V10-Source-target remain open. No independent-exhaustion or whole-lane
completion assertion; goal remains BLOCKED unchanged.

C52 final guarded178/full1094default/262Suite/SolKey377/131 exit0; fresh
Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs/cacheOFF pass. Strict/complete
fixtures/trust/layer/orphan/lane/script corruption pass;897standardpins113modules,
nine new exact standard-trio laws/controls. Independent finder/skeptic source/
control/guard/docs reviews PASS, no confirmed defect. Full aggregateRSS1740936KiB,
new max/OOM/kill events0; historical cumulativepeak remains separate. All2839
C51 seal records verified unchanged; C51 control prefix unchanged. Raw docs1
retains83 complete public-identical findings, separate publiczero-new0; frozen
no-newFAIL11incoming. Raw inventory1 remains1256unrecorded=359publicinherited+
897owned,0unsafe; additive registration proposals are not a globalpass. Goal
BLOCKED unchanged; every original queue parent remains partial/blocked.

Next investigated composition: actual Source RItems for a member-child write
then DELETE on its reached heap, reusing source_items_pair_run and intrinsic
heap-pair/word-append laws. C52 exposes linked expression calls but does not yet
prove that combined Source program; deriving second bounds/root/locals/word
representation from first output remains useful original G34/BackfillB work.


### C53: actual reached member-child Source program composition

SourceStructSequence closes a distinct supported G34/BackfillB application left
open by C52's individual linked calls: an ACTUAL two-statement Source RItems
member-child assignment then deletion, intrinsic Prog and whole word append.
The first assignment consumes INITIAL SourceBoolStructAt/locals and existing
word StateRepr. Its actual parent frame derives the same selected identity;
actual setElem length preservation derives second capacity, unchanged Source
locals derive root/index alignment, and target Simple operands retain their
evaluation through the heap-only change. Second MemOK/word representation comes
from the first certificate. No supplied desired intermediate/final relation or
independent initial-state second run is assumed. Final false read, parent frame,
stack and allocator composition derive from actual writes.

Horizon accounting uses the existing Source recurrence: first stmt n+6, second
stmt n+5, actual Items n+7. No prior fuel/test/proof budget is raised. Source pure
local operands and target core Simple expressions, same named field/index and
finite two-field existing-object observer remain explicit scope. This does not
prove arbitrary side-effectful order, unrelated statements, recursive graphs or
whole compiler/physical-byte adequacy.

Inhabited controls consume C52's actual reached state under BOTH pipelines.
The real Source Items7 and intrinsic Prog/word code materially execute RIGHT
FTF->TTF->FTF while LEFT TFF/oldalias0 remain; complete ordered Source tables,
three word vectors, parent/tag7/neighbour99/cursor48/stack42/allocator are kept.
The same Source program at horizon6 executes first stmt5 successfully then
actually times out in deletion, retaining the changed TTF intermediate heap;
horizon0 retains initial state. Actual reached true versus successful final
false reads discriminate skipped deletion. No successful suffix or rollback/
target-timeout equivalence is fabricated. All earlier fixtures/guards unchanged
apart from one import and appended families.

Focused guarded179jobs passes three new exact standard-trio laws/controls.
Initial length/state-wrapper/Sourcewrite witness/solved-goal proof failures are
retained; no trust/resource/budget changes. Per-file Lean MCP unavailable;
existing serial capped runtime/cacheOFF used. Every original G32-G35.01-.06
and Backfill parent remains partial/blocked; remaining physical byte/
all-profile construction/target failure/general reference/ABI/storage/deep-copy/
recursive Source/reserved-copy/final V10-Source-target requirements stay open.
Goal BLOCKED unchanged; no independent-exhaustion/completion claim.

C53 final guarded179/full1095default/262Suite/SolKey377/131 exit0; fresh
Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs/cacheOFF pass. Strict/complete
fixtures/trust/layer/orphan/lane/script corruption pass;900standardpins114modules,
three new exact standard-trio laws/controls. Independent finder/skeptic source/
control/guard/docs reviews PASS, no confirmed defect. Full aggregateRSS1572680KiB,
new max/OOM/kill events0; cumulative historicalpeak separate. All2899 C52 seal
records verified unchanged; entire C52 fixture prefix unchanged. Raw docs1
retains83 complete public-identical findings, separate publiczero-new0; frozen
no-newFAIL11incoming. Raw inventory1 retains1259unrecorded=359publicinherited+
900owned,0unsafe; additive proposal is not a globalpass. All original queue
parents remain partial/blocked, goal BLOCKED unchanged.

Further concrete investigation: actual named struct reference-field replacement
THEN a selected-child write/delete in one Source RItems program. C49 returns
the changed field and all old Bool-child frames; C51/C52 execute the resulting
selected child. Existing published statement-pair composition can be reused, but
C53 same-child write/delete does not yet discharge changed-selected-identity
program composition or general types/recursive graphs. No exhaustion assertion.


### C54: changed selected identity in one actual Source program

SourceStructRedirect composes actual named reference-field replacement with
deleting the NEW selected Boolean child in ONE Source RItems body, matching
intrinsic Prog and complete published word append. INITIAL finite struct and
existing new-child table observations, root/RHS/index alignment, mapFree, Source
MemOK, real StateRepr and Simple index/valIn premises remain explicit. The first
actual operation returns the changed field and preserves all Bool-child contents;
its actual frame derives the NEW child's capacity. Its Source locals and target
Simple evaluation remain stable, and its independent observer/MemOK/full word
representation feed stage two. No desired postcorrespondence or independently
initial second successful run appears as a premise.

Final selected identity/read/parent-tag/stack/allocator are derived. Other Bool
objects frame under logical inequality to the written new child. Preserving an
initial Source child observer also requires a different Source address: this is
a local theorem case, not global injectivity or a profile admission restriction.
Same-pointer cases remain allowed by the general theorem. Reference assignment
is pointer rebinding of an existing object, not a deep copy or constructor.

General rejection tests the NEW capacity after the real first operation. Source
RItems returns actual panic bytes with the changed prefix heap; intrinsic Prog
and whole word append revert, with no manufactured successful suffix, target
panic bytes or rollback equivalence. First stmt n+6/second n+5/Items n+7 use the
existing recurrence. A lower horizon control actually retains first replacement
before timing out; early horizon0 retains initial state.

Populated BOTH-pipeline controls redirect LEFT->RIGHT then materially clear
RIGHT[1] true->false, retain LEFT TFF/localalias0, tag7/neighbour99/cursor48/
stack42 and actual allocator. Complete ordered three-object Source tables and
THREE FULL16-word vectors are explicit. A separately inhabited Source/intrinsic/
word/allocator fixture makes LEFT nonempty and RIGHT EMPTY: old LEFT[0] is valid
and true, yet replacement then deletion fails against new RIGHT length0. Source
retains the actual replacement, Prog/wholeword reject; two full prefix word
vectors and tables preserve deliberately nonzero unused right payload cells.
A nonempty exact-end case and stale-old-child/skipped-deletion observations
remain distinct; all C53 and older bodies/vectors/guards are verbatim except
one import and appended controls. No new public runtime payload/depth cap.

Focused guarded180jobs passes six new exact standard-trio laws/controls; earlier
parent-state-wrapper and exact-end proof failures retained. Independent source/
control reviews PASS. Per-file Lean MCP unavailable; serial bounded runtime
used, cacheOFF, no budgets changed. All original G32-G35.01-.06 and Backfill A/B
parents remain partial/blocked: physical bytes/all-profile construction/target
allocation failures/general references/graphs/ABI/storage/deep-copy/reserved
copy/final V10-Source-target remain open. Existing goal BLOCKED unchanged.

Timing evidence is kept separate: current warm strict checking times ZERO new
TestSuite modules. Retained C31 cold log measured26 modules, maximum160s under
the original300s each. Exact current Suite import closure, AST fixture and
lean-toolchain (262 files) byte-match C31 commit3cfa818efae6460f4811b69165b9996a02d4e63b;
checkpoint54-testsuite-cold-key.json records the full hash key and actual raw
logs. This is retained cold evidence for that unchanged closure, NOT new timing
coverage or a cold measurement of the newly added MemoryOps proofs.

C54 final guarded180/full1096default/262Suite/SolKey377/131 exit0; actual fresh
Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs/cacheOFF pass. Strict/complete
fixtures/trust/layer/orphan/lane/script corruption pass;906standardpins115modules,
six new exact standard-trio laws/controls. Independent finder/skeptic source/
control/guard reviews PASS, no confirmed defect. Full aggregateRSS1573904KiB,
new max/OOM/kill events0; cumulative history separate. All2954 C53 seal entries
verified unchanged; old fixture prefix unchanged. Raw docs1 remains83 complete
public-identical findings, separate publiczero-new0/frozenno-newFAIL11incoming.
Raw inventory1 remains1265unrecorded=359publicinherited+906owned/0unsafe;
additive proposal is not a globalpass. Existing goal BLOCKED unchanged.

Current strict timing coverage is0 modules, NOT a new cold pass. Retained C31
26-module cold timings (max160s, original300s each) apply only to the exact
unchanged262-file Suite import/AST/toolchain key; actual current and retained
Lean/Lake version lines also match. Newly elaborated MemoryOps proof timings
and resource receipts are separate. No cache/source/seal deletion or time-budget
increase was used.

Next concrete G32/G33/BackfillB investigation: named struct INITIAL observer
transport across actual published Source.allocRef and intrinsic Heap.alloc,
using Heap.Keeps.field/len, MObj.elems_wk and Source.Heap.alloc_other. Existing
SourceMemory has a local Bool copy-schedule growth clause, not a full named
struct observer/fresh-root application. Derive old-reference weakening and
actual fresh Bool identity/content without assuming global address injection
or implementing reserved constructors. General allocation failure/physical
byte/full-profile/final-composition obligations remain open.


## Checkpoint 55: named observer across actual paired allocation (partial)

Concrete gap: the C54 finite named struct observer had no allocation transport.
[SourceStructGrowth.lean](../../Solidity/Backend/MemoryOps/SourceStructGrowth.lean)
now consumes the existing independent Source heap, intrinsic Heap/HRef/MObj,
Keeps and allocator interfaces. It introduces no allocator, value/state layer,
Source syntax/interpreter, profile restriction or global address injection.

- `SourceBoolMemoryAt.transport` and `SourceBoolStructAt.transport` require honest
  preservation of actual occupied Source cells plus intrinsic `Heap.Keeps`.
  Address-map agreement is needed only on valid old intrinsic IDs. Source locals
  and unrelated addresses need no additional constraint for these observers.
- `allocatedSourceAddress` changes only the genuinely fresh intrinsic identity.
  `allocatedSourceAddress_old` derives old-ID agreement with **no axioms**.
- `SourceBoolStructAt.alloc_bool` executes actual `Source.allocRef` and
  `Heap.alloc` on the supplied intrinsically valid Boolean array object. The
  Source payload is extracted from that object. Actual `alloc_fresh/get/other`
  and `Heap.keeps_alloc` derive old-cell preservation, exact fresh Source address
  and intrinsic identity, new contents, old named tag/child observations and
  `MemOK`. Every represented old alias differs from fresh Source `next` because
  its initial get is occupied; no map injection is assumed. Unused map entries
  remain unconstrained, except the one new-ID entry updated by the adapter.
- `SourceBoolStructAt.alloc_select_delete` uses that actual output for a real
  named reference-field `Source.writeLoc` and existing intrinsic setField,
  then resolved member-child Source deletion and the matching intrinsic address
  clear. Initial root/index locals and fresh-element bounds derive all reached
  operands, selection, capacity, `MemOK` and final correspondence. The generic
  theorem also frames every initially represented old Boolean alias through
  **both** replacement and final deletion using derived identity/address
  separation and actual write frames. There is no desired final relation,
  assumed second initial run or stagewise-agreement premise.
- `SourceBoolStructAt.default_word_growth` additionally applies the **existing**
  `source_bool_default_word` empty-default compiler certificate. Initial word
  StateRepr, StructAllocatorRepr, positive local base, fresh space and frame
  capacity remain explicit. Actual Source zeroVal/allocRef, intrinsic declaration,
  whole declareNewCode, old struct/new child observations, MemOK, word StateRepr,
  allocator and stack preservation all follow. This supported empty default
  does not imply nonempty/all-profile target allocation compilation.

The append-only [controls](../../Solidity/Backend/MemoryOps/SourceStructControls.lean)
retain all previous bodies and full vectors verbatim. Both pipelines exercise
arbitrary intrinsically valid runtime payloads, complete four-object Source
allocation tables, all typed fresh reads, old-ID agreement, occupied-parent and
alias preservation. A material fresh length-four FTTT child replaces old length-three
TFF; actual deletion at fresh index1 yields FFTT while old TFF/FTF aliases remain.
Complete allocation/replacement/deletion Source tables and intrinsic vectors
show every stage. Empty allocation is inhabited, not a successful element read;
logical element32 succeeds in a length33 payload and exact-end33 panics.
A wrong fresh map to occupied LEFT contradicts actual independent reads;
allocation alone still selects LEFT until the actual field replacement.
The empty-default word control supplies real initial representation/allocator,
full initial/final 16-word vectors, new local5/header48/free49, old tag7/children,
neighbour99, stack42 and final allocator certificate. No physical-byte meaning
is assigned to element32 or symbolic word cells.

The focused guarded closure passed 184 jobs. Six new public laws and five new
controls have exact standard-only guards; the old-map agreement law has an empty
axiom set, the other ten use propext/Classical.choice/Quot.sound. Failed proof and
control attempts remain in distinct checkpoint55 logs; no sorryAx survives the
passing guards. Per-file Lean MCP and goal read/update RPC are unavailable;
existing bounded serial checks are used and the BLOCKED goal is unchanged.

Independent finder/skeptic reviews confirmed the original generic old-alias clause
stopped at the replacement intermediate. It was strengthened to the final deletion
output using actual fresh separation and write frames, with no new premise.
Final documentation/artifact reviews and final gates are recorded in the handoff.

G32/G33/G34/Backfill B gain this finite independent Source allocation application;
all original G32-G35 and Backfill parents remain partial/blocked. Nonempty target
allocation, all-profile construction/checked allocation failures, physical bytes,
general graphs/paths/ABI/storage/deep-copy, reserved memory-to-storage and final
V10/Source/target composition remain open. Source.allocRef evidence is not a
Source new-expression/typing or whole Source-program theorem. Kernel and symbolic
word checks are not external solc/EVM validation. Global docs/inventory failures
are preserved separately from scoped/no-new comparisons; no reserved registry edits.


C55 final checks on this refined tree: guarded closure184, full default1097,
TestSuite262, SolKey377 parsed/131 read-bearing covered, final wrapper exit0.
Fresh runtime records Lean4.24.0 (797c613)/Lake5.0.0-src+797c613 and KeySort2jobs.
Strict/trust/layers/orphans/lane/complete fixtures/script corruption/diff checks
pass. Scoped917pins/116modules have zero unsafe sets; raw global inventory still
**exit1**,1276unrecorded=359published inherited+917owned (14original+345incoming
inside inherited). Proposed additions remain owned handoff evidence only.
Raw strict docs still **exit1**,83complete findings byte-identical to published
baseline (SHA2561905b6529ffff68bf2ee9256f84952fd8a19e0df94a434b3b052c11638142f2a);
separate publiczero-new passes, while frozen no-new remains **exit1**,11incoming.
No global failed gate is relabelled passed.

Current warm strict timed **zero** TestSuite modules. A fresh comment-aware
complete262-file Suite/fixture/toolchain key and actual matching Lean/Lake versions
verify retained C31 cold26timings/max160seconds under unchanged300seconds each;
this is retained evidence, not new cold timing coverage. C55 full aggregate
Lean/Lake peak RSS1650440KiB, disk growth266240bytes, new max/OOM/kill events0.
Historical cumulative12GiB peak/1051maxevents remain separately recorded. Child
12GiB/no-swap under parent16GiB, hostSwapTotal0 and OS headroom are preserved;
CPU0/threads1/Lean-j1/cacheOFF and every proof/test/time guard are unchanged.
All3014 C54 sealed records are verified unchanged before the C55 commit.

Both independent read-only finder and skeptic source/doc reviews passed; neither
ran Lean/server/builds. Artifact review is separately required after commit/export.
No whole-lane/goal completion or independent queue exhaustion is claimed. A next
supported original G32/G33/G34/BackfillB investigation is carrying the old named
observer through the ACTUAL Source default declaration's new local context, then
binding the new typed reference to the field via the reached resolved assignment.
Existing source_bool_declaration_word/source_decl_statement_run provide the
producer, but shifted Source/intrinsic locals and named observer context transport
must still be derived. C55 zeroVal/allocRef and reached delete do not prove that
Source RItems context-changing declaration/rebind program.


## Checkpoint 56: actual declaration then reached named-field assignment (partial)

[SourceStructDeclaration.lean](../../Solidity/Backend/MemoryOps/SourceStructDeclaration.lean)
closes the supported application absent from C55: `zeroVal`/`allocRef` in the
old Source context alone did not execute a context-changing declaration and
subsequent assignment. No existing producer, evaluator, AST, type or allocator
is replaced; all Source/Evm/constructor owners remain read-only.

- `SourceBoolMemoryAt.recontext` and `SourceBoolStructAt.recontext` transport
  the existing finite observers across **equal actual heaps**, without equating
  locals of different intrinsic Source contexts.
- `source_items_context_pair_run/error` use the actual `RItems.stmt` interface
  from input context Γ to reached Δ and then Δ to Δ. The error clause carries
  the actual reached global state; it constructs no successful suffix state.
- `SourceBoolStructAt.declare_assign_word` consumes the existing
  `source_bool_declaration_word` producer at its actual output, derives the old
  named observer via C55 real allocation transport and uniquely identified
  Source output, and recontexts it to the new cons local frame. The fresh Source
  RHS is `.here`; the old Source root is shifted by `.there`. Independently,
  intrinsic `TEnv.get_wk` derives the weakened old root and the fresh local;
  runtime word cells append the new local while retaining old cell positions.
  These are distinct indexing arguments, not a Source/target length assumption.
- That reached observer, actual fresh child contents, reached `MemOK` and word
  StateRepr supply C49's resolved reference assignment. Initial root alignment,
  mapFree, MemOK, StateRepr/StructAllocatorRepr, positive base, fresh space and
  new-local frame capacity stay explicit. Desired postagreement or an unrelated
  second successful initial run is never assumed. Final named tag/selected fresh
  child/empty capacity, every initially represented old Boolean alias, Source
  external state/events/logs/function locals, stack and actual allocator derive.
- The actual Source `RItems` program and intrinsic `Prog` each contain BOTH
  operations, and the target theorem executes the WHOLE declareNewCode followed
  by structReferenceWriteCode append. It retains separate declaration, reached
  expression/statement and code executions. Source horizons are: body n+6,
  declaration n+5, reached assignment expression n+3 and statement n+4. `RItems`
  retains ORIGINAL Γ.length as parameter count after declaration; the second
  statement is rederived from its actual expression at this count, rather than
  silently substituting extended-context length.

Append-only [controls](../../Solidity/Backend/MemoryOps/SourceStructControls.lean)
execute both declared pipelines with independent populated initial witnesses.
Actual declaration grows the Source context and heap, then the new local binds
fresh logical child3/base48 into the existing tag7 parent. Old children TFF/FTF
and retained alias0 survive. Three complete four-object Source tables and three
full16-word vectors include initial/mid/final parent pointers16/16/48, free
pointer48/49/49, all old headers/contents, neighbour99, new local5/header48,
stack42 and final allocator. Typed Source bindings and intrinsic env IDs record
fresh3 and shifted root2/oldalias0 separately; heterogeneous Source values stay
in typed products.

The inhabited stale-RHS run uses the shifted OLD RHS rather than `.here`; actual
Source/intrinsic/word execution binds child1/base24 instead of fresh3/base48.
It includes complete Source tables, three full16-word vectors and actual final
member reads1 versus3. Low Source body horizon5 REALLY completes declaration4
then times out in assignment3, retaining allocated cell3 and old parent data0;
body3/zero timeout retains the initial heap. The successful body6 reaches data3.
These are interpreter horizons, not admission/test-budget changes. A post-success
primitive Source read at fresh index0 panics, intrinsic index is None, and a real
target read suffix after the whole successful word prefix reverts. These scopes
are separate: no three-statement Source bounds program, matching panic payload,
successful suffix machine or rollback claim is manufactured.

Focused guarded closure passed187jobs. Five public laws and four controls have
exact standard-trio guards. All C55 control bodies and prior guards/vectors remain
byte-preserved apart from one import and appended new controls. Earlier failed
proof/control/guard attempts remain separately retained; no sorryAx survives the
passing guards. Lean MCP/goal read/update tools are unavailable; bounded serial
checks are used and the independently BLOCKED goal is unchanged.

Independent preliminary finder/skeptic source reviews found no math/ownership
issue; final source/control/docs and committed-artifact review receipts are in the
handoff. This is a G33/G34/BackfillB supported EMPTY-default program application,
not all-profile construction, nonempty allocator compilation, physical bytes,
general paths/graphs/ABI/storage/deep-copy or final Source/V10/target closure.
Every original G32-G35 and Backfill parent remains partial/blocked. No source
profile, exclusion, predicate, expected fixture, proof/fuel/node/time/TestSuite
budget or reserved global registry is changed. Kernel/symbolic-word execution
is not external compiler/EVM validation. Raw global docs/inventory failures and
complete frozen/public finding comparisons stay distinct from scoped checks.


C56 refined-tree final gates: focused187/full default1098/TestSuite262/
SolKey377parsed131read-bearing covered and final wrapper exit0. Fresh actual
Lean4.24.0 (797c613)/Lake5.0.0-src+797c613/KeySort2jobs pass. Strict, trust,
layers, orphans, lane, complete fixtures, script corruption and diff checks pass.
Scoped926pins/117modules have zero unsafe sets; raw global inventory remains
**exit1**,1285unrecorded=359published inherited+926owned (14original+345incoming
within inherited). Additive owned pin/feature proposals go only to the coordinator.
Raw strict docs remains **exit1**,83complete public-byte-identical findings
(SHA2561905b6529ffff68bf2ee9256f84952fd8a19e0df94a434b3b052c11638142f2a).
Separate complete publiczero-new passes; frozenno-new remains **exit1**,11incoming.
No reserved records or historical baselines are rewritten to mask failures.

Warm strict timed **zero** TestSuite modules. Independently unchanged262-file
Suite/fixture/toolchain bytes preserve the retained comment-aware import graph;
actual Lean/Lake versions match retained C31 cold26timings/max160seconds under
unchanged300seconds each. This is retained evidence, not new cold coverage.
Full aggregate Lean/Lake peak RSS1628420KiB, disk growth270336bytes, new
max/OOM/kill events0. Historical12GiBpeak/1051maxevents remain separately recorded;
child12GiB/no-swap under parent16GiB, hostSwapTotal0/OS headroom, CPU0/threads1/
Lean-j1/cacheOFF and all existing proof/test/time guards remain unchanged.
All3091 prior C55 seal records verify unchanged before commit. Separate independent
read-only finder and skeptic SOURCE/docs reviews passed; committed-artifact
reviews are separately required after export, without Lean/server/builds.

Further concrete original G34/BackfillB investigation remains available: the
current finite layout reads uint256 tag fields but has no owned resolved
primitive-tag member assignment adapter. Published Source.memSet/DataList.setNth,
Heap.setField, Memory.StructRepr.set/writeField_correct and PtrFrag.writePrimitive
provide independent interfaces to inspect for an actual Source/intrinsic/word
application while framing the reference child. This has not been implemented by
C56, and is not an independent-queue exhaustion assertion. All original physical
byte/all-profile construction/target allocation failures/general paths/graphs/
ABI/storage/deep-copy/reserved-copy/finalV10-Source-target obligations remain open.
The existing goal is BLOCKED unchanged; unavailable worker goal RPC is not
permission to reset, reactivate or complete it.


## Checkpoint 57: uint256 tag member write and reached three-statement program (partial)

Continuing the original G34/BackfillB queue after sealing C56,
[SourceStructTag.lean](../../Solidity/Backend/MemoryOps/SourceStructTag.lean)
implements the independently supported named primitive-member application that
C56 identified but did not implement. Existing Source/Evm/Scalar/constructor
owners remain read-only. The module composes existing typed operations and
compiler certificates; it introduces no evaluator, value/state layer, scalar
compiler, profile restriction or global address injection.

`source_struct_tag_write` proves the actual Source DataList.setNth0 update of
existing sourceBoolStructData, using its real declaration layout equality.
`SourceBoolStructAt.write_tag` derives the reached named observer, new uint tag,
unchanged selected reference, every old Boolean object's intrinsic contents and
represented Source alias, MemOK, locals, other Source addresses and world frames.
A represented Boolean Source cell differs from the struct parent because their
occupied types disagree; no address injection is required.

`SourceBoolStructAt.assign_tag_word` consumes INITIAL Source correspondence,
aligned Source root/uint RHS local, intrinsic root/current target value, mapFree,
MemOK, word StateRepr and existing valIn. Actual RHS-first resolved member
assignment and statement are proved independently of the target. The actual
intrinsic assignMem field step and WHOLE compileVal/root-pointer/field-write word
program follow the published PtrFrag.writePrimitive certificate. Reached
Source/word relations, selected child/aliases, Source world, stack and any supplied
allocator derive from those executions, never a desired postrelation. Source
expression n+3/statement n+4 and actual ≤2 timeout retain the existing horizons.
The finite layout has uint256 tag plus dynamic Boolean-array reference; this
adds no admission exclusion for other shapes or widths.

Append-only [controls](../../Solidity/Backend/MemoryOps/SourceStructControls.lean)
apply the theorem to EVERY existing canonical PrimTy.uint.Denote, with full
Source tables and initial/final16-word vectors, actual member reads, unchanged
TFF/FTF children and pointer0/tag/cursor/stack/allocator observations. Zero and
maximum2^256-1 are concrete instances; the maximum word is exactly W-1, with no
conversion correctness premise, truncation or new cap.

A further actual reached-state application consumes C56's REAL declaration and
fresh-reference binding outputs, then writes the tag. It proves one THREE-statement
Source RItems program, matching intrinsic Prog and WHOLE word append for all
canonical runtime uint values. Source original XΓ.length is6 while initial
intrinsic Γ.length is4; shifted Source bindings and word local cells remain
separate. The final tag statement is rebuilt from its actual expression at the
original Source parameter count. Complete FOUR four-object Source tables and
FOUR16-word vectors cover input/declaration/reference-binding/tag-write, including
old children, fresh empty child3/base48, tag7→value, neighbour99, new local5,
header48, free48→49, retained alias0, stack42 and final allocator49.

Discriminating negatives execute the existing raw Source memSet with uint at the
reference field, yielding exact stuck "field type" with no heap change. This is
a raw-interface test, not a well-typed resolved Source-program counterexample.
A raw word program using child offset1 really overwrites pointer33 and leaves
tag32 unchanged; complete initial/correct/wrong16-word vectors distinguish it
from the certified tag-offset0 program. It has no typed compiler certificate.
Actual low Source horizon2 timeout is kept separate from word behavior. All C56
and earlier bodies, full vectors, guards and failure prefixes remain verbatim.

Focused standard-guarded closure passed188jobs; four public laws and three
controls use exact propext/Classical.choice/Quot.sound guards. Distinct earlier
failed proof/control/guard attempts remain retained; no sorryAx survives the
passing tree. Per-file Lean MCP and goal read/update RPC are unavailable; the
existing capped serial route is used and goal identity/status is unchanged.

Independent read-only finder/skeptic core and refreshed control reviews passed;
final source/docs and committed-artifact reviews and raw commands are in the
handoff. Kernel and symbolic-word evidence does not establish physical bytes,
external solc/EVM adequacy, arbitrary side-effectful operands, general Source
programs/graphs, all-profile constructors/allocation failures or complete memory
compilation. All original G32-G35 and Backfill parents remain partial/blocked;
reserved memory-storage copying and final Source/V10/target composition stay open.
No source observations/profile/predicates/refusals or proof/fuel/node/time/test
budgets, global registry or historical checker baseline is changed.


C57 refined-tree final gates: focused188/full default1099/TestSuite262/
SolKey377parsed131read-bearing covered and final wrapper exit0. Actual fresh
Lean4.24.0 (797c613)/Lake5.0.0-src+797c613/KeySort2jobs pass. Strict/trust/layers/
orphans/lane/complete fixtures/script-corruption/diff checks pass. Scoped933pins/
118modules have zero unsafe sets. Raw global inventory still **exit1**,
1292unrecorded=359published inherited+933owned (14original+345incoming inside
inherited); owned proposals remain coordinator reconciliation, not registry edits.
Raw strict docs still **exit1**,83complete public-byte-identical findings
(SHA2561905b6529ffff68bf2ee9256f84952fd8a19e0df94a434b3b052c11638142f2a).
Separate publiczero-new passes; frozenno-new remains **exit1**,11incoming.
Warm strict timed **zero** TestSuite modules; independently exact262-file Suite/
fixture/toolchain bytes and actualmatching Lean/Lake preserve retained C31
cold26/max160seconds under unchanged300seconds each. No new cold timing coverage.
Full aggregate Lean/Lake RSS1675508KiB, disk growth266240bytes, new max/OOM/kill
0; historical12GiBpeak/1051maxevents remain separately recorded. Child12GiB/no-swap
under16GiBparent, hostSwapTotal0/OS headroom, CPU0/threads1/Lean-j1/cacheOFF and
all proof/test/time guards stay unchanged. All3159 C56 seal records verify before
commit; C56 and all earlier exports stay immutable. Both independent SOURCE/docs
reviews passed; committed-artifact reviews are separately required after export.

Original queue reassessment: G32/G33/G34/G35.01/.03/.04/.05 and Backfill A/B remain
partial, G35.02 and final G35.06 composition remain blocked on reserved/upstream
producer interfaces. No independent queue exhaustion is asserted. A further
supported G34 investigation is actual named uint256-tag DELETE: existing
Source.deleteLoc, primitive default interfaces and deleteMem_primitive_eq_assign
must be connected to the independent named observer and word default write.
C57 assignment and ≤2 timeout do not prove deletion or all-type defaults; that
application remains unimplemented. Full physical bytes/general paths/graphs/
ABI/storage/deep-copy/all-profile target allocation failures and final Source/V10/
target obligations stay open. Existing independently BLOCKED goal is unchanged;
no worker goal read/update RPC or authorization to mutate/reset it exists.


## C58: actual named uint256-tag deletion after reached construction/binding/write

This partial G34/Backfill B application implements the distinct deletion gap
identified in C57, in
[SourceStructTagDelete.lean](../../Solidity/Backend/MemoryOps/SourceStructTagDelete.lean).
SourceBoolStructAt.delete_tag_word starts with the independent INITIAL named
observer, aligned root locals, struct mapFree, MemOK and existing StateRepr.
Actual Source.deleteLoc consumes the positive-horizon uint256 zeroVal; its
Val.default agrees with intrinsic PrimTy.dflt.uint. The actual .delete member
expression returns unit, unlike assignment's value result. The theorem derives
expression n+3, statement n+4, intrinsic deleteMem and the WHOLE existing
compile-default/load-root/write-field program via the published primitive delete
agreement and PtrFrag.writePrimitive. No desired postrelation or assumed delete
execution is supplied. Tag zero, unchanged selected reference and all represented
old Boolean arrays, other Source addresses, locals/world, stack and allocator
frames follow. No address injectivity premise or new allocator/compiler exists.

The appended SourceStructControls bodies consume the ACTUAL C57 declaration,
reference assignment and tag-write output, including MemOK/StateRepr/allocator49.
The fresh local's Source cons context and target context are kept separate;
original Source parameter count XΓ.length remains fixed. named_tag_prefix_stages
reuses the producers at horizons n+6/n+5/n+4, deriving each actual reached stage
and intrinsic step. named_declared_tag_delete executes FOUR Source RItems
statements (horizon8, declaration7/reference6/tag5/delete4), intrinsic Prog and
WHOLE four-operation word append. Every canonical uint is quantified, including
zero and maximum, without a new admission cap. The selected fresh child is the
supported EMPTY default; old nonempty left/right children and aliases are framed.
Five complete16-word vectors expose all old cells, tag7→value→zero, parent child
pointer16→48, saved stack42/free49/local5/header48/neighbour99. The final two
complete four-object Source tables extend C57's retained four complete Source
stages; these are combined evidence, not a claim C58 repeats all five tables.
Fresh/retained Source identities3/0 and old TFF/FTF contents remain exact.

Nonzero9 and maximum distinguish skipped deletion. Actual SourceItems7 times
out only after the REAL declaration/reference/tag prefix, retaining that tagged
heap; expression horizon≤2 times out before tag deletion. These are Source
observations, not word timeout/rollback or panic-returndata equivalence. All C57
and earlier control bodies, vectors and guards remain verbatim. Two production
laws and three control/stage laws have exact standard-only axiom guards.
Focused closure passed189jobs after retained distinct failed proof attempts.
No sorryAx survives the passing refined tree. Lean MCP/goal read-update RPCs are
unavailable; neither limitation authorizes goal recreation or status mutation.

Runtime recovery was operational, not a proof pass: the same existing session
was stopped with retained exit255/OOMfalse and its transient /tmp lock directory
was absent (first lock command exit66). State/mount/diff metadata were preserved,
the absent lock directory restored and the SAME container started without a new
runtime/image, deletion or capacity change. Fresh Lean4.24.0/Lake5.0.0-src+797c613
and KeySort2jobs passed. The same child12GiB/no-swap under16GiBparent, CPU0,
threads1/Lean-j1/cacheOFF and proof/fuel/node/test/time guards remain enforced.
Restart resets the current cgroup counter epoch: current receipts must not be
conflated with separately preserved historical12GiBpeak/1051maxevents. Preflight
forecast96MiB above536870912-byte reserve was safe; sources/caches/seals retained.
Final gate commands/resources and independent read-only finder/skeptic source
and committed-artifact reviews are recorded in the C58 handoff.

All original Work/Backfill parents remain partial or blocked. This finite
uint256-tag/Boolean-reference Source/intrinsic/symbolic-word application does not
prove physical bytes, arbitrary layouts/graphs, all-profile constructors/target
allocation failure, ABI/storage/fresh deep-copy/emitted loops, reserved memory-to-
storage copying or final Source/V10/target composition. General tag operation
sequence applications and further primitive-array Source observations remain
possible investigations; no independent queue exhaustion is asserted. Existing
BLOCKED goal remains unchanged, independently of this productive manual turn.
Raw docs/inventory remain failed; complete-public zero-new and scoped axiom
proposals are separate checks, not global passes or reserved-registry edits.


C58 final reviewed Lean tree: focused189/full default1100/TestSuite262/
SolKey377parsed131read-bearing covered, wrapper exit0. Fresh versions and
KeySort2jobs pass. Strict/trust/layers/orphans/lane/complete fixtures/script
corruption/diff pass; exact938standard pins across119owned modules, zero unsafe
sets. Raw global inventory stays **exit1**,1297unrecorded=359published inherited+
938owned (14original+345incoming within inherited). Additive owned pin/localEvidence
proposals require coordinator reconciliation, with no reserved registry rewrite.
Raw strict docs stays **exit1**,83complete findings byte-identical to published
baseline SHA2561905b6529ffff68bf2ee9256f84952fd8a19e0df94a434b3b052c11638142f2a;
separate publiczero-new passes, frozenno-new **exit1** with11incoming retained.
Warm strict timed zero TestSuite modules; independently exact262file Suite/
fixture/toolchain bytes and matching actual versions retain C31 cold26/max160s
under unchanged300s budget, with no new cold timing coverage. Full aggregate
Lean/Lake RSS1564200KiB, disk growth266240bytes, new cgroup max/OOM/kill events0.
Current restarted-epoch session peak is separately retained; historical peaks/
resource stops are not erased or counted as new exec events. All3224 C57 seal
entries reverified unchanged. Both independent finder/skeptic SOURCE/docs reviews
PASS with no remaining findings; final committed-artifact reviews occur after
new additive export and are recorded in the sealed handoff. Source proof repairs
and all failed focused exits stay retained; no observation/budget weakening.

Queue reassessment against actual owned Source interfaces: uint256 tag deletion
now exists; no SourceUintMemoryAt/uint-array Source observation adapter was found
in the owned Source modules (immutable decoded uint transfers remain distinct).
Published Source primitive values, Data arrays, readLoc/memSet and intrinsic
uint-array paths are possible next independent G32/G34 producers to inspect,
not an implemented claim or evidence that all independent work is exhausted.
Physical-byte target transport/general Source graph/default/failure producers,
reserved memory-to-storage and final V10/Source/target remain genuinely missing
from this component. All original queue statuses remain partial/blocked; no
new admission/profile restriction, semantic answer or goal status change follows.


## C59: independent Source uint256 array observations and real snapshot provenance

After sealing C58, the original G32/G34/Backfill B reassessment found no existing
numeric Source heap observer. The next independent application is implemented in
[SourceUintMemory.lean](../../Solidity/Backend/MemoryOps/SourceUintMemory.lean),
with inhabited controls in
[SourceUintMemoryControls.lean](../../Solidity/Backend/MemoryOps/SourceUintMemoryControls.lean).
This is a typed INITIAL one-object correspondence over the EXISTING Source.Data
array/Source heap and intrinsic Heap/HRef/ArrTy. It reuses sourceUint and its
already proved calldataUint_sourceUint inverse exactly; no new conversion,
decoder, AST, heap or copy evaluator is introduced. Source array type is dynamic
uint256. Intrinsic dynamic/fixed ArrTy may observe its contents, which does not
establish Source fixed-array syntax/lowering or eliminate any other source shape.

Actual Source.memElem/readLoc bounds and exact value iff follow from initial
contents and the existing inverse, without a supplied result/conversion proof or
truncation. Natural indices and runtime list/schedule lengths have no added cap.
Actual published allocRef produces independent Source tables and MemOK with
structural conditions discharged. This is kernel allocation evidence, not new-
expression/declaration/emitted allocator correctness. Actual .indexArray syntax
from aligned root/index locals executes at n+2, deriving its location/read from
the initial observer, with unchanged Source state. Both declared pipelines are
instantiated for these pure-local operands; no general side-effect order claim.

The arbitrary existing runCaptures is executed at REACHED intrinsic heaps;
its captureOrigin read maps to actual INITIAL Source memory. This is explicitly
not a Source copy loop or a final unchanged-index Source observer. Heap.Keeps
transports primitive contents/old typed identities, and the published recursive
SVal.copyStToM builder plus arbitrary successful old-root recaptures yields BOTH
the actual copied recursive mirror and independent numeric Source read provenance.
mapFree and actual Some execution remain explicit in the generic law; concrete
controls discharge them with a real nonempty nested numeric tree and actual
schedule. No fresh Source entries or global address injection are manufactured.

Controls quantify runtime tail n and copy counts; n+3<2^256 is only the existing
intrinsic dynamic-object validity. Actual two Source allocations independently
establish [7,max,max] plus zero tail and separate [max,0] table/Source MemOK. Root
and retained local alias read the same object through actual resolved syntax at
EVERY valid runtime index in both pipelines. Initial numeric target arrays and
nonprimitive parent [root,neighbor,root] are explicitly populated. A real first
snapshot changes [7,max,max] to [7,7,max], breaks old-index Source correspondence,
and still matches computed origin0 read7 while Source index1 reads max. Arbitrary
many REAL existing break/repair cycles restore contents from INITIAL provenance,
with no desired final agreement premise. A published fixed reference-array copy
contains a nonempty numeric child [max,7]; after old-root schedules the copied
root/child contents and recursive mirrors, fresh logical lower bounds/old-root
non-aliasing, numeric neighbor and repeated old IDs[0,1,0] all derive. This is not
physical-address injectivity, recursive Source graph construction or emitted copy.

Additional actual controls cover logical elements31/32 in length33 with values
7/max, exact end33 Source read/indexLoc panic, horizon1 syntax timeout, zero/max
nontruncation and complete boundary values30/31/32/33=[0,7,max,none]. These are
ELEMENT indices, not byte-word encoding. An intrinsic fixed2 observation executes
[max,0]→[max,max] and refutes old-index Source agreement while retaining computed
Source provenance; the Source object remains dynamic. Empty Source arrays,
raw wrong-type/missing-object stuck results and an actual successful changed
snapshot followed by invalid reversed bounds remain distinct. Raw mismatched
readLoc controls are outside typed Source syntax, not source-profile exclusions.
Every prior fixture/body/vector/guard and every earlier seal stays unchanged.

Thirteen new production laws and eight control families have exact standard-only
axiom guards; focused closure passed154jobs after retained distinct proof failures.
Per-file Lean MCP/goal read-update RPCs remain unavailable; the same serial capped
runner is used without goal mutation. Safe96MiB growth envelope above536870912byte
reserve was measured before writes; the SAME12GiB/no-swap session under16GiBparent,
CPU0/threads1/Lean-j1/cacheOFF/proof/fuel/node/test/time limits and keyed warm caches
are retained. C58's restarted cgroup epoch remains distinct from historical peaks.
Independent read-only finder/skeptic source/artifact reviews and actual final
commands/resources are required and recorded in the C59 handoff. No public profile,
refusal/predicate/invariant/expected observation, budget or registry baseline changes.

Original queue remains unfinished: this advances numeric Source observations,
not numeric Source mutation or target compilation, all-profile construction/
allocation failures, physical bytes, general references/paths/graphs/delete,
ABI/calldata-storage/fresh deep-copy/emitted loops, reserved memory-to-storage or
final V10/Source/target composition. No independent queue exhaustion is asserted.
Raw docs/inventory failures stay failures; exact-public zero-new and additive scoped
pins are separate. The existing persistent BLOCKED goal remains unchanged.


C59 refined-tree final gates: focused154/full default1102/TestSuite262/final
SolKey377parsed131read-bearing covered, wrapper exit0. Fresh Lean4.24.0
(797c613)/Lake5.0.0-src+797c613/KeySort2jobs pass. Strict/trust/layers/orphans/
lane/complete fixtures/script-corruption/diff pass. Exact959standard pins across
121owned modules have zero unsafe sets. Raw global inventory remains **exit1**,
1318unrecorded=359public inherited+959owned, with0errors. The initial piped Node
output exited1 but truncated its final summary; that raw1084-line prefix is kept.
A justified capture repair reran the UNCHANGED checker directly into a new real
file, preserving the complete1319-line failure and final counts, not changing a
registry/baseline/policy or relabeling failure as success. Additive959pin proposals
remain coordinator reconciliation. Raw strict docs remains **exit1**,83complete
findings exactly public-byte-identical SHA2561905b6529ffff68bf2ee9256f84952fd8a19e0df94a434b3b052c11638142f2a;
separate publiczero-new passes; frozenno-new stays **exit1** with11incoming.
Warm strict timed0Suite modules; independently exact262-file Suite/fixture/
toolchain bytes and actual matching versions retain C31 cold26/max160s under
unchanged300s budget, not new cold timing. Full aggregate Lean/Lake RSS1663716KiB,
disk growth274432bytes, new max/OOM/kill0; current restart-epoch peak/cache and
older historical resource events remain separately preserved. All3284 C58 seals
reverify unchanged. Both independent finder/skeptic final SOURCE/docs reviews
PASS; committed-artifact reviews follow compact additive export. Every distinct
failed proof attempt remains retained, with no sorryAx in the passing tree.
A final metadata helper had a retained pre-execution Python syntax error before
any suffix ran; its corrected helper preserves all actual command outcomes.

Reassessment: numeric Source indexed reads now have a real producer; numeric
indexed write/delete/default-expression/target program composition remains a
further concrete G34 application requiring inspection of actual Source.memSet,
published primitive-write/delete and existing StateRepr interfaces. This is
identified as available investigation, not implemented or an exhaustion claim.
Full original G32-G35 and Backfill A/B remain partial/blocked, including real
reserved memory-storage/final Source-V10-target producers, physical bytes,
all-profile construction/failure/general-reference/graph/ABI/deep-copy obligations.
The existing BLOCKED goal is unchanged; no worker goal status mutation occurred.


C60 — numeric Source mutation and reached word composition (partial G34/Backfill B).
The new SourceUintWrite/SourceUintAssignment/SourceUintDelete/SourceUintSequence
modules consume the existing immutable INITIAL SourceUintMemoryAt and published
Source/Evm operations read-only. They derive actual memSet/writeLoc, resolved
RHS-first indexed assignment, deleteLoc's uint-zero default/unit, reached
correspondence/MemOK, untouched locals/world and distinct-object/address frames.
The two Source RItems statements, intrinsic Prog and complete word append execute
on the actual first output; second bounds follow preserved lengths, not an assumed
second result. The reverse order and genuine successful-prefix/late bounds failure
are separate actual executions. Source panic bytes, intrinsic revert and symbolic
word revert remain separately scoped; Option/errors do not imply rollback.

SourceUintMutationControls independently inhabits populated numeric heaps and
Source tables with retained aliases and a neighbor. Both pipelines execute actual
assignment/delete, with complete initial/intermediate/final intrinsic vectors,
Source two-object tables, all dynamic word contents and fixed sixteen-word frame
vectors (locals, alias/root, header, neighbor, gaps and free pointer), stack42 and
allocator96. Max/zero order controls distinguish a materially changed middle even
when final values equal the initial vector; logical31/32, empty/exact endpoint,
late rejection and low-horizon timeout are retained. The raw stale-pointer negative
violates INITIAL StateRepr explicitly, and changes the neighbor instead of the
represented root; it is not a compiler counterexample. The concrete fixture's
17+length<=80 separated word layout is a sufficient witness capacity, not a public
payload cap; generic adapter laws quantify arbitrary runtime lengths/indices.

C60 focused controls12 passes162 jobs with exact standard-only guards, aggregate
RSS1006644KiB and zero new OOM events. Distinct failed attempts are retained:
controls10/11 and diagnostic-full01 genuinely reached the12GiB cap and were killed
(Lean137; wrapper1/1/direct137), not proof passes. Guarded prefix diagnostics
isolated the remaining concrete stale-pointer proof normalization; replacing its
broad concrete simplification with a private symbolic-machine proof before
instantiation preserved every statement/vector and passed without any budget,
representation or runtime change. The current session cumulative OOM count3 and
peak12GiB remain historical failures, separate from passing-exec RSS/events.

Independent finder/skeptic read-only reviews of actual Source/intrinsic/word
operations and controls found no mathematical defect; their normalization concern
was confirmed by the passing isolated prefixes and repaired without weakening.
Final refined-tree gates and committed-artifact reviews follow below. This does
not close general paths/graphs/references, all-profile construction/target
allocation failure, physical bytes, ABI/storage/fresh deep-copy, reserved copy or
final Source/V10/target composition. Existing BLOCKED goal remains unchanged.


C60 final refined-tree wrapper exit0: default1107/TestSuite262/final SolKey377parsed,
131read-bearing allcovered. Runtime actual Lean4.24.0/Lake5.0.0-src+797c613 and
KeySort2jobs pass. Strict/trust/layers/orphans/lane/complete fixtures/script
corruption/diff pass; exact984standard pins in126owned modules pass scoped
validation. Raw global inventory remains **exit1**:1343unregistered=359public
inherited+984owned,0unsafeerrors. Raw strict docs stays **exit1** with83complete
findings, byte-identical to published baseline; separate publiczero-new passes,
frozenno-new fails with11incoming findings. No global record/baseline altered.
Warm strict timed0Suite modules, exact262source/fixture/toolchain bytes preserve
C31cold26/max160s<300s keyed evidence, not new timing coverage. Full aggregate
RSS1735856KiB, disk growth266240bytes, newOOMdelta0; cumulative current-epoch
max10719/oom3/kill3/12GiBpeak stays failed-history evidence. Both independent
finder/skeptic final SOURCE/control/docs reviews PASS, no confirmed remaining
findings; independent committed-artifact reviews follow export. Prior3346 C59
sealed entries reverify unchanged. All original queues remain partial/blocked.

Further original supported investigation: published Source.evalE.compound resolves
RHS then location once and reads the ACTUAL current cell; existing published
Evm.MemoryCompound implements intrinsic/word compound assignment. No owned
numeric Source compound update bridge exists. A useful next application requires
an independently proved exact Source.binVal/convRV versus intrinsic arithmetic
clause (including checked overflow), not an assumed desired arithmetic result.
No claim that independent work is exhausted or that these premises are already
supplied. General graph/physical-byte/all-profile/ABI/storage/deep-copy/reserved
copy/final composition remains unfinished and the existing goal stays BLOCKED.


C61 — actual numeric read/update/write after C60 (partial G34/Backfill B).
SourceUintCompound derives exact existing Source.binVal/intRes addition and
checked arithmetic overflow versus intrinsic compoundT, without taking a desired
arithmetic result as a premise. In-range result reads the actual represented cell,
then existing Source compound syntax evaluates RHS first, resolves the location
once and writes; actual MemOK/observer/local/stack/allocator transport follows.
The word program composes published readLocalCode/binaryCode/writeLocalValueCode
certificates read-only. Its pure local operands permit the read/RHS ordering
agreement; no arbitrary effectful RHS/lvalue order is claimed. Explicit range
bounds describe this local successful case, never a profile exclusion. A separate
actual resolved Source checked-overflow theorem returns arithmetic panic before
the write; unchecked wrapping remains a separate unfinished application.

SourceUintCompoundControls reuses C60's independent public initial witness over
identical populated fixture definitions; it does not assume a reached relation.
An actual Source RItems program, intrinsic Prog and complete word append assign3
to the old0 cell, then read the REACHED3 and add3 to obtain6. Initial max/neighbor,
shared alias, all root content words, complete Source object tables, explicit
sixteen-word frames, stack42/free96 and an inhabited final StructAllocatorRepr
are observed across every stage, in both pipelines. A frozen-initial negative is
tied to that actual Source program and refutes final3. The same initial represented
max cell plus1 executes real Source arithmetic panic and full word revert; no
suffix machine/rollback/target panic-payload equivalence is invented. All C60 and
older vectors remain byte-preserved. Generic laws quantify arbitrary intrinsic
valid runtime lists/indices; finite fixture17+length<=80 is only word-region
layout, not a source admission cap. C60 empty/end/31/32/timeout/late-failure/order
controls remain in the checked import closure rather than being replaced.

C61 focused controls08 passes166jobs with exact standard-only guards, aggregate
RSS969792KiB and no new OOM event. Earlier distinct type/normalization/dependent
lookup/heartbeat failures are retained, not passes. No proof/time/memory budget
was increased. The independently checked C60 package remains immutable3439entries.
Additional registry clarification: C60 metadata used descriptive label `delete`;
the ACTUAL manifest feature ID is `deleteExpression`. Coordinator proposals must
use `deleteExpression`, alongside `assignment`, `compoundAssignment`, `integerTypes`,
`memoryLocation`, `dynamicArrays`, `indexAccess` and `memoryAliasing`. This is an
additive correction, not an edit to any earlier seal or reserved global registry.

Original-queue reassessment remains partial: supported numeric addition is not
all arithmetic/compound/bump cases, arbitrary effectful operand order or broader
Source reference paths. Physical byte representation, all-profile construction/
target allocation failure, ABI/reference/storage/fresh deep-copy/recursive Source
graph/liveness, reserved memory-storage and final V10/Source/target producers remain
unfinished. Published bounded word execution is distinct from external solc/EVM.
No independent-work exhaustion or goal recovery/completion is asserted. The
existing BLOCKED goal remains untouched; per-file Lean MCP/get/update goal tools
are unavailable, so permitted serial focused diagnostics are used.


C61 refined-tree final wrapper exit0: default1109/TestSuite262/final SolKey377parsed,
131read-bearing allcovered. Fresh Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs pass.
Strict/trust/layers/orphans/lane/complete fixtures/script-corruption/diff pass.
Scoped992exactstandard pins across128owned modules validate; raw global inventory
remains **exit1**,1351unregistered=359public+992owned/0unsafeerrors. Raw strict docs
stays **exit1**,83complete public-byte-identical findings; separate publiczero-new
passes, frozenno-new fails with11incoming. Global registries/baselines untouched.
Warm strict0timed modules; independently current262Suite/fixture/toolchain bytes
and actual C61versions match retained C31cold26/max160s<300s, not new timing.
Focused controls08 aggregate969792KiB/full1581668KiB, full diskgrowth266240bytes;
all C61execs newOOMdelta0. C60cumulative12GiB/max10719/oom3/kill3 and all earlier
failed attempts remain retained, never relabeled passing. All3439 C60sealed
entries reverify unchanged. Both independent finder/skeptic SOURCE/control/docs
reviews PASS with no confirmed remaining finding; committed-artifact review follows.

Remaining concrete original G34 investigation: reached compound arithmetic panic
as a late Source RItems/intrinsic/word failure after a materially changed first
statement; C61 has actual in-range two-statement composition and actual initial
max-overflow expression/word outcomes, but not that general late-overflow theorem.
Other compound operators/unchecked wrapping/general effectful operands likewise
remain unsupported here. This identifies future supported investigation, not an
exhaustion claim or permission to duplicate reserved owners. Original upstream
physical bytes/all-profile allocation-failure/general reference-graph/ABI-storage/
fresh deep-copy/reserved copying/final Source-V10-target obligations remain open.
The persistent BLOCKED goal is unchanged; no status operation occurred.


C62 — LATE checked arithmetic failure after an actual changed prefix
(partial G34/Backfill B, not whole-lane completion).
SourceUintLateFailure reuses the existing resolved assignment, Source compound
update/overflow and published intrinsic/word read-binary-write certificates.
The all-outcome word theorem is derived, not supplied as a compiler oracle.
The late composition accepts INITIAL local alignment, bound, MemOK/StateRepr,
checked mode and a local arithmetic case value+delta out of range. The first
actual write produces mid/ym/mm. Its length/set-self lookup and unchanged locals
derive the second operation's actual old value, bound and Source/word relations.
Source execItems(n+6), intrinsic Prog and complete word append then reject at
that reached operation. Source returns the actual prefix globals; no target
suffix machine, rollback or Source panic-byte/word-revert equivalence is asserted.

The controls execute a populated runtime-indexed zero-to-max family. Both declared
pipelines retain complete initial/prefix typed contents and two-object Source
tables, all root word contents, explicit16word frame vectors, saved stack42,
free pointer96, root/alias identities, neighbors8/9, world/local frames and an
inhabited allocator. A typed inequality proves the first root really changed.
INITIAL0-plus1 succeeds with result1 while reachedmax-plus1 panics/reverts; the
same operation's epochs are distinguished, not assumed. Reversing the actual
program succeeds0-to1-to-max, with real second-stage prerequisites derived and
complete initial/intermediate/final observations; equal final cell values do not
make the two program outcomes equal. A lower Source horizon5 executes the real
material prefix then times out; at horizon6 the arithmetic failure is reached.
Empty/exact-end inputs instead reject the FIRST statement with index panic and
no executed arithmetic suffix. C60/C61 and all earlier fixtures remain unchanged.

Generic laws quantify arbitrary intrinsically valid runtime lengths/indices.
The concrete fixture's17+length<=80 only separates its fixed word regions and is
not a public payload/depth admission cap. Pure local operands and the same typed
uint destination are the supported case; no arbitrary effectful RHS ordering,
unchecked overflow, full type family, recursive Source graph or physical bytes
are inferred. No representation/compiler/evaluator or reserved producer is added.
All four new laws and five controls carry exact standard-only axiom guards.
The timeout theorem's originally guessed empty axiom set failed; its actual
[propext, Classical.choice, Quot.sound] set is now pinned, not an unsafe allowance.

Focused controls08 passes168jobs, aggregate RSS1022180KiB and newOOMdelta0 under
unchanged serial12GiB/no-swap containment. Every distinct earlier failed proof/
normalization/guard attempt remains retained. Three real C60OOM kills and the
cumulative12GiB peak remain failure history, separate from current passing runs.
The new lane-specific script tests only pin/evidence admission: actual complete
execution observations are kernel proofs, not text-test simulations. It exercises
positive exact coverage and missing/unsafe/renamed guard corruption in memory,
without editing reserved global pin inventories or source fixtures.

Original queues remain partial/blocked: physical byte representation, all-profile
constructors/target allocation failures, general references/paths/graphs, other
arithmetic/effectful operands, ABI/storage/fresh deep-copy/liveness, reserved
memory-to-storage and final Source/V10/target composition remain unfinished.
No independent-work exhaustion, external compiler/EVM validation or goal status
recovery/completion is claimed. Existing BLOCKED goal identity/status is untouched;
get/update goal RPC and per-file Lean MCP remain unavailable in worker tools.


C62 final refined-tree wrapper exit0: default1111/TestSuite262/final SolKey377parsed,
131read-bearing allcovered. Fresh Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs pass.
Strict/trust/layers/orphans/lane/completefixtures/script syntax/diff pass; combined
13scriptcorruptiontests pass, including8new targeted guard-admission cases.
The initial newscript mutation regex failed to remove guards (6pass/2fail); that
actual exit1/rawlog is retained. Exact literal-line mutation repaired the test
without changing any Lean statement/vector, baseline or unsafe-axiom allowance.
Scoped1001exactstandard pins across130owned modules validate, while raw global
inventory remains **exit1**,1360unregistered=359public+1001owned/0unsafeerrors.
Raw strict docs stays **exit1**,83complete public-byte-identical findings; separate
publiczero-new passes, frozenno-new fails with11incoming. No global registry/debt
was edited. Warm strict timed0Suite modules; independently current262Suite/
fixture/toolchain bytes and actual C62versions match retained C31cold26/max160s
under300s, not new timing coverage. Focused controls08 aggregate1022180KiB/full
1570840KiB; full diskgrowth270336bytes/newOOMdelta0. All C62execs newOOMdelta0;
C60cumulative12GiB/max10719/oom3/kill3 remain failed history. Both independent
finder/skeptic SOURCE/control/doc/script reviews PASS with no confirmed remaining
finding. All3506 C61sealed entries reverify unchanged. Committed-artifact reviews
follow the compact additive export. Existing goal stays BLOCKED unchanged.

Reassessment: the requested same-cell latechecked-add failure application is now
proved, but not all numeric/default/path/copy cases. A further original G33
investigation is actual numeric default declaration/context extension: the current
SourceDeclaration adapter source_bool_declaration_word handles Bool arrays,
while source_decl_statement_run is polymorphic and published declareNewCode plus
SourceUintMemoryAt/source_uint_alloc supply relevant interfaces. No owned
source_uint_declaration adapter was found in the current source scan; a numeric
application still needs independently derived zeroVal/MemOK/fresh-map/context
alignment/allocator facts rather than assuming the Bool theorem applies. This
is concrete future work, not implemented or an exhaustion assertion. Full original
physical-byte/all-profile allocation-failure/reference-graph/ABI/storage/fresh
copy/reserved memory-to-storage/final Source-V10-target obligations remain open.


## C63 — numeric empty default declaration and context extension (partial G33)

At parent abdab57fa43b6bd0f8167a4466963528873cdef8 the actual SourceDefault and
SourceDeclaration adapters were Boolean-only. New owned SourceUintDefault and
SourceUintDeclaration specialize the published independent zeroVal/allocRef,
Heap.allocDefault/TRun.declMem, and existing uint newArray_correct/declareNewCode
producers. They introduce no allocator, decoder, evaluator, type or admission rule.

source_uint_default_run/intrinsic/memOK/default_frame/word/lowfuel derive actual
Source execution, fresh empty intrinsic contents, actual Keeps and logical fresh
identity, occupied old-address separation, existing whole word execution and real
zero/one-fuel timeout. SourceUintMemoryAt.withLocals changes only the heap observer;
it makes no claim that local indices are unchanged. declaration_frame derives the
actual declaration, old observer across real Source/intrinsic allocation and fresh
separation. source_uint_declaration_word derives Source-cons locals and MemOK with
the existing intrinsic local push/heap-prefix extension, StateRepr, allocator and
unchanged stack. Source and intrinsic local bindings are checked explicitly;
heap identities append while the word local occupies b+old context length.

Premises remain INITIAL MemOK/StateRepr/StructAllocatorRepr, positive local base,
space cursor+1<W and frame capacity. Old-object frame laws consume INITIAL
SourceUintMemoryAt. No desired output relation, successful final operation,
global address injectivity or second independent run is assumed. The only default
constructor application here is an EMPTY dynamic uint256 array; it is not an
all-profile constructor or checked allocation-failure theorem. The existing raw
word_empty_allocator_wrap law remains unchecked wrapping evidence only.

SourceUintDeclarationControls executes populated runtime old arrays/shared aliases
and neighbor objects in both declared pipelines. populated_declaration records
actual Source statement, intrinsic declaration and entire word constructor, fresh
and both old representations, Source shifted locals, complete16word frame,
all old content words, saved stack, logical identities and allocator. Additional
source_object_table/fresh_empty_observations expose all five initial/final Source
object observations, fresh intrinsic/shifted old local binding, empty contents,
intrinsic index0=None, actual Source index panic and fresh header96zero.
nonuniform_run applies the generic producer to nonempty [7,0,max] in both pipelines;
fresh_context_negative distinguishes fresh identity/word local from retained old
aliases. populated_timeouts retains actual horizons0..2, with no fresh suffix.
The fixture's word-region fit bound is not a public payload limit. No fresh word
read-revert suffix, Source allocation-expression, byte memory or external EVM
execution is claimed. Earlier fixtures and their vectors remain untouched.

Separate read-only finder and skeptic source/control/script reviews PASS. Both
requested explicit fresh contents/context/empty-bound observations; those were
added and checked. The frame vector already included fresh header96 (a preliminary
review note was corrected), and a direct zero-header clause is now present too.
The new script tests exact16headline guard admission and missing/unsafe/renamed
mutants only; it is not execution evidence. All16 guards check actual standard
sets (fresh_context_negative uses propext/Quot.sound, others the standard trio).
Focused controls09 passes170jobs, aggregate922988KiB/no newOOM; all earlier failed
attempts are retained, including the dependent controls01 stopped at a still
failing frame helper. No failed proof is delivered as a successful theorem.

Fresh Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs and unchanged final wrapper pass:
default1114/TestSuite262/SolKey377parsed/131read-bearing covered. Full aggregate
RSS1593824KiB, diskgrowth274432bytes and newOOMdelta0. Existing12GiB/no-swap child,
16GiBparent, CPU0/serialLean-j1/threads1/cacheOFF and OS headroom are retained.
Preflight983793664available bytes admitted96MiB forecast above512MiB reserve;
post-full980967424available. C60historical3OOMkills/cumulative12GiB peak remain
failed history, not current passing memory evidence. Goal remains BLOCKED
unchanged; goal get/update RPC and Lean MCP diagnostics unavailable.

All original G32/G33/G34/G35.01/.03/.04/.05 and BackfillA/B remain PARTIAL;
G35.02 and G35.06 remain BLOCKED on reserved copy and final upstream composition.
Physical bytes, all-profile constructors/target allocation failures, general
paths/graphs/reference/ABI/storage/deep-copy/liveness and final Source/V10/target
composition are not supplied by this supported numeric constructor application.
A next distinct original G33/BackfillB investigation is carrying a nonempty
existing numeric observer and shifted alias through declaration into actual reached
numeric write/delete syntax, consuming new fresh empty bounds rather than
assuming the old local index still denotes the old root. This application is not
yet proved here; no queue-exhaustion or whole-lane completion is asserted.

C63 final static/completefixture/strict/trust/layer/orphan/lane/script checks pass;
25combined corruption tests pass (12new guard-admission tests). Scoped1017 exact
standard-only pins across133owned modules pass; raw globalinventory stays exit1,
1376unregistered=359public+1017owned/0unsafe errors. Strict docs stays exit1 with
83complete findings, byte-identical to publicbaseline (separate zero-new PASS),
while exactfrozenbase comparison retains11incoming and FAIL1. No unrelated
historical/vendor/global debt was rewritten. Warm strict timed0Suite modules;
all262currentSuite/fixture/toolchain files independently equal retainedC31 bytes
and actualversions, so cold26/max160s<300 remains keyed retained evidence only.
All3573 C62sealed entries reverified unchanged. Separate independent finder and
skeptic source/control/script reviews PASS with explicit added empty/fresh/context
observations; committed-artifact review follows export. Earlier failed focused
checks/coretype/contextinfer/guardformat/dependentindex issues are retained in raw
logs; controls09 and finalfull pass with no elaboration-generated sorryAx.


## C64 — reached numeric mutation after context-changing declaration (partial)

Following reviewed C63, the next distinct G33/G34/BackfillB application now derives
actual numeric declaration followed by indexed OLD-alias assignment. New owned
SourceUintDeclarationSequence consumes C63 source_uint_declaration_word and
SourceUintMemoryAt.declaration_frame, existing source_items_context_pair_run and
resolved_uint_assign_word. No allocator, evaluator, syntax representation or copy
algorithm is added. INITIAL Source/intrinsic local alignment, old index bound,
MemOK/StateRepr/allocator/positivebase/space/framecapacity derive the actual first
Source statement and changed context; old locals/refs weaken separately and the
second bound follows actual Keeps.len. The second operation executes at that
reached heap, Source-cons context and target constructor output, never the initial
state or an assumed second run. Source original parameter count is retained.

SourceUintMemoryAt.declare_assign_word proves both actual statements and Source
RItems, intrinsic Prog, existing declare+write word append, reached/final old
observer, initial fresh observer and its structural frame after old write,
other Source-object frames, MemOK/StateRepr/final allocator/stack, actual allocated
Source globals and full local extension. Only supported empty new numeric object
and pure-local old-root/index/RHS operands are covered. It does not claim that the
fresh object accepts any index, nor all-profile constructors/allocation failures.

SourceUintDeclarationSequenceControls applies the law in BOTH pipelines to
nonempty [7,0,max] oldcontent and shared aliases: declaration leaves content
unchanged, reached assignment writes3 at1, retained alias actually reads3 while
fresharray2 rejects0 with Sourcepanic and stays intrinsically empty. All three
initial/mid/final Source oldobject observations, neighbor/fresh tables, intrinsic
content vectors, three FULL16wordframe vectors/all content words, local/root/fresh
IDs, savedstack and allocator are derived. Wrong-root/skipped-write negatives
distinguish freshptr96 from oldptr16 and unchanged0 from written3. C63 endpoint/
lowhorizon/space-boundary scope remains retained; C64 supplies no new late timeout
or target empty-read suffix. No physicalbytes/Source rollback/external EVM claim.

Focused controls04 passes194jobs, exact3standard-only guards (one pair, two trio),
aggregate955292KiB/newOOMdelta0. Earlier core/context-inference and mixed-generation
primitive heap-parameter rewriting failures are retained. The latter were repaired
by explicit intrinsic heap parameters, preserving every expected vector and bound.
C64 forecast96MiB plus512MiB reserve is admitted by958881792available bytes after
C63 seal; same existing runtime/caches/12GiBnoswap/16GiBparent/CPU0/serialLean-j1/
threads1/cacheOFF and unchanged budgets. Prior C63seal remains immutable.

Every original Work/Backfill parent remains partial/blocked. Full physical-byte,
all-profile construction/targetallocationfailure, general path/graph/delete/rebind,
ABI/reference/storage/deepcopy/liveness, reservedmemory-to-storage and final
Source/V10/target obligations remain open. No original-lane completion or
independent-queue exhaustion is asserted. Existing blocked goal is unchanged.

C64 final wrapper exit0:1116default/262Suite/SolKey377parsed/131read-bearing
covered. Fresh Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs pass. Full aggregate
RSS1578740KiB/diskgrowth266240bytes/newOOMdelta0; original caps/cacheOFF remain.
Both independent SOURCE reviewers PASS with no confirmed proof defect. The
skeptic noted that wrong_root_and_skipped_write compares identity/pointers/values,
while the actual fresh Source endpoint rejection is a separate conjunct; no whole
wrong-target program execution is claimed. Exact3guards pin actual standardsets;
the newscript admission mutants are distinct from kernel execution evidence.

C64 strict/trust/layers/orphans/lane/completefixtures/script syntax/diff gates pass;
33combined corruption tests pass, including8new sequence-guard admission cases.
Scoped1020standard-only exactpins/135modules pass; rawglobalinventory remains
exit1,1379unrecorded=359public+1020owned/0unsafe errors. Rawdocs remains exit1 with
83complete findings byte-identical to publicbaseline (separate zero-new PASS),
while frozenbase comparison still FAIL1/11incoming; no baseline/globaldebt edits.
Warmstrict timed0Suite modules; independently all262currentsource/fixture/toolchain
bytes and fresh64versions match retainedC31cold26/max160s<300, not newtiming.
All3645 C63sealed entries reverified unchanged. Both independent SOURCE/control/
doc/script reviews PASS, no remaining confirmed finding. Committed-artifact
reviews follow additive export. Final resource sample955629568available bytes
above unchanged96MiBforecast+512MiBreserve; original worker/goal identity retained.

Next concrete original G34/BackfillB investigation: after this real numeric context
extension, derive late rejection of an indexed operation on the FRESH empty root
in Source RItems/intrinsic Prog/wholewordappend, retaining successful allocation
prefix and distinguishing an old-root valid read from fresh-root endpoint panic.
Current C63/C64 prove the actual fresh Source/intrinsic endpoint and successful
old-root sequence separately, not that combined rejecting program. Existing
source_items_context_pair_error and resolved_uint_assign_word_bounds are public
owned interfaces to investigate. This is unfinished supported work, not a new
admission rule, established result or an assertion of independent-queue exhaustion.


## C65 — actual declaration then fresh-root late rejection (partial)

At C64 parent20579e116d33a7020bcd8ab93cbda3c9251f6e07 the successful old-alias
sequence and separate fresh Source.memElem rejection were proved, but not one
combined rejecting program. New owned SourceUintDeclarationFailure consumes
source_uint_declaration_word, resolved_uint_assign_word_bounds and
source_items_context_pair_error. sourceUintDeclareFreshAssign is ordinary existing
RItems composition, not an AST, evaluator, allocator or alternate copy semantics.

source_uint_declare_fresh_reject_word derives actual successful declaration,
fresh empty contents/length/identity, extended Source/intrinsic local alignment,
MemOK/StateRepr/allocator and every runtime uint index bounds failure from INITIAL
scalar alignment and existing constructor/frame/space premises. It proves reached
Source expression/statement/Items index panic, intrinsic writeAddr=None/Stmt/Prog
revert and the WHOLE existing constructor+indexed-write word append reverting.
No failed suffix, desired reached relation or final preservation is assumed.
Original Source parameter count Γ.length is preserved independently of the new
local context. Old represented numeric roots survive with derived logical/source
fresh separation, not a global injectivity premise or admitted shape exclusion.

Source evalE failure exposes the reached EMState; Items failure exposes reached
globals and caller nil locals. Fresh locals are known from the actual successful
prefix, not fabricated as an Items error return. Intrinsic/word revert outcomes
erase suffix states; all target frames/allocator/stack/content observations attach
ONLY to the real successful constructor boundary. No rollback or Source panic-byte
identity with symbolic word revert is claimed. Source index panic bytes are
4e487b71 followed by31zero bytes and 0x32; the symbolic `.revert` has no payload.

Generic low-horizon laws distinguish Items0..3 timeout with INITIAL globals from
Items4..5 timeout after successful allocation. The populated all_horizons control
classifies every runtime natural fuel, with index panic at6+ and the corresponding
actual global state. These evaluator fuel observations impose no new public cap.

SourceUintDeclarationFailureControls executes BOTH pipelines with old[7,0,max],
neighbor[8,9] and retained/shared old aliases. Actual rejecting Items/Prog/word
append, all6initial/reached Source cells, intrinsic old/neighbor/fresh content
vectors, allSource scalar/reference local observations, both FULL16wordframes and
all oldcontent words, fresh/old typed IDs, savedstack and allocator are proved.
Source next2→3 and reachedglobals≠initial distinguish retained allocation from an
invented rollback. Oldalias actual read returns0 while freshwrite rejects. Actual
skipped-declaration oldwrite succeeds; the actual C64old-root Items program succeeds
from the SAME initial state where the fresh-root program rejects. Exact panicbyte
and early/reached/allhorizon controls are separate kernel theorems. No inaccessible
final intrinsic/word machine or new all-profile allocator failure is asserted.

Focused controls05 passes196jobs, aggregate961416KiB/no newOOM. All13 new public
laws/controls have exact standard-only guards: panic bytes use no axioms, others
the standard trio. Earlier recursion/type/sequence projection/concrete conversion
failures are retained; the simplifier loop was repaired with actual fresh-local
alignment, not a recursion/proof budget increase. New script tests guard admission
and applied missing/unsafe/renamed mutants only, not runtime execution.

Preflight reverified all3708 C64sealed hashes and exact same running container/
image/mounts/toolchain/cache identity with idle workers. Available933736448 bytes
admitted96MiB changed-output/log/compact-export forecast above512MiB reserve.
Same12GiB/no-swap child,16GiBparent/OSheadroom/CPU0/serialLean-j1/threads1/cacheOFF
and all proof/fuel/node/TestSuite/time guards are unchanged; no deletion/newruntime.
Goal remains BLOCKED unchanged; goal get/update and per-file MCP unavailable.

All original Work G32/G33/G34/G35.01/.03/.04/.05 and BackfillA/B remain PARTIAL;
G35.02 and G35.06 remain BLOCKED on reserved/final composition dependencies.
Physical bytes, all-profile/reference constructors/target allocation failures,
general graphs/paths, ABI/storage/deepcopy/liveness/reserved copying and final
Source/V10/target closure are not proved by this supported application. No queue
exhaustion, compiler/EVM adequacy or whole-assignment completion is claimed.

C65 final unchanged wrapper PASS0:1118default/262Suite/SolKey377parsed/131read-bearing
covered. Fresh Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs PASS. Full aggregate
RSS1593884KiB/diskgrowth274432bytes/newOOMdelta0; currentexec counters remain
unchanged from historicalC60max10719/oom3/kill3/cumulative12GiBpeak. Both independent
SOURCE/control/doc/script reviewers PASS, no confirmed remaining proof defect.
All-fuel classification is proved by actual finite low cases and high n+6 runs,
not an assumed monotonicity principle. Old fixtures/prefixes remain untouched.

Further original G33 investigation found published DefaultBuilder.fixedPrimitive
and defaultFixed_copy/AllocatorRepr.allocateFixedPrimitive, with a headerless
max1n target footprint, and actual Source.zeroVal/zeroData/zeroElems for fixed
arrays in Source.Machine. Existing SourceUintMemoryAt always describes a dynamic
Source type; its intrinsic_fixed control explicitly disclaims fixed Source lowering.
A genuine fixed-uint Source default/observer/context bridge remains independently
unimplemented, requiring typed Source length evidence, actual zeroElems fuel and
conversion agreement, and the published fixed-builder output. No fixed/reference
constructor producer is missing or duplicated here; reserved producers remain
read-only. This is a concrete remaining application, not an exhaustion assertion.

C65 final strict/trust/layer/orphan/lane/completefixture/script syntax/diff gates
PASS;41combined script tests PASS (8new failure-guard admission mutations).
Scoped1033exactstandard-only pins/137modules PASS; rawglobalinventory remains
FAIL1,1392unrecorded=359public+1033owned/0unsafe errors. Rawdocs remains FAIL1,
83complete findings byte-identical to publicbaseline (separate publiczero-new
PASS), while exactfrozenbase comparison FAIL1 retains11incoming. No unrelated
baseline/vendor/global registry was edited. Warmstrict timed0Suite modules;
all262currentSuite/fixture/toolchain bytes independently equal retainedC31source
and fresh65versions match, so cold26/max160s<300 is retained evidence only, not
newtiming. All3708 C64sealed entries reverified unchanged. Finalresource sample
930586624available bytes above unchanged96MiBforecast+512MiBreserve; allC65exec
OOMdeltas0, historicalC60failures/cumulativepeak retained separately. Both independent
SOURCE/control/doc/script reviews PASS with no confirmed remaining defect;
committed-artifact reviews follow compact additive export. Goal remains unchanged.


## C66 — genuine fixed uint Source default and declaration (partial G33)

At parent23a425294919c94fed25d483f9eb54eba4593bfb existing SourceUintMemoryAt
ALWAYS used dynamic Source STy none even for an intrinsic fixed ArrTy. The new
sourceUintFixedObject/SourceUintFixedAt use EXISTING Data.array with actual n
and dependent element evidence from MObj (.fixed (.prim .uint) n), recording
Source STy some n. Dynamic observer/theorems/controls are untouched; fixed Source
is never coerced to dynamic. No value/state/AST/interpreter/allocator is added.

source_uint_zeroElems_run/fixed_zeroData/fixed_zeroVal prove actual independent
Source evaluator execution at fuel n+1/n+2/n+3. Insufficient counterparts prove
actual timeout with unchanged state at fuel≤n/n+1/n+2, including primitive work
before timeout. These length-parametric evaluator laws do not increase proof/test
budgets or impose public admission/fuel/length/depth caps. SourceUintFixedAt
read/bounds/eval_index/keeps and typed conversion/wk transport preserve actual
length and contents. source_uint_fixed_intrinsic derives actual fresh default
correspondence/replicate contents/Keeps/freshID from published defaultFixed_copy,
not an assumed successful run or desired relation. Occupied Source cells frame
through actual allocation; old typed IDs are distinct by their real upper bound,
with no global address-map injection premise. MemOK is the existing zeroOK law.

source_uint_fixed_declaration_word consumes INITIAL Source MemOK and Objects
StateRepr/AllocatorRepr/positivebase/framecapacity plus cursor+max1n<W. Published
DefaultBuilder.fixedPrimitive/defaultDeclare_correct supply the actual intrinsic
declaration and WHOLE headerless word declaration, indexed by the SAME real g
as the independent Source fixed observer. Actual Source declaration at n+4 and
local cons/MemOK, intrinsic adoption/local push/heap extension, full word state,
base extension/allocator/stack and fresh/old Source/typed identity frames derive.
No second-run, postcorrespondence or final-preservation oracle is an input.
Existing constructor/word/Source producers remain read-only and are not duplicated.

Supported Source/word constructor applications require 0<n; this is a theorem
case, not a new profile exclusion or Source-admission theorem. Low-level kernels
already have natural lengths including0. The zero_padding_kernel_only control
asserts ONLY intrinsic/word max1n footprint for0, never a Source declaration or
zero-length Source admission. Kernel evaluator facts at0 do not grant admission.
General reference constructors/all-profile allocation failure remain open.

Independently inhabited inputs have actual old fixed[7]/neighbor[9], repeated
old aliases, Source allocations and MemOK, complete typed object-word ownership,
stack77 and caller99. populated_declaration quantifies every positive runtime n
with existing word space, deriving actual Source/intrinsic/word execution and
all6initial/reached Source cells, old/fresh intrinsic contents, Source context and
typed local identities, Source fresh0 versus oldalias7 resolved reads, exact-end
panic, both FULL16wordframe vectors and every new elementword0, unchanged old
bases/neighbor/aliases/caller/stack and final ownership/allocator. Fresh fixed words
are headerless: word32 is element0, NOT a dynamic length header. New pointer32 is
stored in the actual added local5; old locals remain below the owned object frame.

positive_examples directly applies the general law at1/3/33 in BOTH pipelines;
element_boundary reads32 and rejects33 after actual length33 declaration. Wrong
dynamic type, fixed length and stale identity controls disagree with produced
Source tables; same-type n=1 old7 versus fresh0 prevents a vacuous type-only test.
All insufficient declaration horizons retain the populated initial Source state.
Raw zero-padding still reserves one owned cell, separately scoped as above.
Complete prior fixture vectors/guards/prefix failures remain unchanged.

Focused controls07 PASS209jobs/exact28newstandard-only guards (two conversion/wk
pairs,26trios), aggregate955616KiB/newOOMdelta0. Actual earlier type/tuple/recursor/
read conversion/zero-padding normalization failures are retained, not waived.
No sorry/newaxiom/native shortcut/heartbeat or recursion-limit increase was used.
Per-file MCP and goal get/update unavailable; existing goal remains BLOCKED,
unchanged. Preflight verified all3772C65sealed hashes and exact same idle capped
runtime/image/mounts/cache/toolchain:908558336available admitted96MiB forecast
above512MiB reserve. SerialCPU0/Lean-j1/threads1/cacheOFF/12GiBnoswap/16GiBparent
and OS headroom/unchanged guards are preserved; no deletion or newruntime.

All original G32/G33/G34/G35.01/.03/.04/.05 and BackfillA/B remain PARTIAL;
G35.02/.06 remain BLOCKED. Physical bytes, all-profile/reference construction and
checked allocation failure, general paths/graphs, ABI/storage/deep-copy/liveness,
reserved copying and final Source/V10/target composition remain unfinished.
Kernel/symbolic-word proof is not external compiler/EVM testing or whole-lane
closure. No independent-queue exhaustion is claimed.

C66 raw_space_wrap additionally checks the existing unchecked word boundary at
cursor32+size(W-32)=W: execution returns a wrapped cursor0, incompatible with
full allocator ownership above frame8. No enormous Source/intrinsic array is
evaluated, no Source admission follows, and this is NOT checked allocation failure.

C66 final unchanged full wrapper PASS0:1121default/262Suite/SolKey377parsed/
131read-bearing covered. Fresh actualLean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs
PASS. Full aggregateRSS1623504KiB/diskgrowth270336bytes/newOOMdelta0; prior C60
max10719/oom3/kill3/cumulative12GiBpeak/DockerOOMKilled remain failed history,
not currentexec evidence. Both independent read-only SOURCE/control/doc/script
reviews PASS. They confirmed genuine fixed types and same actual default g,
nonvacuous populated ownership, headerless/padding/wrap/typednegative scopes.
An initially stale controls05/RSS doc label was corrected to actual07/955616
before final full validation; no theorem/premise/vector change was required.

Original-queue reassessment: SourceUintFixedAt now supports fixed reads, but
SourceUintWrite/SourceUintDelete still consume the dynamic SourceUintMemoryAt.
Published Source.memSet's typed array branch and Evm.Memory.Objects indexed
assignment certificates support a next G34/BackfillB investigation: actual fixed
Source element write/delete at the reached new local after C66 declaration, with
preserved fixed length, old aliases and neighbors. That exact fixed update
transport is not established by the present default/read theorem and remains
unimplemented; no producer absence, whole-lane completion or independent queue
exhaustion is asserted. Reserved constructors/Source/Evm implementations stay
read-only. All previously named original obligations remain binding.

C66 final structural/trust/layer/orphan/lane/complete-fixture checks PASS; combined
script admission/corruption tests PASS53. Scoped exact standard-only guards
PASS1061 across140owned modules. Raw global inventory remains FAIL1 with1420
unrecorded=359published+1061owned and0unsafe; additive proposals are evidence,
not reserved-registry edits or a global pass. Raw strict docs remains FAIL1/83
findings; COMPLETE current/public bytes match, separately PASS zero-owned-new.
Frozen comparison retains11incoming findings/FAIL1. Warm strict times0newSuite
modules; independently all262current/C31source-fixture-toolchain keys and actual
versions match, retaining26cold modules/max160seconds under300, not new timing.
All3772C65sealed entries reverified. Final idle runtime available904626176bytes
retains512MiBreserve+96MiBforecast; no newOOM events or resource guard changes.


### C67 — genuine fixed uint Source update and primitive deletion (PARTIAL)

The C66 observer carries Source STy some n; existing numeric mutation adapters
carry none, even where intrinsic ArrTy is generic. Current owned-source inspection
reproduced that concrete gap. SourceUintFixedWrite preserves genuine fixed Data
length through actual Source.memSet/Data.array and intrinsic MObj.setElem .fixed.
It derives reached SourceUintFixedAt and old Source-address/intrinsic-ID/world
frames, from INITIAL observer and runtime valid index. No dynamic cast, desired
postrelation, second heap/state/evaluator, address-map injection or new admission
restriction is introduced. Existing dynamic modules and ALL previous controls and
guards remain unchanged.

SourceUintFixedAssignment derives actual RHS-first resolved local index lvalue,
assignment expression and statement, actual intrinsic Stmt.assignMem and WHOLE
published Objects.PtrFrag.write code. SourceUintFixedDelete derives actual
primitive zero/default/unit deletion via existing deleteLoc and intrinsic
primitive-delete/assignment equality, with complete existing headerless word
code. Inputs are INITIAL operand alignment, fixed observer, Source MemOK and
Objects.StateRepr; results derive actual Source/intrinsic/word execution,
reached fixed observer/MemOK, local/stack and Objects.KeepsAllocator frames.
Declared fixed length bounds Source indexLoc; local lookup is not a runtime
Source heap-shape/admission theorem. Rejection gives Source index panic versus
intrinsic/word revert without claiming equal payload or rollback.

source_uint_fixed_declare_write_delete consumes C66's actual positive fixed
constructor on INITIAL memory/ownership/allocator/space/frame evidence. The
new Source local cons and intrinsic heap weakening/local push derive the next
operands. Real assignment outputs feed real deletion. It derives both reached
Source observers, final word StateRepr/AllocatorRepr, old-ID/other-address frames,
all stacks, and the WHOLE existing three-code append. Source statements have
SEPARATE exact horizons (declaration n+4, mutations4); no combined Source RItems
or intrinsic Prog composition is claimed by this theorem. No assumed final
agreement, stagewise restoration, Source admission of zero, global injection,
new allocator or reserved producer implementation is used.

The populated runtime control independently constructs old fixed[7]/neighbor[9]
with repeated old aliases, Source MemOK and complete object-word ownership.
For every positive runtime n and canonical k<n under existing cursor32+max1n<W,
actual fresh declaration then indexed value=k write and default delete are
observed. At n33/k32 the write materially changes logical element32 to32, then
clears it; the word reverse order leaves32. The Source reverse program is NOT
claimed. Old contents7/9, root aliases, fresh full contents/typed Source tables,
locals, stack77/caller99/freepointer, allocator and FULL16word vectors remain
explicit. Length1/index0 and length3/index2 are direct producer applications.
Actual endpoint33 rejects Source assignment/delete and intrinsic/word deletion;
Source panic bytes are independently pinned, not equated to word payload.
Same-type old7/fresh0, wrong dynamic/fixed length and skipped-clear/reverse-word
observations discriminate stale identity/type/order. Logical32 is not physical
byte encoding. Low-horizon constructor controls remain C66's exact unchanged
laws. Zero-size padding remains RAW intrinsic/word only, no Source admission.

C67 controls07/08 failed at the enforced12GiB cap, Lean137/Lake1, each newOOM1;
all raw receipts and earlier elaboration failures remain preserved. Monolithic
run reduction and then broad simp proof were replaced with explicit short-code
certificates from published fixedAddr_run and exact append/observed rewrites.
No limit/heartbeat/fuel/test/stack budget increased. Approval review rejected
one proposed repair because it removed new control statements; it never ran.
The accepted safer repair preserved EVERY vector/boundary/positive statement
and changed only proof bodies/additive helpers. Diagnostic copies are evidence,
not deliverable admitted proofs. Final checks below record actual outcomes.

Same runtime/image/mounts/toolchain/cache and writer lease preflight verified all
3855C66sealed entries,882401280available above512MiBreserve+96MiBforecast.
SerialCPU0/Lean-j1/threads1/cacheOFF/aggregate12GiBnoswap/16GiBparent and OS
headroom remain unchanged. Per-file Lean MCP and goal get/update unavailable;
existing persistent goal remains BLOCKED unchanged. Earlier C60OOM history and
new C67OOM history remain failures even after passing proof repairs.

All original G32/G33/G34/G35.01/.03/.04/.05 and BackfillA/B remain PARTIAL;
G35.02/.06 remain BLOCKED. General graphs/paths/effects, all-profile/reference
construction/allocation failure, physical bytes, ABI/storage/deep-copy/liveness,
reserved copy and final Source/V10/target composition remain unfinished.
Kernel/symbolic-word evidence is not external compiler/EVM execution. Fixed
Source Items/Prog declaration/update/delete and later failure composition remain
supported next applications, not already supplied here or queue exhaustion.

C67 final focused controls12 PASS218jobs/RSS994736KiB with exact23new public
guards (22standardtrios, axiom-free panic bytes), no sorryAx. Source/control/
script/document finder AND skeptic reviews independently PASS, no confirmed
findings. They explicitly checked separate Source statements and word-only
reverse order, not a Source Items/intrinsic Prog theorem. Final unchanged full
wrapper PASS0:1126default/262Suite/SolKey377parsed/131read-bearingcovered,
aggregateRSS1721756KiB/diskgrowth266240bytes/newOOMdelta0. Fresh actual
Lean4.24.0commit797c613/Lake5.0.0-src+797c613/KeySort2jobs PASS.

C67 strict/trust/layer/orphan/lane/complete-fixture/script checks PASS,73combined
admission/corruption tests including20newmutation-admission tests. Scoped exact
standard-only pin validation PASS1084/145ownedmodules; raw global inventory
FAIL1/1443unrecorded=359published+1084owned/0unsafe. Additive proposed pins
are coordinator reconciliation evidence only, no reserved-registry modification.
Raw strict docs FAIL1/83 findings, COMPLETE current/public bytes identical and
zero-owned-new comparison separatelyPASS; frozen no-new retains11incoming/FAIL1.
Warm strict times0newSuite modules; independently all262current/C31source/
fixture/toolchain bytes and fresh67versions match, retaining26cold/max160sunder
300 timing only, not new cold coverage. All3855C66sealed entries reverified.
Final idle resource sample874676224availablebytes retains512MiBreserve plus
96MiBforecast; old and newOOM/cumulativepeak history remains explicitly separate.
No guard, expected observation, admission decision or source ownership changed.


### C68 — actual fixed declaration/write/delete programs (PARTIAL)

Current C67 source inspection reproduced separate Source statement horizons and
word append, with no combined Source RItems/intrinsic Prog. Existing Source
execItems consumes fuel at each statement, so the length1 case cannot use the
minimal constructor horizon followed by two minimal mutations. SourceUintFixedFuel
proves actual zeroElems(n+extra+1)/zeroVal(n+extra+3) execution by induction on the
DECLARED length, retaining exact n elements and existing Data.array some n.
Caller extra fuel is execution input, not a proof budget increase, monotonicity
axiom, source admission cutoff or new evaluator/allocator. These kernel facts
include0 but grant no zero-length Source admission.

source_uint_fixed_program_word now executes ONE existing Source.RItems at n+7:
actual declaration n+6, reached RHS-first indexed assignment n+5, then reached
primitive default/unit delete n+4. All stages use ORIGINAL Γ.length parameter
count despite Source local cons; intrinsic heap extension/local push and word
local offsets are derived separately. Actual Source default/decl producers and
C67 resolved operation certificates derive the mid/write/delete states, typed
fixed observers, MemOK, complete word StateRepr/AllocatorRepr, old object/world/
local/stack frames and whole word append from INITIAL alignment/ownership/space.
Existing typed Prog executes the matching declaration/assign/delete on those
same intrinsic heaps. No desired final relation, supplied suffix run, arbitrary
conversion certificate, global address injection, new AST/IR/state/interpreter
or reserved constructor/copy implementation is introduced. Program definitions
are ordinary values of EXISTING Source.RItems and Prog, not alternate semantics.

source_uint_fixed_program_reject uses a separately aligned later index, initially
at or beyond n. Actual constructor and valid first write derive the reached
Source observer, locals, intrinsic heap, StateRepr and allocator. The next real
Source expression panics with index bytes, its statement/whole RItems retain
EXACT first-write globals and empty caller locals. Intrinsic Prog and whole word
append revert; those outcome types expose no failing final heap/machine. No
suffix object/state, Source/word panic-payload equivalence or transaction rollback
is asserted. Source zeroVal is not a general new-expression/compiler theorem.

Independently inhabited controls have old fixed[7]/neighbor[9], repeated old
aliases, TWO numeric locals, Source allocation/MemOK and complete object-word
ownership. Runtime program_runs/late_rejection apply actual general producers;
selected_cases directly observes successful Source RItems/intrinsic Prog and
final last-element0 at1/3/33. Complete fresh lists, old Source tables/typed IDs,
all retained Source locals/alias/root identities, both full16wordframes, caller99,
stack77, numeric slots4/5, new pointer slot6, allocator/freepointer and logical32
are exposed. Length3/index2 materialwrite2 then clear0, reverse WORD order leaves2;
length33/index32 writes32. No Source reverse program is claimed. Previous C67
vectors/guards and ALL earlier fixture source remain unchanged.

changed_prefix_panic executes actual Source10/typed Prog error after writing
[0,0,2], with a real Source read2 of that prefix plus old7/9 frames. Thus skipped
first-write/rollback/cleared-suffix observations disagree. changed_prefix_timeout
uses length1 with separate index0/RHS7: Source6 allocates and actually writes7,
then deletion times out. It retains that represented child/read7 and old objects;
this is an actual low-horizon outcome, not a new depth/fuel restriction. raw_zero
executes existing zero-length KERNEL syntax at Source7: allocation succeeds, first
index rejects and no delete suffix runs. Raw headerless target reservation uses
one padding cell/free33, then rejects. It is explicitly NOT zero-length Source
admission or an all-profile allocation theorem. Positive headlines retain0<n.

Focused checks use only the same supported capped runner; per-file MCP and goal
get/update remain unavailable. Exact public axiom guards and gate outcomes below
record final validation. Syntax/normalization failures remain raw failures. One
dependent controls attempt replayed a still-failing prerequisite; its failed log
is retained and does not establish a control pass. No source/statement/premise/
observation/proof/fuel/node/stack/test/time budget was weakened. All3953C67sealed
hashes preflight verified; same runtime/image/mounts/cache/toolchain/writer lock,
852463616available admitted96MiB above512MiBreserve. CPU0/Lean-j1/threads1,
aggregate12GiBnoswap/16GiBparent/OS headroom and cacheOFF remain unchanged. C60
and C67OOM history remains failed history; no old seal/cache/source is deleted.

All original G32/G33/G34/G35.01/.03/.04/.05 and BackfillA/B remain PARTIAL;
G35.02/.06 remain BLOCKED. Fixed supported programs do not close general
physical-byte/graph/path/effect representation, all-profile/reference constructors
or target allocation failures, ABI/storage/deep-copy/liveness, reserved copying
or final Source/V10/target composition. Kernel/symbolic-word checks are distinct
from external compiler/EVM tests. The existing goal remains BLOCKED unchanged;
no goal mutation/integration or independent-queue exhaustion is claimed.

C68 final refined controls08 PASS238jobs/RSS1041992KiB/newOOMdelta0, with12exact
standardtrio public guards and no sorryAx. Final success/rejection/controls also
explicitly derive unchanged Source ex/events/logs/fnLocals from the actual write/
delete frame chains; no added premise. Both independent read-only finder and
skeptic SOURCE/control/document/script reviews PASS, including these four frames.
Initial full01 PASS is retained for its earlier tree only. FINAL full02 PASS0
covers refined source:1130default/262Suite/SolKey377parsed/131read-bearingcovered,
aggregateRSS1667100KiB/diskgrowth266240bytes/newOOMdelta0. Fresh actualLean4.24.0
commit797c613/Lake5.0.0-src+797c613/KeySort2jobs and actualcacheOFF/threads1 PASS.

C68 strict/trust/layer/orphan/lane/complete-fixture/script checks PASS,89combined
admission/corruption tests including16newfixed-program admission tests. Scoped
exactstandard-only pins PASS1096/149ownedmodules; raw globalinventory FAIL1,
1455unrecorded=359published+1096owned/0unsafe. Additiveproposals are evidence for
coordinator reconciliation, no reserved inventory/ledger modification. Rawdocs
FAIL1/83completefindings, COMPLETE current/public byte equality and zero-owned-new
separatelyPASS. Frozen no-new remainsFAIL1/11incoming. Warmstrict times0newSuite
modules; independently all262current/C31source/fixture/toolchain bytes and actual
68versions match, retaining26cold/max160sunder300 only, not new timing coverage.
All3953C67sealed entries reverified. Finalidle843120640availablebytes retains
512MiBreserve+96MiBforecast; samecaps/cache/sourceoutputs preserved. ALLC68execs
havezeroOOMdelta; historical C60/C67 max15158/oom5/kill5/cumulative12GiBpeak and
DockerOOMKilled remain failed history, not current run RSS or new resource stops.

Original-queue reassessment: fixed local alias/rebinding followed by reached
mutation is another concrete G34/BackfillB application to investigate. Existing
source_local_alias_run/memOK execute Source locals.set without heap changes;
source_alias_word uses the older RefArrayStateRepr, whereas fixed C68 uses Objects
StateRepr. Published Objects.PtrFrag.rebind supplies the compatible wholeword
producer. An owned SourceUintFixedAt/Objects alias bridge and reached SourceItems/
Prog application are not implemented here; consume those existing interfaces
read-only, without duplicating a producer or asserting queue exhaustion. General
Source graphs/physical bytes/all-profile construction/failure and all previously
named reserved/final composition obligations remain genuinely open.


## C69: genuine fixed-reference local rebinding and reached mutation (partial)

Owned modules `Solidity/Backend/MemoryOps/SourceUintFixedAlias.lean`,
`Solidity/Backend/MemoryOps/SourceUintFixedAliasProgram.lean`,
`Solidity/Backend/MemoryOps/SourceUintFixedAliasFailure.lean` and
`Solidity/Backend/MemoryOps/SourceUintFixedAliasControls.lean` close the specific
C68 fixed-local bridge gap. Published Source local assignment and Objects pointer
rebind producers remain read-only. INITIAL genuine Source some-n observer, same
represented source/typed local pointer, Source MemOK, Objects StateRepr and
AllocatorRepr plus positive local base derive the SAME reached reference, actual
Source expression/statement, intrinsic rebindMem and existing pointer load/store
word execution. Typed scalar/local frames are derived, no caller global address
injectivity or final-agreement premise. Both heaps, world/events/logs/function
locals, old addresses/objects, stack and allocator are framed across rebinding.

`source_uint_fixed_alias_program_word` feeds those actual reached states into
existing fixed assignment then primitive deletion, deriving ONE Source RItems,
intrinsic Prog and whole existing word append, fixed correspondence, MemOK,
allocator and all other local/object/address/world frames. Caller horizon h
executes statements h+6/h+5/h+4 inside Items h+7 with ORIGINAL parameter count.
Unrelated source-address and logical typed-ID frames are separate local facts;
no global map injection, pairwise disjointness or every-stage desired relation
is assumed. The kernel statements quantify runtime fixed n and indices; they
never admit zero-length Source merely because low-level syntax is expressible.

Controls independently construct three existing source objects/typed heap and
Objects word representation: LEFT=[7,8,7], RIGHT=[9,10,9], neighbour=[11,12],
retained LEFT alias and saved [77,88] stack. Both actual Source pipeline configurations execute the forward
Source Items and typed Prog; arbitrary valid index/value instances derive full
source tables, all object contents/identities and final representation. Concrete
index2/value42 complete16word vectors expose pointer replacement, material RIGHT
write then zero deletion, stable old aliases/neighbor/cursor40 and saved stack.
The word-only reordered run writes LEFT42, then redirects and clears RIGHT0;
the retained LEFT content discriminates it. Its stale first write independently
executes in Source/intrinsic/word and writes LEFT42, rather than merely stipulating
corrupted contents. No complete reversed Source Items/Prog theorem is claimed.
Same-pointer and self-alias Source execution, shared-alias word mutation and
actual selected/retained Source reads9 versus7 are proved. No fresh allocation,
deep copy, alternate evaluator or Source admission restriction is introduced.

`source_uint_fixed_alias_reject` derives actual successful rebinding then bounds
rejection from INITIAL index>=n. Whole Source error exposes unchanged globals
and empty caller locals; rebound local is observed only in the successful prefix.
Intrinsic/word reverts expose no final heap/machine and no payload equivalence or
rollback claim. The horizon6 control REALLY rebinds, writes RIGHT42, then times
out at deletion; Source error retains changed globals. Source success requires
horizon7 here, an execution observation, not an increased fuel/proof/test budget.

C69 focused final closure PASS220jobs, exact guards13 (one axiom-free local helper,
others standard trio), zero new OOM. Earlier syntax/canonical-word/opaque typed
projection/append matching/solved-goal diagnostics are retained as failed exits;
one controls01 prerequisite replay occurred before inspection and is retained,
not counted as a proof pass. New lane script tests exact pins and dropped/unsafe/
renamed guard corruption. No old fixture/control/vector or expected observation
was edited. Final full/static gates and independent SOURCE/artifact reviews are
pending at this writing; exact final outcomes are appended below before commit.

Original G32/G33/G34/G35.01/.03/.04/.05 and Backfill A/B remain PARTIAL; G35.02 and
G35.06 remain BLOCKED on reserved memory-to-storage/final V10/Source/target
composition. This advances fixed-reference path/rebinding/identity transport,
not physical-byte/all-profile construction/checked target allocation failure,
general reference graphs/ABI/storage/deep-copy/emitted loops or whole compiler.
Kernel independent Source plus symbolic-word proofs are not external solc/EVM
execution. Existing persistent goal BLOCKED unchanged; get/update APIs and Lean
MCP diagnostics are unavailable, no goal status mutation, no queue exhaustion.

C69 final full01 PASS0 covers the registered final Lean tree:1134default/262Suite,
SolKey377parsed/131read-bearing covered. Actual Lean4.24.0 commit797c613/Lake5.0.0-
src+797c613/KeySort2jobs PASS, selected exec vars show threads1 and optional cache
OFF. Focused01 PASS220jobs/exact13new guards (one empty+12standardtrio), scoped
owned1109pins/153modules standard-only. Strict/trust/layer/orphan/lane/complete
fixtures PASS,105combined admission/corruption tests PASS including16newfixedalias
tests. Warmstrict times0newSuite modules; independently every262current/C31source,
fixture/toolchain bytes and actual69versions match retained26/max160sunder300,
which is retained keyed cold evidence only, not new cold coverage.

Rawdocs FAIL1/83 completefindings remains byte-identical to consumed public C31;
complete zero-owned-new separatelyPASS. Frozen no-new remainsFAIL1/11incoming.
Rawinventory FAIL1/1468unrecorded=359published+1109owned/0unsafe. Additive owned
pin proposals only, reserved registries/ledger unchanged. Both independent
read-only finder/skeptic source/control/script/doc reviews PASS after fixing the
finder's wording ambiguity: complete reordered execution is word-only, not a
reversed Source Items theorem. Artifact reviews are separately required after
commit. All failed diagnostics/receipts remain, no unsafe elaboration artifact is
accepted: final exact pins have no sorryAx. C69 has zero new OOM on EVERY observed
exec. C60/C67 cumulative OOM5/peak12GiB history is retained separately. Finalfull
aggregateRSS1586720KiB/diskgrowth270336bytes; finalresource812756992available bytes
preserves512MiBreserve+96MiBforecast. Same container/image/mount/caps/cache identity,
no worker besides idle sleep after gates; no new runtime or cleanup.

Queue reassessment: the fixed alias bridge and reached operation application are
now supplied for arbitrary intrinsic fixed n/valid indices under explicit initial
Source/Objects assumptions. The next independently supported context application
to investigate is declaration of a fresh fixed local then assigning an OLD local
to that new root, followed by reached index mutation; C66/C68 establish Source
cons versus intrinsic append and constructor output, C69 consumes initial pointer
alignment. That exact context-changing rebind application is not established by
this checkpoint. Broader general shape/path/graph/default/copy/target prerequisites
remain as above; no independent-queue exhaustion, integration, goal reactivation
or whole-assignment completion is asserted.


## C70: actual fixed declaration, fresh-root rebinding and reached mutation (partial)

`Solidity/Backend/MemoryOps/SourceUintFixedDeclareAlias.lean` consumes the existing
fixed constructor and C69 alias program. From INITIAL MemOK, genuine positive
fixed n, scalar local alignment, valid index, Objects StateRepr/AllocatorRepr,
positive local base, actual cursor+max1n space and new-local frame capacity, it
derives declaration, OLD-local alias to the genuinely NEW root, write then delete.
ONE existing Source RItems uses ORIGINAL parameter count throughout all four
statements; Source cons and intrinsic heap weakening/push and word-frame slot are
handled separately. No intermediate observer, run or final agreement is a premise.
Existing typed Prog executes the same four reached stages; complete published
word constructor/pointer/index/default-write append actually runs. Fresh identity,
new/old local pointers, all old typed-object/occupied Source-address frames, fresh
observer, MemOK/StateRepr/allocator/stack/cursor and final ex/events/logs/fnLocals
are derived. No constructor algorithm or reserved Source/Evm producer was edited.

Source Items n+8 is a SUFFICIENT execution horizon, not a minimal-horizon theorem
or new admission cap. Declaration statement uses n+7; the three reached statements
use n+6/n+5/n+4. This slack reconstructs the pure-local expression statements with
the ORIGINAL parameter count, rather than assuming the new context length equals
it. Intrinsic old locals use shifted indices and actual TEnv.wk; Source locals use
cons. Zero-length Source admission remains unproved/unchanged. General reference
construction/checked target allocation failure/physical bytes stay outside scope.

`Solidity/Backend/MemoryOps/SourceUintFixedDeclareAliasControls.lean` independently
inhabits the same old populated LEFT=[7,8,7], RIGHT=[9,10,9], neighbour=[11,12] and
shared backup alias, then actually declares positive fixed3 root3. Both Source
pipeline configurations execute Source Items11 and corresponding typed Prog from
those initial inputs. Runtime k<3 and canonical values are supported by the
control application; the generic theorem quantifies arbitrary positive n. Fresh
initial zeros become42 at index2, then0; old Source tables/typed contents remain
unchanged, old destination points to fresh3 while retained alias stays0, and new
local agrees with the redirected old local. Full20word vectors retain all16old
observed cells and append new local7 plus fresh40/41/42, with cursor43 and saved
[77,88] stack. Skipped rebind is a WORD-only contrast clearing OLD LEFT rather
than fresh. Actual reached Source memElem reads42 then0 at fresh3, while old0
still reads7; wrong old-address correspondence for the fresh intrinsic root is
refuted from those computed reads, not assumed injectivity or a desired result.
A Source Items7 timeout executes the actual insufficient first declaration and
exposes no allocated suffix; no rollback/panic-byte or word-error state invented.

Earlier fixture/control/vector/guard files remain unchanged. Six new exact
standard-trio guards and lane-specific evidence-admission/corruption tests are
required; kernel proofs establish executions, script tests only check evidence
admission. C70 focused01 PASS238jobs before explicit world-field return extension;
final focused/full/static/reviews are recorded below when complete. All failed
syntax/type/canonical matching/local proof-shadowing/Source equality-instance
attempts stay retained as failures; no unsafe elaboration result accepted.

Original G32/G33/G34/G35.01/.03/.04/.05 and both Backfills remain PARTIAL; G35.02
reserved memory-to-storage and G35.06 final Source/V10/target remain BLOCKED.
This context application is not all-profile allocation, arbitrary paths/graphs,
ABI/storage/fresh deep-copy/emitted loops/liveness or whole compiler closure.
Kernel/symbolic-word evidence is not external solc/EVM testing. Goal BLOCKED and
its identity/status/counters unchanged; no integration or queue-exhaustion claim.

C70 FINAL focused02 PASS238jobs after explicit generic world-frame return,
RSS1027544KiB/newOOM0, all6exact new guards standardtrio. Full01 PASS0 on final
registered Lean tree:1136default/262Suite/SolKey377parsed/131read-bearing covered.
Actual Lean4.24.0 commit797c613/Lake5.0.0-src+797c613/KeySort2jobs, selected threads1
and actual cacheOFF verified. Strict/trust/layers/orphans/lane/complete fixtures
and113combined script/corruption tests PASS, including8newdeclare-alias admission
tests. Scoped1115ownedpins/155modules standard-only PASS; rawglobalinventory stays
FAIL1/1474unregistered=359published+1115owned/0unsafe. No reserved registry edit.
Rawdocs FAIL1/83 completefindings remains byte-identical to consumed public C31;
zero-owned-new separatelyPASS; frozen comparison remainsFAIL1/11incoming. Warm
strict times0newSuite modules; every262current/C31source/fixture/toolchain byte
and actual70versions independently match retained26cold/max160sunder300 only,
not new timing coverage. Both independent read-only finder/skeptic SOURCE/control/
script/document reviews PASS with no confirmed defects; artifact review separate
postcommit. World ex/events/logs/fnLocals equalities now explicitly returned from
actual reached C69 frame chain, without adding a premise.

All13C70exec receipts retain6actual failed diagnostics and0newOOM. Historical
C60/C67 cumulative OOM5/12GiBpeak remains failed history, not this exec RSS. Final
full aggregateRSS1575172KiB/diskgrowth266240bytes, finalresource783097856available
bytes preserves512MiBreserve+96MiBforecast; same12GiB/no-swap child/16GiBparent,
OSheadroom/runtime/cache/mounts/source outputs and all prior seals preserved.
No old fixture/vector/guard modified. Exact type/context syntax, heap-name
shadowing, canonical projection and Source.Val non-DecEq diagnostics were repaired
distinctly; no failure relabeled passed or proof/resource budget increased.

Further original-queue investigation (not an exhaustion claim): existing
`Solidity/Backend/MemoryOps/SourceUintCompound.lean` proves numeric checked compound
mutation only through the dynamic SourceUintMemoryAt/type none. C66's genuine
SourceUintFixedAt/type some-n cannot be obtained by changing the intrinsic ArrTy
argument there. Published `Solidity/Evm/MemoryCompound.lean` exposes generic
compoundAssign_eq_write for actual ArrTy, while Objects ArrayRepr.read and
PtrFrag.write supply read/write constituents read-only. A genuine fixed Source
compound-success/overflow and compatible Objects target application is not
implemented by C70; its exact Source eval order, bounds and producer premises
must be checked before a new application. Reserved-copy/physical-byte/all-profile
constructor/target-failure/generalgraph/ABI/storage/deep-copy/final Source-V10-target
obligations remain open; no original parent or persistent goal is declared done.


## C71: genuine fixed numeric compound updates at reached states (partial)

New owned modules `Solidity/Backend/MemoryOps/SourceUintFixedCompoundSource.lean`,
`Solidity/Backend/MemoryOps/SourceUintFixedCompound.lean`,
`Solidity/Backend/MemoryOps/SourceUintFixedCompoundSequence.lean`,
`Solidity/Backend/MemoryOps/SourceUintFixedCompoundBounds.lean` and
`Solidity/Backend/MemoryOps/SourceUintFixedCompoundControls.lean` apply published
producers read-only. The genuine Source type stays array memory int.u256 some-N,
with intrinsic RefTy.fixed. No dynamic-type cast or duplicate evaluator/allocator/
operator/representation is introduced. Actual Source compound execution evaluates
RHS, lvalue, represented OLD cell, converted RHS, binVal, then write. The old cell
comes from INITIAL SourceUintFixedAt/typed contents; it is not a desired reached
value or compiler-result premise. Published source_uint_add/overflow supply exact
numeric conversion/arithmetic. Success supports checked OR unchecked IN-RANGE
addition only. Overflow explicitly requires F.checked=true, yielding arithmetic
panic; no unchecked wrapping agreement with the checked intrinsic/word operation.

`fixed_uint_add_certificate` composes EXISTING Objects ValFrag.read/binary and
PtrFrag.write. Their published correctness uses actual fixed readPrimitive and
binaryValue_correct while preserving the full Objects representation/ownership,
then derives full Objects StateRepr and KeepsAllocator from the actual store.
The postrepresentation is not weakened to legacy primitives. Source MemOK, locals,
old distinct typed-object/source-address frames and all four world fields derive
from the same actual fixed write. Pure local operands matter: word arithmetic
reads OLD before its RHS local whereas Source evaluates RHS first. This is not
an arbitrary side-effectful order theorem. Whole code and exact bounds/overflow
revert outcomes are proved; no panic-byte/returndata or post-revert machine claim.

`resolved_uint_fixed_add_twice_word` feeds the first actual output into the second
operation. INITIAL range cases old+rhs and (old+rhs)+rhs suffice; actual set-self
lookup derives second OLD and fixed length preservation derives capacity. ONE
existing Source Items/typed Prog/fullword append executes both stages. Selectable
ORIGINAL nps is retained by rebuilding pure expression statements. Source Items
fuel+6 uses statements fuel+5/fuel+4, a sufficient execution horizon without a new
admission/fuel/depth/length cap or budget increase. The companion late-overflow
law derives second failure from that actual first write; Source error retains its
changed globals while intrinsic/word errors expose no final heap/machine/rollback.

Both Source pipeline configurations execute a REAL C69 reference rebind then
RIGHT9→51→93, retaining LEFT=[7,8,7], neighbour=[11,12], backup aliases, complete
Source tables, local identities, allocator/cursor and saved [77,88] stack. Frozen
OLD would incorrectly repeat51. Checked high-word control first computes
9+(W-10)=max, then the ACTUAL reached max+(W-10) overflows before writing; frozen
initial9 would still succeed. Actual Source/typed/wholeword successful prefixes,
exact panic/error boundary and changed Source globals are observed. Canonical
zero RHS executes successfully without erasing fixed type or modifying prior
fixtures. Endpoint and low-horizon timeout are distinct from arithmetic overflow.

Actual positive fixed declaration then reached zero→42→84 is also composed as ONE
Source RItems with ORIGINAL parameter count, typed Prog and full published word
append from initial constructor/space/frame/SourceMemOK/Objects premises. Source
cons versus intrinsic weakening/push, fresh identity, default OLD zero, old roots,
occupied Source addresses, locals, world, stack and allocator are DERIVED. This
application quantifies arbitrary runtime positive n/k under existing index/space
validity, not a fixed payload/depth admission cutoff. Length33/index32 really
updates the fresh last cell; ALL33 target payload words are observed at the actual
represented base, with exact endpoint33 and stale old-length3 root rejection.
The raw empty-kernel Source/typed observation gives bounds failure and explicitly
DOES NOT establish zero-length Source admission or target allocation failure.

Complete20word observations preserve all16 earlier observed cells plus new local7
and fresh payload40..42. They cover actual reference rebind9→51→93, skipped-rebind
WORD-only LEFT7→49→91, actual max prefix before revert, and the SAME declaration/
new-local program zero→42→84 with cursor43 and saved stack. Source declaration
branch selects the NEW local; C69 branch rebinds an OLD local to an existing root.
No combined declaration→OLD-local rebind→compound Source theorem is claimed here.
The distinct valid fixed types of new-n versus old-length3 locals are observed in
separate typed conjuncts, never a heterogeneous list cast. Existing C66-C70
controls/vectors/guards and all sealed evidence remain unchanged.

C71 focused01 PASS226jobs/RSS1078972KiB/newOOM0;20new exact standard-trio guards,
no sorryAx. New evidence-admission script checks exact heads/axiom sets and applied
missing/unsafe/renamed-guard mutants; those scripts are not execution proofs.
Per-file Lean MCP and goal get/update APIs remain unavailable; bounded serial
closure used, persistent BLOCKED goal never mutated. Final gates/reviews recorded
below before commit. Every actual diagnostic failure and both automatic approval
rejections are preserved: rejected commands did not execute. Complete named proof
facts replaced the flagged draft/tuple goal-slot proposals, with no policy bypass,
expected observation change or unsafe axiom. One pre-write editor assertion failed
before mutation and controls07 replayed the OLD passing control tree; it is not
final refined evidence. No new OOM occurred; C60/C67 historical five kills remain
failures, separately from this exec RSS and per-exec memory.events deltas.

ALL original G32/G33/G34/G35.01/.03/.04/.05 and Backfills A/B remain PARTIAL;
G35.02 reserved-copy and G35.06 final Source/V10/target remain BLOCKED. Physical
bytes/all-profile construction/checked target allocation failure/general paths/
references/graphs/ABI/storage/deep-copy/emitted loops/liveness and final composition
remain genuine unfinished obligations. This kernel/symbolic-word application is
not external solc/EVM testing, Source profile closure, queue exhaustion, goal
reactivation or whole-lane completion. No reserved owner, global registry/ledger,
predicate/refusal/observation or proof/resource/test budget was changed.

C71 FINAL full01 PASS0 on the registered final Lean tree:1141default/262Suite,
SolKey377parsed/131read-bearing covered. Actual Lean4.24.0 commit797c613/Lake5.0.0-
src+797c613/KeySort2jobs and selected actualthreads1/cacheOFF PASS. Final focused01
PASS226jobs/all20new exact standardtrio guards/RSS1078972KiB/newOOM0. Strict/trust/
layers/orphans/lane/completefixtures and133combined script/corruption tests PASS,
including20newcompound evidence-admission tests. Scoped1135ownedpins/160modules
standard-only PASS; rawglobalinventory staysFAIL1/1494unregistered=359published+
1135owned/0unsafe. No reserved registry/ledger edit. Rawdocs FAIL1/83 complete
findings remains byte-identical to consumed public C31; zero-owned-new separately
PASS. Frozen comparison remainsFAIL1/11incoming. Warmstrict times0newSuite modules;
every262current/C31source/fixture/toolchain byte and actual71versions independently
match retained26cold/max160sunder300 only, not new cold timing coverage.

Separate independent read-only finder/skeptic final SOURCE/control/script/doc
reviews PASS with no confirmed defects. Full Objects preservation, initial-only
arithmetic case premises, reached late failure and arbitrary-positive fixed
constructor application were independently scrutinized. Reviewer limitations
retain pure-local ordering, successonly in-range when unchecked, rawempty not
admitted, and no combineddecl→OLDlocalrebind→compound Source program. Artifact
reviews remain separate after commit. Every30C71exec receipt has newOOMdelta0;
13actual proof failures retained. Both rejected commands never executed; safe
named completed proof facts subsequently checked with exact guards. The failed
pre-write editor assertion and old-tree controls07 replay are explicitly retained,
not final source evidence. Historical C60/C67 cumulative OOM5/12GiBpeak remains
failed history, not this exec RSS. Full aggregateRSS1583776KiB/diskgrowth270336bytes,
finalresource750682112available bytes preserves512MiBreserve+96MiBforecast and OS
headroom in the SAME12GiB/no-swap child/16GiBparent/runtime/cache/lease. No cleanup,
new runtime or proof/fuel/node/time/TestSuite budget change.

Original-queue reassessment: fixed compound execution/overflow and actual existing-
root rebinding plus separate fresh-declaration applications are now supplied.
A distinct possible G33/G34/BackfillB application remains the COMBINED declaration
then OLD-local rebinding to NEW root then compound updates, in ONE Source program.
C70 gives context-changing declaration/rebind/ordinarywrite-delete and C71 exposes
nps-parameterized compound pairs, so these published owned outputs should be
investigated together rather than called unavailable or duplicated. General
Source INC/DEC and arbitrary side-effectful paths/graphs are not proved here.
This is a further supported investigation, NOT a queue-exhaustion or full-lane
completion assertion. All previously named G32-G35/reserved/final prerequisites
and raw mandatory global-gate failures remain open; goal BLOCKED unchanged.

C71 refinement: initial staged diff FAIL2 found two trailing spaces in the new
Source helper, despite earlier unstaged diff being clean before new-file staging.
Rawlog/assertion failure retained, no commit was made then. Removed ONLY trailing
whitespace; final focused02 PASS226/RSS917256KiB and FINAL full02 PASS0/1141default/
262Suite/SolKey377-131 cover the corrected tree. Earlier full01 PASS is earlier-
tree evidence only. Final full02 warm sampleRSS79752KiB/processcount1/diskgrowth
266240bytes/newOOM0; earlier full01 RSS1583776KiB separately retained. All32C71execs
newOOMdelta0,13proof failures plus stagedFAIL2/editor failures retained. Refined
strict/trust/layers/orphans/133corruptiontests/stageddiff PASS; rawdocs/inventory
failures and exact public/frozen comparisons remain unchanged and separate.


## C72: fixed declaration, OLD-local rebinding and reached compound pair (partial)

Original G33/G34 and Backfill B application. New owned modules are
[SourceUintFixedDeclareCompound](../../Solidity/Backend/MemoryOps/SourceUintFixedDeclareCompound.lean),
[SourceUintFixedDeclareCompoundOverflow](../../Solidity/Backend/MemoryOps/SourceUintFixedDeclareCompoundOverflow.lean),
and [SourceUintFixedDeclareCompoundControls](../../Solidity/Backend/MemoryOps/SourceUintFixedDeclareCompoundControls.lean).
No reserved Source/Evm/Bridge producers, global inventories or old fixtures changed.
The frozen base remains fb379ae20f10e2c92113453ddd9d40d8f2efbe09; consumed public
prerequisite remains 2fe1f8932f96be15b00df03ba2cde46f64a87758; parent C71 is
30fdffac2907933eb7057383c04a0505c1b9ae74. The persistent goal stays BLOCKED unchanged.

`source_uint_fixed_declare_compound_word` derives one actual Source RItems program:
positive fixed uint declaration, OLD-local rebinding to the NEW root, then two
reached compound additions. The matching existing intrinsic Prog and whole
published constructor/pointer/read/binary/write word append are proved. Genuine
Source STy some n and intrinsic RefTy.fixed n are retained. The Source cons and
typed weakening/push contexts remain separate. ORIGINAL Source parameter count
Gamma.length is used throughout; the complete program has sufficient horizon n+8,
not a minimal-fuel or public admission claim. The two expression horizons are n+4
and n+3; default construction and alias statement use n+7 and n+6 respectively.

INITIAL premises: positive n, scalar local/index/RHS alignment, actual k<n,
canonical uint RHS, inRange(value+value), Source MemOK, full Objects.StateRepr and
AllocatorRepr, positive base, cursor+max(1,n)<W and b+(Delta.length+1)<=frame.
The actual allocator proves fresh OLD0 at the selected cell; no caller-supplied
OLD value, desired reached observer or preservation equality is assumed. Existing
Source/typed alias producers derive operand framing and strong reached representation;
the C71 pair derives its second OLD from the first real write. OLD destination
pointer alignment is unnecessary because actual rebinding overwrites that local.
All other Source/typed locals, every old typed object, occupied old Source address,
stack, allocator cursor and Source ex/events/logs/fnLocals are derived as frames.
No global address injectivity is added. The success theorem covers checked or
unchecked IN-RANGE arithmetic only; unchecked overflow agreement is not claimed.

`source_uint_fixed_declare_compound_overflow_word` uses checked=true and INITIAL
out-of-range double(value), deriving actual fresh0->value success then second
arithmetic panic from that changed prefix. Source Items retains its real prefix
globals; intrinsic Prog errors and whole symbolic word code reverts. Only the
legitimate successful target prefix has StateRepr/AllocatorRepr/stack/contents.
No suffix machine or transaction rollback/panic-payload equivalence is invented.
`source_uint_fixed_declare_compound_timeout` proves actual entire-program timeout
before allocation/rebinding for fuel<=n+4, with initial globals retained.

Controls independently inhabit old LEFT=[7,8,7], RIGHT=[9,10,9], neighbor=[11,12]
and Source/Objects/MemOK/allocator representations. BOTH original pipelines execute
the combined declaration/rebind/fresh0->42->84 program for every runtime k<3.
Complete Source object tables, all payload cells, reached full locals, typed old/
fresh identities, world frames and strong word allocator/stack evidence are kept.
OLD retained LEFT and the neighbor stay unchanged while the rebound old local
and new declaration local point to fresh ID3/Source address3. Complete20word
constructor/alias/first/second vectors include all prior16 cells plus local7 and
fresh40/41/42. WORD-only skipped alias changes LEFT7->49->91 and leaves fresh0;
WORD-only delayed alias leaves LEFT49 and fresh42 instead of the correct fresh84.
These negatives are not falsely labeled Source whole-program executions.
The actual checked max case gives fresh0->MAX then panic, old contents retained;
frozen initial fresh0 would incorrectly succeed again.

`boundary33` first executes a separate certified real length33 constructor,
then applies the actual combined program at that REACHED state: the old declared
ID3 is redirected to second fresh ID4, old ID3 stays all-zero, fresh index32 goes
42->84. Every33 payload word, typed/Source reads and endpoint33 panic are proved.
Its statement includes the actual first constructor run, actual combined target
run and entire two-prefix word append, not just an existential representing
machine. The first Source declaration and subsequent Source RItems are explicitly
separate executions; no larger two-declaration Source Items theorem is claimed.
A separately inhabited initial frame9 is necessary for two new locals; this is an
actual ownership capacity premise, not a changed proof/resource budget. Logical
element32 is not a physical-byte encoding claim. Generic laws quantify runtime n;
no public payload/depth cutoff or zero-length Source admission is introduced.

Independent read-only finder preliminary mathematical/control/script PASS found no
defect. Skeptic found boundary33 dropped its already-derived Evm.run clauses from
the conclusion; these exact first/combined/whole runs were added while preserving
every existing observation. Final source/artifact reviews and gates are recorded
in additive /workspace/v11-memory-operations-evidence/checkpoint72 evidence.
Automatic approval rejected an unexecuted test-generation command as potentially
dropping C71 cases; the safe NEW script retains all C71 cases and appends C72 cases,
leaving the original script byte-unchanged. No permission/policy change or bypass.
Earlier focused failures and the preflight identity assertion remain evidence;
none is reclassified as a pass. All new guards require exact standard axiom sets.

ALL original G32/G33/G34/G35.01/.03/.04/.05 and both Backfills remain PARTIAL;
G35.02 and G35.06 remain BLOCKED on reserved copy/final composition prerequisites.
Physical bytes, all-profile constructors/target allocation failures, general paths/
reference graphs, ABI/storage/deep-copy/recursive liveness and final Source/V10/
target correctness remain unfinished. These are kernel and symbolic-word proofs,
not external solc/EVM validation or original-lane completion. Global docs and axiom
inventory debt remain raw failures, distinct from complete public-byte equality
and exact owned pin proposals. No exhaustion of independent work is asserted.

C72 final validation: focused03 PASS244jobs; literal full01 PASS1144default/262Suite,
SolKey377parsed/131covered/OK and exit0. Actual Lean4.24.0 commit797c613 and
Lake5.0.0-src+797c613 plus KeySort2job PASS observed with cacheOFF/thread1.
Full sampled aggregate RSS 1587628KiB, disk growth
274432bytes, newOOMdelta0; cumulative
session peak12GiB and historical5OOM kills remain qualified failure history.
All19C72exec receipts retain 12failed proof gates;
none is reclassified green. First preflight assertion and unexecuted approval
rejection remain separately retained. No resource/proof/time budget was increased.
Structural/trust/lane/completefixtures PASS;165script/corruption tests PASS.
Seven new exact standard-trio guards give1142owned pins/163modules, with all1135
C71owned sets byte/exact-row unchanged. Raw inventoryFAIL1/1501unregistered=
359published+1142owned/0unsafe; coordinator additive registration remains proposed,
not a global pass. Raw docsFAIL1/83finding rows; complete consumed-public bytes
match separately, frozen72rows+11incoming comparison remains FAIL1. Warmstrict
times0newSuite modules; all262source/fixture/toolchain hashes match retained C31
cold26/max160seconds<300 only, not newcoldcoverage. Both independent read-only
final source/control/script/doc reviews PASS after boundary-run fix; artifact
reviews follow actual commit/export. No external compiler/EVM execution inferred.


## C73: actual fixed prefix/postfix increment and reached MAX overflow (partial)

Continued original G34/Backfill B after sealing C72. Owned modules
[SourceUintFixedIncrement](../../Solidity/Backend/MemoryOps/SourceUintFixedIncrement.lean)
and [SourceUintFixedIncrementControls](../../Solidity/Backend/MemoryOps/SourceUintFixedIncrementControls.lean)
consume published Source RExpr.incDec and MemoryCompound.incrementMemory_eq_compound,
Objects.ValFrag read/binary and PtrFrag.write read-only. No new evaluator, arithmetic
producer, heap, AST, source profile exclusion or reserved-owner edit. Frozen base
fb379ae20f10e2c92113453ddd9d40d8f2efbe09 and published prerequisite
2fe1f8932f96be15b00df03ba2cde46f64a87758 remain ancestors; parent C72 is
695d24a4a58f8fb81026950302ac3f167124a898. Existing goal stays BLOCKED unchanged.

`fixed_uint_increment_certificate` proves the whole EXISTING indexed read,
checked binary add-one and indexed write code against actual intrinsic preInc or
postInc, keeping FULL Objects.ResultRepr, not a weaker legacy postrepresentation.
`resolved_uint_fixed_increment_word` derives actual independent Source
location->OLDread->incDecVal->write execution. Source prefix returns NEW, postfix
returns OLD; the matching intrinsic/word STATEMENT discards expression value and
performs the same write. This is not an emitted-expression return-value theorem.
Actual operation order is preserved; no side-effectful operand reorder claim.

INITIAL premises are genuine fixed SourceUintFixedAt, aligned Source/typed root
and index locals, runtime valid index, inRange(actual INITIAL cell+1), Source
MemOK and full Objects.StateRepr. The actual old value comes from the represented
heap, never a desired reached-value premise. Existing source_uint_add supplies
arithmetic; the actual existing fixed write derives reached observer/locals,
MemOK, every other typed object/Source address and ex/events/logs/fnLocals frame,
stack and Objects.KeepsAllocator. Any actual initial AllocatorRepr/positive base
therefore transports; no fresh allocation or global injection is invented.
Source expression/statement sufficient horizons are n+3/n+4, not minimum-fuel or
admission bounds. Generic runtime length/index are unrestricted beyond existing
intrinsic validity. Unchecked Source agrees only for the stated IN-RANGE case.

`resolved_uint_fixed_increment_overflow_word` requires checked=true and initial
actualcell+1 out of range. It derives exact Source arithmetic panic before write,
Source statement globals retained, intrinsic revert and whole symbolic word
revert. No target posterror machine, panic bytes, transaction rollback or unchecked
wrapping correspondence is claimed. Decrement, general increment-expression
compiler correctness and all-profile bounds/failure composition remain open.

Both-pipeline controls independently inhabit LEFT=[7,8,7], RIGHT=[9,10,9],
neighbor=[11,12] and all Source/typed/Objects/MemOK/allocator premises. Actual
prefix returns8 and postfix returns7 while both write LEFT index0 to8. Full old/
new typed vectors, Source tables, complete Source locals, alias identities,
world frames, cursor40, savedstack77/88 and strong ownership are proved.
The MAX rejection control consumes C72's ACTUAL constructor->rebind->firstwrite
prefix fresh0->MAX, including its concrete constructor/alias/write Evm.run
witnesses, strong prefix StateRepr/AllocatorRepr, Source observer and old frames.
New increment rejects at this genuinely reached MAX rather than frozen initial0;
old objects/aliases/neighbor and Source world remain represented. No post-revert
target is returned. The C72 failure's already-proved successful prefix is used,
not an assumed successful suffix or a fabricated heap.

Complete20word initial/first/second increment vectors execute the actual word
statement code: LEFT7->8->9, all prior16cells plus local7/fresh40/41/42, aliases,
RIGHT/neighbor, freepointer and savedstack retained. These double-increment word
vectors are not falsely called a new two-statement Source Items theorem. Prior
C71/C72 source/typed/word vectors and every exact guard remain byte-unchanged.
The NEW script retains every C71/C72 admission case and appends C73 cases; applied
missing-guard/unsafe-axiom/renamed-target mutations test evidence admission only.
Kernel execution theorems, symbolic word observations and external compiler/EVM
validation remain distinct. No external solc/EVM run or physical-byte claim.

Initial proof attempts exposed actual constructor naming, Source lifted-result,
canonical literal-one and opaque fixed-index reductions. A word-control reduction
hit the unchanged200000heartbeat limit; splitting through existing run_append_ok
resolved it. No budget was raised and no old source refactored. Every failure log
is retained; successful repairs do not relabel them. Final gates/reviews are in
additive checkpoint73 evidence; raw docs/global inventory failures remain failed
versus separate complete public-byte parity/scoped-pin validation.

ALL original G32/G33/G34/G35.01/.03/.04/.05 and Backfills A/B remain PARTIAL;
G35.02/.06 remain BLOCKED reserved-copy/final composition. Physical bytes,
all-profile construction/target allocation failures, general paths/reference
loops/graphs, ABI/storage/deep-copy/recursive liveness, reserved memory-to-storage
and final Source/V10/target composition remain unfinished. Fixed decrement and
further eligible operation compositions are not declared exhausted or unavailable.
This component does not complete the original lane or reactivate the goal.

C73 independent skeptic found reached_max_overflow dropped its actual Source
prefix executions from the conclusion; fixed ADDITIVELY with first SourceevalE7
returningMAX,z and SourceItems11 retainingz.2, alongside existing actual target
run chain and all frames. Final source finder/skeptic PASS after this repair.
Final focused01 PASS246jobs and final full02 PASS1146default/262Suite,
SolKey377parsed/131covered/OK/exit0. Earlier full01 PASS before Source-prefix
conclusion fix remains earlier-tree evidence only. Actual Lean4.24.0 commit797c613,
Lake5.0.0-src+797c613 and KeySort2jobs PASS/cacheOFF/thread1 observed. Final full
sampled aggregateRSS1592704KiB/diskgrowth274432bytes/newOOM0.
All12C73exec receipts retain6failedproof gates; unchangedheartbeat
stop in controls02 is a real failed gate, not newOOM or a pass. Historical5OOM
kills/cumulative12GiBsessionpeak remain separate. Structural/trust/lane/complete
fixtures/strict PASS;205script/corruptiontests PASS. Sixnew exactstandard guards
give1148owned pins/165modules, all1142C72rows unchanged. Raw inventoryFAIL1/
1507unregistered=359published+1148owned/0unsafe; additive proposals are not a
global pass. Raw docsFAIL1/83rows, exact consumed-public bytes match separately;
frozen72rows+11incoming remainsFAIL1. Warmstrict0newtimedSuite; independently
all262current/C31source-fixture-toolchainhashes+runtime versions match retained
cold26/max160s<300 only, not new timing coverage. Artifactreviews follow commit.


## C74: fixed decrement, reached zero underflow and real Source Items pair (partial)

Continued ORIGINAL G34/Backfill A-B, not a replacement assignment. New owned
[SourceUintFixedDecrement](../../Solidity/Backend/MemoryOps/SourceUintFixedDecrement.lean),
[SourceUintFixedBumpSequence](../../Solidity/Backend/MemoryOps/SourceUintFixedBumpSequence.lean),
and [SourceUintFixedDecrementControls](../../Solidity/Backend/MemoryOps/SourceUintFixedDecrementControls.lean)
consume published Source.incDecVal(false), actual evalLoc/read/write and existing
Evm.Memory.incrementMemory_eq_compound for preDec/postDec, ValFrag binary/sub and
PtrFrag.write read-only. No replacement allocator/interpreter/AST/value/heap or
reserved Source/Evm/Bridge producer edit. Frozen fb379ae20f10e2c92113453ddd9d40d8f2efbe09,
consumed public 2fe1f8932f96be15b00df03ba2cde46f64a87758 and C73 parent
e8a84af20f8e927ef9cd2c02bdb0299c3276252b remain the recorded ancestry. Goal stays
BLOCKED unchanged; no goal RPC/status/reset/activation action was taken.

`source_uint_sub_one` and `source_uint_sub_one_underflow` prove actual arithmetic
and conversion from existing Source.intRes and intrinsic compoundT definitions.
There was no published owned fixed subtraction-by-one application to invoke.
The in-range case derives the exact Source uint bound from inRange(x-1), then
proves actual Source.incDecVal checked false and compoundT .sub results. The
out-of-range case requires checked Source=true and proves exact arithmetic panic
and intrinsic none. Neither is an assumed successful execution/output oracle or
an alternate arithmetic semantics. Unchecked wrapping underflow is not identified
with the checked target. These are local arithmetic cases, never source exclusions.

`fixed_uint_decrement_certificate` composes actual existing read/sub-one/write
code with full Objects.ResultRepr. `resolved_uint_fixed_decrement_word` derives
actual Source location->OLDread->incDecVal(false)->write and prefix NEW/postfix
OLD expression results, the discarded-result statement, intrinsic preDec/postDec
and whole word execution. INITIAL genuine SourceUintFixedAt (some N/fixed N),
root/index local alignment, actual runtime bound, inRange(INITIAL actualcell-1),
Source.MemOK and full Objects.StateRepr are premises. Actual reads/writes derive
reached correspondence, all unchanged locals/other typed objects/Source addresses,
Source ex/events/logs/fnLocals, stack and Objects.KeepsAllocator. Existing initial
AllocatorRepr and positive base transport through that derived certificate.
Sufficient expression/statement horizons n+3/n+4 are not minimal-fuel/admission
claims; runtime lengths/indices have no extra payload/depth cutoff. Genuine fixed
types are retained. A target statement's discarded result does not prove an
emitted expression-result compiler theorem or physical-byte encoding.

`resolved_uint_fixed_decrement_underflow_word` reads the actual represented cell,
requires checked=true and actualcell-1 out of range, then proves Source arithmetic
panic before write, retained Source globals, intrinsic revert and whole target
revert. No target machine/panic bytes/transaction rollback are fabricated after
reversion. Zero remains supported by this failure case, never excluded from a
profile; no zero-length Source admission is added.

`resolved_uint_fixed_bump_pair_word` closes C73's explicitly missing two-statement
application with ONE existing Source RItems increment then REACHED decrement,
matching intrinsic Prog and complete published word append. INITIAL actualcell+1
in range is the only arithmetic case premise. The first actual set and unchanged
fixed length derive the second OLD, index bound and subtraction range. Thus
Source OLD/NEW results follow reached contents for either pre/post choice.
Original caller nps stays explicit at sufficient Items horizon fuel+6; expression
horizons are fuel+4/fuel+3. Entire typed heap equality to INITIAL heap is derived
from both actual writes, List.set_getElem_self and existing dependent heap
extensionality; it is not a premise. Every Source object lookup is restored from
initial correspondence/other-address framing, and Source locals/world fields,
stack and allocator are derived. No claim of total Source machine equality or
external transaction rollback follows. Arbitrary Source graphs and final compiler
composition remain separate unfinished obligations.

Both-pipeline controls independently inhabit old LEFT=[7,8,7], RIGHT=[9,10,9],
neighbor=[11,12] with real Source table, MemOK, Objects heap/locals and allocator.
Standalone decrement makes LEFT7->6; prefix returns6 and postfix7, unchanged old
aliases/neighbor/world/cursor40/stack77,88 and complete Source/typed tables follow.
Reached underflow executes the ACTUAL existing positive length3 declaration,
OLD-local rebind, write42 and delete0 Source Items/typed Prog/full word append.
Its final Source z is explicitly linked to the successful SourceItems11 and target
machine to constructor/alias/write/delete runs. The intermediate write Source
state is separately linked to actual SourceevalE7 from the derived rebound state;
its full locals/world fields and old/new table are derived from the existing
write producer. Actual new-root Source index read is0 while retained OLD-alias
index read is7; checked decrement rejects only at the selected fresh zero root.
Full old/intermediate/final object vectors, savedstack, allocator43 and Source
world/locals are observed without assuming reached correspondence.

`reached_pair` directly applies the generic Source Items/Prog/word theorem in
both pipelines and all pre/post choices: LEFT7->8->7, decrement postfix observes8
rather than stale7, all old objects/aliases/neighbor and Source object reads
restore. Complete20word initial/decrement/decrement vectors give7->6->5; actual
increment then decrement word vectors give7->8->7 with all prior16cells plus
local7/fresh40..42, stack/freepointer/frames retained. Wrong-operation and wrong
pre/post values6/8/7 discriminate accidental increment or stale result. Unlike
C73's word-only double vector, the increment/decrement pair now has actual Source
Items and intrinsic Prog certificates; emitted expression-result correctness is
still not claimed. Every previous C71/C72/C73 fixture/vector/guard/test is preserved.
The NEW lane test retains every earlier admission case and appends all C74 heads;
mutation tests validate evidence admission, not replace kernel execution proofs.

Preflight verified all4473 prior seals, same idle runtime/image/mount/cache/toolchain,
aggregate12GiB/no-swap under16GiB parent and OS headroom; initialfree663412736bytes
cleared unchanged reserve536870912+forecast100663296. The entire warm source,
compiled output/log/commit/compact export route was admitted, no cold cache copy,
cleanup/new runtime/guard or budget change. All failing attempts are retained;
no subsequent pass relabels a failure. Per-file MCP was unavailable; actual serial
focused closures substitute within repository permissions, explicit Lean-j1/thread1,
CPU0/cacheOFF. Final full/strict/structural/fixtures/pins/resources/reviews are
recorded additively in checkpoint74 evidence. Raw global docs/inventory failures
remain failures, separate from exact public-byte parity and scoped pin proposals.

All ORIGINAL G32/G33/G34/G35.01/.03/.04/.05 and Backfills A/B remain PARTIAL;
G35.02/.06 remain BLOCKED on reserved-copy/final Source-V10-target prerequisites.
Physical bytes/all-profile constructors and target allocation failures/general
paths/graphs/ABI/storage/deep-copy/recursive liveness/reserved memory-to-storage
and final composition remain real open obligations. Further late decrement
failure/bounds/composition work is not declared exhausted or unavailable. Kernel
and symbolic-word results do not establish external pinned solc/EVM execution or
whole-lane correctness. Existing goal identity/objective/status remain unchanged.

C74 final source finder/skeptic PASS; only a decrement-comment typo was suggested
and corrected. Actual script admission exposed a missing exact prefix_postfix
axiom guard: initial257tests254PASS/3FAIL, static batch exit1 retained. The proof
already existed; the standard-trio guard was added without changing the theorem,
expected observations or test cases. Initial raw inventory1516(before guard) and
full01 PASS1149/262 before guard remain earlier-tree evidence only, not finalgate.
Final focused02 PASS247jobs; final full02 PASS1149default/262Suite, SolKey
377parsed/131covered/OK/exit0. Actual Lean4.24.0 commit797c613/Lake5.0.0-src+797c613/
KeySort2jobs/cacheOFF/thread1 observed. Full sampled aggregateRSS
206708KiB/diskgrowth270336bytes/newOOM0. All13C74exec
receipts retain3failed proof gates; historical5OOM/cumulative12GiB
sessionpeak remain separate. No proof/time/memory/disk guard was increased.
Refined structural/trust/lane/completefixtures/strict PASS;257script/corruption
tests PASS. Tennew exactstandard guards give1158owned pins/168modules, all1148
C73rows unchanged. Raw global inventoryFAIL1/1517=359published+1158owned/0unsafe
remains failed pending coordinator reconciliation. Raw docsFAIL1/83rows is complete
byte-identical to consumed public; frozen72rows+11incoming comparison FAIL1,
separate public zero-new comparison PASS0. Warmstrict0newtimedSuite; all262current/
C31source-fixture-toolchainhashes+actualruntimeversions match retained cold26/
max160s<300 only, not new timing coverage. Artifact reviews follow actual commit.


## Checkpoint C79: checked schedule composition and H1 runtime recovery

H1 authorizes “Free disk + 4 GiB reserve”: the Lean cap remains 12 GiB with
zero swap, CPU0/LEAN_NUM_THREADS=1/-j1 and the original 600-second gate ceiling.
The cache-reclaim controls are not writable. One own exited regenerable
node-version probe was backed up and removed, reclaiming 170651648 bytes; the
running session and every previous commit/latest seal remain intact. No source
profile, target predicate, observation, premise or proof budget changed.

`DisjointSnapshotSchedules` proves arbitrary actual reached-schedule commutation
for distinct logical objects, rejection transport, complete initial-read
provenance, and existing typed-path transport. Its separation premise is a local
theorem case, not a source exclusion or descendant/address injectivity premise.
`DisjointSnapshotScheduleControls` supplies primitive and shared-child reference
witnesses with ordered initial/intermediate/final vectors, alias noncommutation,
late rejection, endpoint and element32 observations.
`DisjointSnapshotPathApplications` adds actual fixed(n+3) parents, explicitly
constructed reference/Boolean MPaths with changed selections, and literal
intrinsic fixed0/dynamic-empty endpoint success and out-of-bounds path failure.
The fixed0 witness does not admit zero-length Source fixed arrays. Its length33
instance observes interior index1; it is not an additional element32/byte claim.

The actual combined 78-job focused closure passes all 18 exact standard-only
axiom guards. Fixes reduce proof beta/tuple projections, make closed bounds and
logical IDs explicit, remove unused simplifications, and annotate all 27 new
`have` types. The original RAM theorem statements and ordered observations are
frozen by `tests/v11-disjoint-schedules-statements.json`; the scoped checker and
corruption tests protect those original signatures without replacing Lean.

The five already-published C75/C76 modules are consumed byte-for-byte from
`c6c33c90ad710ede662ef8d343532ec8de242881`; all 85 existing owned dependencies
match that public commit exactly. Their actual local 251-job closure passes,
including first 1→0 then reached underflow and retained-prefix timeout/bounds.
No published repair or reserved Source/Evm/Bridge implementation was duplicated.

Kernel/intrinsic and symbolic-word certificates remain separate from external
compiler/EVM testing. Global documentation and inventory debt are still raw
failures until their real gates say otherwise; additive owned proposals and
public/base no-new comparisons do not turn them green.

All original queues remain open: G32/G33/G34/G35.01/.03/.04/.05 and Backfill A/B
are partial; G35.02 and G35.06 retain reserved-copy/final-composition dependencies.
Physical bytes, all-profile construction/allocation failures, general paths and
recursive graphs, ABI/storage/deep-copy/liveness and full Source/V10/target
composition are not established by this checkpoint.

C79 independent source finder/skeptic review confirmed statement/vector parity
and resource/ownership boundaries. Both found the same structural-checker gap:
total pin count alone admitted a duplicate target hiding a missing headline.
The checker now requires the exact target multiset, printed theorem name and
observed per-headline standard axiom set; three added mutation cases exercise
those defects. This changes no Lean claim and no reserved global inventory.

C79 measured final source results: full wrapper 1157 default jobs, 262
TestSuite jobs, SolKey 377 parsed/131 read-bearing; focused authored closure
78 jobs and byte-exact published late/bounds closure 251 jobs pass. The owned
checker finds 1188 standard pins across 176 modules. Complete fixtures pass;
270 corruption tests include the 13 new disjoint tests. Strict automation
finds zero newly timed TestSuite modules; retained source/toolchain-keyed C31
cold evidence (26 modules, max160s under300s) is not new timing coverage.

Raw global inventory remains FAIL1: 1547 unrecorded changes and zero unsafe
axiom errors. Raw strict docs remains FAIL1 with 83 findings. Its complete
checker output is byte-identical to C74; exact consumed-public c6c33c90 has
86 findings, so public comparison has zero new findings and three fewer,
but complete byte equality is FALSE. Frozen baseline has72 and11incoming
findings remain FAIL1. No unrelated docs, vendor decisions or global pins
were edited. All raw logs and complete lists are retained separately.

The minimal Lean container lacked Git; task-private host Git/loader libraries
repair only those static checks, without replacing container or Lean system
libraries. All failed missing-tool/ABI probes are retained. A runner completion
race returned null for one baseline-docs exit; the actual exit was recovered
as1, never a pass. The preserved v2 runner requires finished output plus an
integer completed exit, with an explicit exit1 negative control. Historical
OOM counters remain five; current checks show zero new OOM events.

Further independent original work is not exhausted: exact same-object
two-schedule commutation can be characterized from composed captureOrigin
reads, beyond C79's sufficient distinct-object case. No such next proof is
claimed complete here. Every original parent and final composition stays open.
