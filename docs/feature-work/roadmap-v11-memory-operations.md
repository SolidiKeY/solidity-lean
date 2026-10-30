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
