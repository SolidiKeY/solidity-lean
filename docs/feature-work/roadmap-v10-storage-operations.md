# V10 storage operations — G27–G30

The lane remains partial. `Backend/StorageOps/` is Source-free;
`Lowering/StorageOps/` contains clients of the independent Source semantics.
Kernel operation laws, structured target execution, numeric transport and
external compiler/EVM evidence are separate boundaries.

## Graph and representation components

`Value.overlay` is the independent copy specification. `Traversal.copyArray`
provides outer runtime-prefix transport with semantic nested leaves;
`RecursiveCopy` and `RecursiveClear` independently traverse demanded nested
values. Their correspondence laws identify these views, without an admitted
depth cap. Lazy function-valued fields do not prove eager emitted traversal.

Path/common-prefix laws, disjoint updates, snapshot copies, mapping barriers,
stale-tail clearing and aggregate lifecycle components reuse the existing
intrinsic graph and published `Represented` relation. Numeric transport retains
`FiniteRun` per-run hash/region coverage, `KeysFit`, initial store observations
and separation premises; no global hash injectivity is inferred.

Structured target loops include runtime headers, repetition and nested/fixed
copies. `OutputRootComplete.complete` requires read/write/clear coverage over
intermediate stores. `LoopLaws` shares turn/exit adapters; it does not prove
arbitrary-loop termination. Controls retain overlap, collision, header
interference, malformed operands and complete context observations.

## Source clients and address limits

Source delete/copy, repetition and disjoint-copy clients preserve exact runtime
footprints, captured snapshots, older shadows and ordered outcomes. Registered
modules replace historical script wrappers; those scripts are not dependencies
of the new interfaces. Rollback laws invoke the existing rollback explicitly.

`SourceWordRead.complete` and `SourceWordWrite.complete` pair independent Source
and SLOAD/SSTORE runs sharing word observations. Source paths and target slots
are independent parameters. `SourceArrayWrite.complete_numeric` similarly shares
length, index and payload with graph/target operations, but has no relation
identifying its Source path with its target base. These facts do not establish
Source address/layout compilation or compiler preservation.

`StackWordWrite.code` consumes the value already on the stack;
`TargetOperations.writeCode` adds the constant value push to that shared suffix.
Their existing instruction behavior and proof premises are unchanged.

Fresh indexing laws derive canonical-header checks and panic0x32 from raw Source
cells. Bounds-first write failures precede payload/type/static/fuel checks.
Retained raw reads remain distinct from fresh liveness. Unwritten uint cells
are raw-absent while published reads default to zero. Finite numeric and
nonempty live/retained owner-query clients discharge their stated premises;
written-read inequality is not a separate failed representation judgment.

`SourceWordCommutation` proves full Source-world equality for distinct captured
typed cell writes, actual ordinary/writable execution and exact journal order.
Mixed uint/bool controls retain nonempty locals, transient storage and a journal
prefix: worlds agree while journals/states differ; overlap changes worlds.
Explicit undo restores the seeded execution state. The routine combined adapter
is pending in [TERRA-TODO](../../TERRA-TODO.md), without a compiled stub.

`SourceWriteRollback` proves typed static refusal and actual `rollbackTo`
restoration for a captured account-write-only poststate. Populated controls
execute the original mark, retain a successful write through a later refusal,
show that a failed bind skips its rollback continuation, and invoke rollback
separately. A wrong mark loses older journal/log prefixes; a wrong payload type
fails before static refusal. Heap/events/locals survive because these writes
never changed them. This does not prove general frame or compiler rollback.
The routine generic pair adapter remains uncompiled in TERRA-TODO.

`SourceStorageCopyPrefix.prepared` proves the actual distinct-path Source
`storeVal(storRef)` result for primitive integer arrays at original fuel
`count+padding+4`. Snapshot and payload phases finish; cleanup reuses its phase
fuel. Success commits the header last; timeout retains exactly the corresponding
prefix of the existing copy journal and the old header. Runtime counts and
padding are arbitrary naturals, with the original OLD-read/type premises.
Uniform and populated controls distinguish shorter payload failure, snapshot
failure, partial cleanup, the sharper success threshold, empty/varying lengths,
self-copy and refusal. Complete outcomes, contexts and journal snapshots retain
both raw absent cells and defaulted zero reads. Generic smaller-fuel cases,
Source AST/address compilation and target realization remain open; this is not
G35 memory-to-storage work.

`SourceStorageCopyBarrier` proves the complementary primitive snapshot barrier:
`loadElems` fuel≤count, array capture fuel≤count+1 and distinct-path
`storeVal(storRef)` fuel≤count+2 return timeout with the entire initial state.
Valid source-header/element reads are explicit; no destination-header/type or
writable premise is needed before capture completes. Populated controls preserve
complete ordered raw/default reads, contexts and journals, and distinguish the
first payload write, malformed-source failure, malformed destination, same-path
success and empty-array fuel boundary. Finder and skeptic reviewed the actual
constructor thresholds and complete controls without running Lean. These laws
are intrinsic Source execution, not an implicit rollback or compiler bridge.

`SourceStorageCopyPayload.copy_prefix` closes the nonempty primitive payload
boundary: at original fuel sourceLength+3, actual capture finishes and exactly
sourceLength−1 elements are written before the final leaf times out. The exact
poststate contains that journal prefix; cleanup and header commit are skipped.
The source-header/read and destination-header/type premises remain explicit.
Populated two/three-element and empty/short-destination clients retain complete
ordered outcomes, raw/default views, contexts and journals. Actual fresh indexing
can reject a newly written retained cell under the unchanged old header, while
an existing location still reads it. Static/type/self-copy and next-fuel controls
distinguish false extensions. The proof reuses published capture/leaf operations;
it does not implement memory-to-storage lowering or infer automatic rollback.

Header readback retains the published proof unchanged. The task runtime now
follows repository-default elaboration, preserving explicit single-thread and
resource limits; both readback and the original EVM heartbeat checks pass in
that mode. Diagnostics from the incompatible task-local override are retained.

`SourceStorageCopyEmpty.copy_empty` proves the remaining primitive fuel3
boundary: an empty destination commits a zero header, while a nonempty old live
tail times out before its first clear. Ten complete controls distinguish static,
type, missing-source and same-path ordering, the next-fuel first clear, actual
fresh/retained reads and raw-absent header materialization. Empty success grows
the journal even when ordinary header reads stay zero; it is not a no-op.
The generic all-fuel composition statement is well-typed but unproved in
TERRA-TODO; with it, fifteen routine adapters remain pending.

## Source byte capture and writes

`Lowering/StorageOps/SourceByteStorageCopy` proves OLD-state runtime byte
capture and exact write progress at every original fuel using the existing
Source fixed-byte cells and operation journal. Success requires fuel strictly
greater than the payload length; equal fuel writes all bytes and then times
out on the empty tail. This timeout preserves those writes and is not rollback.
The typed-cell and OLD-read hypotheses remain explicit.

The companion controls instantiate both general producers and retain complete
ordered outcomes, raw byte cells, journal snapshots and unchanged account/frame
context. They distinguish partial writes, final-write timeout, successful writes,
empty fuel boundaries, nonzero-start capture, static refusal and malformed paths.
Independent read-only finder/skeptic reviews found no producer soundness issue;
full storage-reference byte/string capture-to-cleanup/header composition and
packed physical layout remain open at that helper boundary. These are Source operation helpers, not a
memory-to-storage or whole compiler certificate.

## Source byte cleanup and prepared phases

`SourceByteStorageClear.range_eq_int` transports actual primitive byte-clear
operations to the checked scalar runtime range, including zero-fuel failure;
it does not equate byte and integer values. `SourceByteStoragePrepared` composes
byte payload writes, exactly the demanded clear prefix and header-last commit.
At phase fuel `length+padding+2`, cleanup gets budget `length+padding`; failure
retains its generated writes and old header. No implicit rollback follows.

The populated controls execute actual storage-reference byte copies and retain
all ordered outcomes, raw observations, success/timeout journal order and
nonempty local/account context. Shrink, growth, empty, self and static cases
separate raw cleared absence from default-byte reads and fresh bounds checks;
older shadows and unvisited tails remain observable. Independent read-only
finder/skeptic reviews found no producer issue; their requested timeout-journal
and default/live alias controls are included. String-copy coverage is not claimed.
The generic capture-to-prepared adapter is type-validated but unproved in
TERRA-TODO; sixteen routine adapters now remain pending. Packed representation,
Source address compilation and emitted/world composition remain open.

## Byte capture failure barrier

`SourceByteStorageBarrier.load_timeout` proves exact full-state preservation at
arbitrary insufficient capture fuel and nonzero starts, under valid OLD byte
reads. No writable frame or destination hypothesis is needed. Malformed source
reads can instead fail earlier; the read premise cannot be dropped.

Populated controls pin all ten actual storage-reference failure/self cases and
four byte-capture outcomes. Missing-destination and static checks follow valid
capture; zero-fuel timeout precedes the self-copy shortcut. Complete ordered
state/context/journal rows and shifted/static witnesses retain earlier shadows.
The two routine memory/copy wrappers are type-checked statements only in
TERRA-TODO; eighteen adapters remain pending. This is a capture barrier, not
implicit rollback or a Source-to-target compiler theorem.

## Nested allocating capture

`SourceNestedByteCapture.empty_capture` executes the existing Source allocation
of an empty reference object. `timeout_prefix` proves arbitrary runtime prefixes:
capturing `count+1` empty byte-reference elements at original fuel `count+3`
times out after exactly `count` existing heap allocations. OLD child-header reads
are transported through heap-only changes using the published read-frame law.
The footprint uses existing Source states/heaps and `Nat.repeatTR`, not another
evaluator or an admitted-source depth cap.

Populated actual storage-reference array copies distinguish storage/journal
preservation from changed heap on timeout and static refusal. Ordered outcomes,
heap contents, source shadows, old objects, success journals and self-copy are
pinned. This is a concrete limit on generalizing primitive byte full-state
preservation; no automatic heap/world rollback follows. The routine outer-copy
wrapper is a type-checked proposition only in TERRA-TODO; nineteen adapters
remain pending. General nested shapes, physical allocation/failure and compiler
composition remain open.

## Nonempty nested capture payloads

`SourceNestedByteValues.capture` derives actual byte reads and typed allocation
for nonempty payloads. `timeout_prefix` tracks distinct per-child payloads in
runtime allocation order: at original fuel `count+length+3`, capture of
`count+1` references times out after exactly `count` allocations. Both parameters
are arbitrary naturals. Headers and byte reads are transported through heap-only
updates using the published read-frame laws; the footprint folds existing
Source heap operations over the runtime index range.

This component uses a common runtime inner length, not arbitrary differing
child lengths and not a source-profile cap. Populated copies distinguish partial
capture, later destination/static failure and self-copy; old objects, retained
source tails, complete headers/context/journals and distinct nonempty heap
payloads are pinned. A reversed allocation order is a checked negative control.
The routine outer wrapper is type-checked prose only in TERRA-TODO; twenty
adapters remain unproved. General variable-shape capture, physical emission and
compiler/world composition remain open.

## Independently varying child lengths

`SourceVaryingByteCapture.timeout_prefix` removes the common-inner-length
premise from the preceding capture family. Every child has its own runtime
length and payload. At original loop fuel `count+budget+3`, earlier children
must satisfy `length(start+j) < count+budget-j`; the final child satisfies
`budget ≤ length(start+count)`. These are actual matching-prefix fuel conditions,
not an admitted-source cap. The proof derives each successful capture's padding
and transports OLD header/byte reads across the resulting heap-only updates.

Seven populated Source copy outcomes preserve complete headers, raw tails,
heap contents, contexts and journals. Lengths 1/2/2 leave an older second byte
outside the first captured object. A checked earlier-fuel counterexample shows
why the success inequalities cannot be dropped. The routine outer wrapper is
type-checked prose only; twenty-one Terra adapters remain unproved. General
recursive shapes, eager target realization, physical allocation and compiler/
world composition remain open.

## Successful capture and returned identities

`SourceByteCaptureSuccess.capture_all` proves successful runtime traversal of
varying-length byte children under the original per-child fuel conditions and
OLD reads. It returns the exact typed reference function `oldHeap.next+j`,
independent of the storage start index, together with the ordered allocation
footprint. The empty case and the `finCons` identity step are included.

Full, shifted, static, empty, one-short and outer snapshot controls pin returned
identities, complete states/headers/heaps/contexts/journals and actual heap-byte
readbacks. An unallocated address is refused; an incorrect absolute-source-index
offset is a negative control. Old objects and retained source tails survive.
The routine outer snapshot wrapper is a type-checked proposition only in
TERRA-TODO; twenty-two adapters remain unproved. These are logical Source heap
identities, not physical pointer compilation, allocation-failure or world/
compiler closure.

## H26 downstream layout and execution interface

`Backend/StorageOps/ProducerInterface` packages three explicit certificates:
`PathEndpoint` ties the typed path location to the selected target operand;
`StateEndpoint` retains graph representation, finite-run regions, numeric
transport, query coverage and target observations; `ReachedEndpoint` certifies
actual selected-code execution to that same observed machine. Pending producer
laws are fields, with no unconditional producer instance.

The execution equation matches the already published
`Backend/MemoryCopies/Premises.LocationStepPremise` at public revision
`6f3eedf0788ee1f8a3bcf230558c712ecdca04d5`. Consumers can construct that premise
from `endpoint.execution`; the StorageOps interface avoids its Source imports.
The inhabited bool-word client supplies every field and changes storage from
zero to one while preserving stack, memory and context. Independent finder and
skeptic reviews inspect this interface and witness without running Lean.

This endpoint uses intrinsic `Evm.Machine`/`Evm.run`, not physical bytecode or
packed byte-store execution. General concrete producers, Source authority and
P17 physical adequacy remain open. The interface-first checkpoint was sealed before the separate readback
modules described below were restored.

## Capture allocation readbacks

`SourceCaptureReadback.allocation_observations` proves exact fresh addresses
and typed payloads for every arbitrary finite runtime capture prefix, with
independently varying child lengths. It also preserves every older heap object.
The proof uses the existing allocation operations and their typed readback laws;
no replacement heap or representation relation is introduced.

Full and shifted clients exercise actual Source capture and `heapAt`: existing
objects survive, fresh objects contain changed captured bytes, dangling and
wrong-type reads fail, and complete ordered states and journals are unchanged
by reads. This strengthens logical Source heap observations only; physical
allocation, target execution and world rollback remain open. The H26 endpoint
stays sealed separately; P17's physical bridge choice is coordinator-escalated.

## Captured nested-byte commit traversal

`SourceCapturedByteCommit.commit_all` proves the actual `Source.storeElems`
commit phase for arbitrary outer counts and independently varying byte-child
lengths. Captured typed heap readbacks, existing path types, writable context,
original fuel inequalities and destination headers at the reached prefix states
are explicit premises. The ordered footprint contains only existing `Source.Op`
values; it is not another evaluator. OLD header observations alone are not
claimed sufficient for the intermediate reads.

A populated whole storage-reference copy composes the checked capture and
commit laws, then commits its outer header. Complete ordered outcomes and
journals distinguish shifted references, empty traversal, dangling capture and
partial writes on timeout. Fresh indexing refuses a retained child before the
outer header commits, then accepts it afterward. A dirty child clears two
stale bytes while retaining an older shadow byte; a wrong-reference control
changes the selected payload. All prior fixtures remain unchanged.

The initially combined concrete reduction exceeded the original heartbeat
limit. Reusing capture/commit laws and keeping named outcome checks fixes that
without changing budgets or observations. These are logical Source operations,
not memory-to-storage compiler closure, general recursive physical emission or
world rollback. The physical P17 bridge remains coordinator-escalated.

## OLD-header transport through commit prefixes

`SourceByteCommitFrames` proves persistent and transient read frames through
byte writes, partial/full cleanup, header commit and arbitrary runtime prefixes.
`prefix_header` derives the next sibling's actual read outcome from the OLD
state using structural Source path separation. This supplies the intermediate
header condition of the captured-byte commit theorem for the checked client;
it does not assume the desired prefix execution or a physical address relation.

The client exercises populated varying-length captures using only OLD header
reads. Complete prefix state/journal observations retain unvisited defaults,
source shadows and captured objects. An unrelated malformed query keeps its
failure; an already visited header changes from zero to two, showing why the
outside-path condition matters. Ordinary Source liveness checks, numeric hash
transport, physical execution and world composition remain separate obligations.
The routine generic OLD-header wrapper remains a type-checked statement for Terra.

## Cleanup timeout after a runtime child prefix

`SourceCapturedBytePhase.run_phase` derives captured-child execution from the
existing heap and byte-copy semantics. `SourceCapturedByteTimeout.cleanup_timeout`
proves an arbitrary successful child prefix followed by partial last-child
cleanup. Captured-object, type and original per-child fuel conditions remain
explicit. OLD destination headers suffice through the checked path frames.
The exact failure state includes earlier commits and only the available stale
tail prefix; neither the failing child header nor the outer header is committed.

A populated whole storage-reference copy writes varying-length children before
its last cleanup times out. Three of four stale bytes are cleared, an uncleared
stale byte and an older shadow survive, and complete ordered journals are pinned.
A successful phase control distinguishes the cleanup boundary. A separately
invoked `rollbackTo` restores journaled state while captured heap objects remain;
a rollback continuation after the failed bind is skipped. The original mark's
heap component is not a heap-restoration guarantee. No Source semantics changed.
The routine generic rollback wrapper is type-only for Terra; twenty-four
adapters remain unproved. Physical target/caller rollback remains open.

## Payload timeout after a runtime child prefix

`SourceCapturedByteWriteTimeout.payload_timeout` proves the actual captured
child writes exactly the available payload prefix before timeout, including
zero write fuel. `write_timeout` lifts this through an arbitrary successful
child prefix with OLD headers transported through the checked frames. Earlier
payload/cleanup conditions and the final shortage condition remain explicit.
The exact trace contains no cleanup or header for the failing child.

A whole storage-reference copy captures varying-length children, commits the
first two, writes both bytes of the third and then times out at its empty-tail
fuel boundary. Its last child header stays zero despite populated raw cells;
a successful phase control commits that header. Complete ordered states and
journals distinguish failure, success, skipped rollback and separately invoked
rollback retaining captured heap objects. The original heartbeat limit is
preserved by reusing the checked commit theorem for the success contrast.
These Source fuel observations do not establish EVM gas behavior, physical
execution or whole-caller rollback. The prior twenty-four Terra adapters remain
unproved; no generic pending adapter is used as a producer.

## Remaining obligations

General Source AST/address/default/value correspondence, complete packing/ABI
and recursive physical emission, aggregate target lifecycle and compiler/world
rollback composition remain open. G27.01–G27.05, G28, G29.01–G29.03, G30 and
Backfill A/B therefore remain partial. Published owner results are reused with
explicit premises; no missing representation or target bridge is assumed closed.

## Snapshot fixture extraction boundary

A shared initial-store fixture was evaluated without changing control statements
or observations. Both implementation variants passed affected kernel checks, but
the sequence fixture runtime increased by 22.7%, then by 10.5% after a
reducibility optimization, exceeding the 10% limit in both trials. The original fixture definitions remain
in production. Candidate patches and raw measurements are retained separately;
this result is not migration or performance acceptance.

## C224 adopted-head checkpoint (2026-11-07)

The preserved branch had adopted master through 8319ae6ccb2df62ac6b4e8aad460f4d87853cd9f.
Owned StorageOps sources, Source/Ctor, the toolchain and Lake configuration were
unchanged from C223. Fresh KeySort passes by artifact fetch; the initially empty
build directory does not establish cold compilation or a performance baseline.

The checkpoint selected 350 touched targets. That build timed out with exit 124
after 600.22 seconds (602 seconds wrapper wall time), peak sampled aggregate RSS
1112567808 bytes and no resource stop. It completed 487 jobs without a recorded
compiler error; those jobs are partial progress, not a completed build. Run-lean
ran its preliminary checks but its heavy build was refused by the retained
prerequisite guard. No identical retry, timeout increase or guard bypass was made.
The V10-C224-TIMEOUT policy question was sent immediately through coord-ask;
independent per-file proof work remains separate from full confirmation.

Trust, orphans and layers pass. Strict docs remain FAIL: 4 missing references and
131 ambiguous references. Running the same current checker on exact committed
trees gives identical current/published findings at master 2a43bf4fcdaf24750265afc8f8be5b420d1d22b0
(zero new/removed). The frozen original base under that same checker has 0 missing
and 12 ambiguous references; its comparison remains FAIL with 132 new and 9 removed
findings. Published equality is not a raw strict or frozen-baseline waiver and
reproduces no build-timeout baseline. Strict axiom pins also remain FAIL: 16312
pinned theorems, zero errors, 271 unrecorded changes. No inventory or gate policy
was edited. All raw failures and completion-validated comparison logs are retained.

Separate read-only finder and skeptic reviews found no receipt-boundary issue.
Original closure still needs concrete Source-origin/layout/alignment and reached
state construction for the published PathEndpoint/StateEndpoint/ReachedEndpoint
interfaces; generated intermediate copy/clear coverage remains an explicit
per-run premise. Generic recursive emitted selection, ordinary Source aggregate
lifecycle and physical/P8/caller-world composition remain producer obligations.
Existing intrinsic leaves and the 52-row audit reference ledger do not close
G27-G30, the backfills or any consolidated proof/acceptance queue.


### Checkpoints 225–226: interrupted diagnostic and rejected false-loop backfill

C225 tested source head `139f09acbb231b26237fafd55a937ef79f9cc8f5`.
The host monitor was lost across session restart while the capped runtime build
continued. The verified task-owned runtime was stopped under the existing
interruption policy. Build exit and complete resource measurements are unknown;
this is not a passing full gate. Cache seeding had failed extraction with ENOSPC
and installed no pack. Raw logs and interruption receipts remain off Git.

Before C226, the existing lane fast-forwarded to published master
`2a917f7329f06c3fa4b15ebea1608b4c2caa3826`. GitHub #71 authorized a shared
false-loop success lemma and proof-only rewrites in the two allocation controls,
conditional on checking being no slower. No existing statement or definition was
changed. The candidate affected build passed; the baseline warm-up passed 222
jobs. An initial timing prerequisite failed on an unmaterialized cache object;
the repository restore helper corrected it before a fresh fixed measurement set.

Three serial warm samples per file used identical H111 stack and H113 resource
settings. Median seconds before/after were SimLemmas 7.89/7.94, mixed allocation
2.42/2.43, and recursive allocation 3.02/3.01. The predefined per-file and summed
median rule rejected the change. Every sample is retained; no sample was selected
away. All three source files were restored byte-for-byte to the committed master
version. This is a rejected bounded backfill attempt, not a completed production
extraction or a general performance result. No unchanged retry is authorized.
The rejected candidate was not accepted into the axiom inventory.

Evidence: `/workspace/v10-storage-operations-evidence/checkpoint225-interruption.json`,
`checkpoint225-interruption-last20.log`, `checkpoint226-plan.json`,
`checkpoint226-timing.json`, `checkpoint226-restoration.json`, and
`checkpoint226-rejected.patch` in the same directory. Original producer, physical
adequacy, audit coverage, full validation and trust/documentation gate obligations
remain open. Independent reviews are recorded in the checkpoint handoff.


### Checkpoint 227: nonempty target write-sequence audit witnesses

The additive audit module supplies simultaneous inputs for four exact frozen
TargetDefaultInit laws: run_writes, context_writes, agreement_writes and
outside_writes. One populated machine and the ordered writes root0:=7,
root1:=23, root0:=0 expose overwrite order. Both covered roots agree with the
captured store initially; a distinct outside root and complete non-store context
frame. Actual execution and agreement reuse the frozen laws. Omitting the last
write changes root0, and an always-reverting program disagrees with the actual
successful sequence. No Source, schema compiler, physical hash, gas/fork or world
adequacy is asserted.

Exact source commit `f869a9173e50390a3f88f8444453b42fb73fb6ce` passed the bounded
serial kernel check in 1.84 seconds, peak aggregate RSS 682602496 bytes, without a
resource stop. All eleven measured local axiom guards use only propext,
Classical.choice and Quot.sound. The first check failed on a local reduction
before finite inequality checking; the corrected proof and subsequent exact-head
guards pass. The mapping generator's initial wrong census-field lookup also
failed and was corrected without changing the census or interfaces.

The frozen registry now contains 56 mapped rows: 44 joint-premise bundles and
12 data inhabitants; 3225 of 3281 conservative rows remain unmapped. Additional
execution/negative controls do not increase that interface count. Registry tests
include rejection of drift in this module and its source pin. Historical checked
heads and the prior complete-validation marker remain historical; only the new
module has a fresh exact-head receipt.

The corrected repository trust wrapper reports 6614 sources, 289 inventoried
sites and zero findings. Direct scanner invocation without its required file
list failed and is retained. Strict axiom pins remain FAIL: 16411 pinned,
zero errors, 251 unrecorded and 99 baselined changes. The eleven new declarations
are all standard-only entries; no shared axiom inventory was written. Independent
read-only finder and skeptic found no semantic fidelity issue; metadata review
and sealed evidence accompany this checkpoint. Full lane validation and all
previous producer, timing and documentation gate holds remain open.


### Checkpoint 228: live-array access and retained refusal audit

The additive ArrayAccessWitnesses module supplies six exact frozen premise
bundles: TargetArrayRead.run_current and failure_matches, plus
TargetArrayWrite.run_current, success, failure_matches and header_frame.
One existing intrinsic Bool array has length 1 and retained extent 3, with true
payloads; the populated symbolic-slot machine has the same current header.
The successful index-0 write stores false. Actual read/write execution reuses
the frozen laws, including the complete machine context and stack tail. The
selected header representation is supplied jointly with actual adapter success.

Retained index 1 has a raw present cell and permits raw save, while live access
and the write adapter refuse it. Index 3 is separately out of extent and also
reverts. The observations retain the header, untouched retained cell and outside
slot. Reject-all disagrees with the successful read. These controls establish
no Source lowering, numeric/physical hash, gas/fork or world adequacy.

Source commit `c4484a7dc292c1cf547a99e8f48bcfeb1763e8d7` passed its exact-head
serial check in 1.84 seconds, peak aggregate RSS 701554688 bytes, without a
resource stop. Sixteen measured axiom guards pass: seven axiom-free and nine
using only propext, Classical.choice and Quot.sound. Initial local extent
construction, dependent record syntax, and header compatibility proof failures
are retained; corrected definitions use the existing intrinsic types and
explicit length/extent bounds, without producer statement or budget changes.

The frozen registry now maps 62 rows: 50 joint-premise bundles and 12 data
inhabitants. 3219 of the 3281 conservative rows remain unmapped. Six new rows
are counted once; additional execution/refusal controls add no interface count.
New source/pin corruption checks pass. Prior complete and per-source validation
heads stay historical; only this additive module has a fresh receipt.

The repository trust wrapper passes 6614 sources and 289 inventoried sites with
zero findings. Strict pins remain FAIL: 16532 pinned, zero errors, 372 unrecorded
and 99 baselined changes. The sixteen new declarations are standard-only;
shared inventories and gate policies are unchanged. Independent read-only
finder and skeptic found no source fidelity defects; metadata reviews and
strict committed-tree documentation comparisons accompany the sealed handoff.
All original producer, full-validation, timing and documentation holds remain.


### Checkpoint 229: represented live-array numeric readback

The existing ArrayAccessWitnesses fixture now jointly inhabits the exact frozen
TargetArrayRead.represented_read and complete_read premises. Both use the same
populated length-1/extent-3 array, machine and live index 0. Selected queries are
nonempty: the current header and the live element. The index support bound,
header compatibility bounds, logical representation and target observations are
proved together. Numeric completion additionally supplies Transport over a
nonempty header/child location list and selected-child coverage. Its constant
true-word stores and explicit local hash satisfy that read-only interface; no
finite-region injectivity, physical hash adequacy or Source compiler is inferred.

Both successful conclusions apply the unchanged original laws. Negative controls
show an all-false numeric store violates Transport and a zeroed target child
violates initial target agreement. These are refused premise bundles, not new
compiler or execution-totality claims. Existing definitions, statements and
sixteen earlier guards remain unchanged.

Exact source commit `3695698ee4e9806353038c773409dc0182e781c6` passed all 24 local
guards in 2.42 seconds, peak aggregate RSS 710434816 bytes, without a resource
stop. Eight new guards use only propext, Classical.choice and Quot.sound.
The first check failed on a missing explicit support-bound proof and a local
word-type mismatch; its rejected diagnostics are retained separately. The
corrected and final guarded source passes without unfinished proof artifacts.

The frozen registry maps 64 rows: 52 joint-premise bundles and 12 data
inhabitants; 3217 of 3281 conservative rows remain unmapped. Only two new
interface statements are counted. Source pin metadata retains the earlier
ArrayAccessWitnesses identity and receipt in historical_checks; all unrelated
and complete-validation receipts remain historical. Registry drift controls pass.

Trust scanning passes 6614 sources and 289 inventoried sites with zero findings.
Strict axiom pins remain FAIL: 16540 pinned, zero errors, 380 unrecorded and
99 baselined changes. Only the eight new standard-only entries are classified
for this increment; no shared inventory is written. Independent read-only
finder/skeptic source and metadata reviews and strict committed-tree document
comparisons accompany the handoff. Earlier producer, performance, documentation
and full-validation holds remain open.


### Checkpoint 230: complete numeric write with a retained frame

After adopting published master, the existing ArrayAccessWitnesses module
supplies every exact frozen TargetArrayWrite.complete_numeric premise together.
The same populated array, successful index-0 false write and machine are used.
The selected frame is nonempty: raw retained index 1, distinct from written
index 0. Logical apartness and symbolic nonaliasing are proved. The explicit
FiniteRun uses N=16, L=2, R=1, local hash 8, preimage data0 and covered locations
root0, child0 and child1. Initial header/frame representation, Transport, key
fitting and every covered target cell agree on these same inputs.

The actual theorem destructs this joint bundle and applies the original law,
retaining successful whole-machine execution, postrepresentation, numeric
Transport and all covered target observations. Observations distinguish numeric
addresses 0/8/9 and target header/written/retained cells as 1/0/1, preserving the
outside slot and non-store context. A hash-zero negative control refutes the
finite-run premise via two covered colliding addresses and the existing
word_inj law. This is a finite-model premise refusal, not a physical hash
collision or global injectivity claim. Source/compiler/world adequacy stays open.

Corrected source commit `f2189455bb6c61b10022b6d81e5a49cb241c4461` passed all
39 guards in 3.02 seconds, peak aggregate RSS 717266944 bytes, with no resource
stop. Fifteen new proofs use two empty axiom sets, three propext-only sets and
ten standard-three sets. Initial local hash/boundedness reductions failed and
were corrected. Guard generation also matched a theorem-name prefix, nesting
an accidental duplicate guard; commit 833a5ed14779235e3ffaae6abc09c6ce4e7ddaea
and its exact-head check FAIL are retained. The corrected guard preserves all
measured expectations and the passing receipt names only the corrected source.

Only one new frozen statement is counted. The registry maps 65 rows: 53 joint
bundles and 12 data inhabitants, with 3216 of 3281 conservative rows uncovered.
Prior source identities remain in historical_checks; complete and unrelated
source receipts remain historical. Registry corruption controls pass.

Trust scanning passes 6616 sources and 289 inventoried sites with zero findings.
Strict pins remain FAIL: 16559 pinned, zero errors, 384 unrecorded and zero
baselined changes. The fifteen new entries are standard-only; no shared
inventory or gate policy was edited by this increment. Independent read-only
finder and skeptic reviews, exact committed-tree documentation comparisons and
all rejected diagnostics accompany the sealed handoff. Original producer,
performance, full-validation and documentation holds remain open.


### Checkpoint 231: complete default initialization over dirty retained cells

Three exact frozen laws now have simultaneous witnesses: TargetDefaultInit.complete,
CopyDefaults.represented and CopyDefaults.numeric_transport. The same populated
array fixture supplies a checked CopyPermit, nonempty supported header/child
queries, a concrete finite run, numeric Transport, demand/selected coverage and
all target agreements. Each law is applied directly to its corresponding bundle.
The complete initializer retains all five conclusions, including successful
selected SLOAD readback. Default logical element reads are None, while raw dirty
child words remain 1; only the header becomes zero. A genuinely successful header
read and noop/reject-all counterexamples prevent an empty success story. This is
not a Source allocation or physical/world/compiler adequacy result.

Exact source commit `e90ef087062dc975455b436c63b7b292329f7a2e` passed all 51 guards
in 3.64 seconds, peak aggregate RSS 723103744 bytes, without a resource stop.
Twelve new proofs use two propext-only and ten standard-three axiom sets. The
initial check passed with an unused existential-binder warning; that binder was
renamed without changing the proposition. Existing statements, definitions and
39 previous guards remain unchanged apart from the added local import. This is
new audit work, not a matched proof-refactor or whole-build timing comparison.

The registry maps 68 rows: 56 joint bundles and 12 data inhabitants; 3213 of
3281 conservative rows remain uncovered. Only three new interface statements
are counted. Historical source identities/receipts and the complete-validation
marker remain historical. Registry corruption controls pass.

Trust scanning passes 6616 sources and 289 inventoried sites with zero findings.
After adopting published inventory reconciliation, strict pins remain FAIL:
16571 pinned, zero errors, 62 unrecorded and zero baselined changes. All 62 are
new standard-only entries in the two guarded audit modules: nine axiom-free,
five propext-only and 48 standard-three. Per-entry source/head/log classification
is exported for coordinator integration; no shared inventory is written here.

Checkpoint 230's oversized sealed HANDOFF.md remains unchanged. A separate
1811-byte compact relay was locally verified against its original sealed manifest
and its own checksum list. A first relative-checksum invocation used the wrong
working directory and read no files; the corrected verification passes. New
handoffs use a bounded checkpoint history summary while retaining the full
original-base patch and bundle. Original scope and goal identity are unchanged.
Read-only finder/skeptic reviews and raw strict/frozen documentation comparisons
accompany the sealed packet. All broader producer and final-gate work remains.


### Checkpoint 232: H121 producer ownership and checked dependency intake

H121 transfers the staged VY5 Source-origin/lifecycle and P8 aggregate-lifecycle
items to this lane. They are local open work, not waits on the frozen Claude
lanes. Original goal identity, observations and remaining obligations are
unchanged. No frozen interface or new per-case source implementation is added.

Fresh master was adopted first, then the exact P8 head
809f6d7f8efd8067d76402f5207e0fb04ecd0bc7 was merged. Its PlanWitness, Merged and
MergedControls focused build passes 142 jobs in 44.21 seconds, peak aggregate
RSS 795566080 bytes, without a resource stop. This producer is an inhabited
MODEL reference over empty Source programs; Merged is a pair of frozen halves.
It is not actual Source.sessionAt or aggregate-lifecycle adequacy. Six frozen
P8/P8b interface files retain their exact bytes.

The VY5 composition and dirty-readback commits e8247d927 and a0cdc0bec are already
on master. CorrectnessPublic and DirtyReadbackControls pass a 124-job focused
build in 89.76 seconds, peak aggregate RSS 2235285504 bytes, no resource stop.
Composition retains its explicit producer inputs; dirty readback declares a
local cleanup boundary and supplies no Source semantics call. Presence and
focused checking do not finish the locally owned Source-origin producer.

The existing V07 head 8ab717749c4dcf4cd5932e7fea800af1ddca5a87 already has the
shared GraphAdmissionAssembly.declarationGraphProducerOfEmpty helper. Only
SourceRefusal and GraphAdmissionAssembly are missing from master. H112 forbids
a duplicate per-case proof, so question V10-H121-V07 asks whether to publish the
existing packet or extend H121 to integrate those two unchanged files here.
No live V07 source file is edited or integrated while that route is pending.

A minimal P8 consumer proposal reuses that helper. The exact fetched V07 files
and the proposal passed isolated kernel checks; the proposal's three measured
standard-three axiom guards also pass. This is a checked UNAPPLIED proposal,
not a live producer instance or master evidence. The first isolated attempt
failed before elaboration on prerequisite object lookup; the published imports
were built and a read-only object view prepared before successful checks. No
failed artifact is accepted. Exact input hashes and receipts accompany the
portable packet; compiled object views are not shipped as evidence of source.

After these checks, this lane re-baselined on published master
806a972a4f1eefc367f7fe21078e56469447ce13. Selected API bytes are unchanged, but
focused receipts retain their actual pre-rebaseline source head
79e400cb9cf07b5e6a23efa4adfcfd2a291a7134; this is no fresh whole-build claim.
The original V10 and consolidated queues, real Source adequacy, physical Y04 and
separate 4.35 validation remain open. Checkpoint 231's bounded handoff and the
compact checkpoint-230 relay remain separate sealed/historical receipts.


Checkpoint-232 static checks at the latest baseline: trust passes 6628 sources
and 289 inventoried sites with zero findings; registration reports 6612 reachable,
zero orphaned and zero disallowed modules. Strict pins remain FAIL: 16675 pinned,
zero errors, 85 unrecorded and zero baselined changes. The isolated consumer's
three axiom guards use only propext, Classical.choice and Quot.sound. No shared
inventory is written. Kernel/source-head receipts and portable relative artifact
references distinguish prior focused validation from the later baseline merge.
The V07 integration question remains pending; neither isolated compatibility nor
a locally checked model proposal authorizes live integration or Source adequacy.


## H121b actual-Source H24 intake

The memory-reference-structs ticket at
85b3741d0ac578696e147cf5d455e38c4f8671b6 requests the locally owned P8
admission/origin producer, not transfer of its G42.04 body/result obligation.
LibraryPremises.Inputs requires admission, origin and program/environment,
pipeline and fixed-parameter agreements for the same library-containing Source
program. A producer over empty environments cannot discharge libraryDeclared.
The checked PlanWitness and P8b.Merged model results remain separate evidence.

Source.Semantics.sessionAt is the existing actual evaluator. Its sourceLang uses
Nat horizons and explicitly leaves resource failures, the hash premise and
stipend rule uninstantiated. ResourceContractLaw1.nat_encodable_resource_impossible
refutes the full failure replacement/projection contract when the resource
retracts into Nat; it does not refute all non-Nat resources or all possible
LibraryPremises.Inputs. LibraryPremises currently describes all such inputs as
uninhabited: that blanket documentation claim is not justified by this theorem.
This intake records the correction without editing the consumer-owned module.

Source.FailureResources.Bound already supplies horizon plus full failure choices
and replacement laws. Reuse this resource interface rather than duplicating it;
its module explicitly does not make the evaluator consult those choices.
Remaining local work is an actual-Source operational reference with justified
failure resources, canonical frontend-derived origins, root/feature extraction
and declaration admission for the same program, followed by lifecycle
correspondence. Neither a caller-supplied execution equality nor an origin chosen
from the producer itself completes those duties. No new instance, Source edit,
frozen signature change or completed adequacy proof is claimed here.

The protected V07 packet remains a separate pending integration route, not a
reason to substitute its empty-environment model for actual library admission.
Y04 physical adequacy/reached-state delivery and the separate 4.35 trust/timing
disposition remain external waits. Existing proof/coverage and final-gate gaps
remain open. Fresh master 05d2c2587 was inspected and merged before this intake;
no kernel check is claimed for this documentation-only change.

Independent read-only finder and skeptic checked this intake against the frozen
P8 interface, ResourceContractLaw1, LibraryPremises and Source semantics; neither
found an inaccuracy or ran Lean. The initial documentation append and master
merge omitted the writer lock; subsequent edits and commit checks used it.
No concurrent writer was observed in status; unobserved activity is not ruled out.


## Checkpoint 234: generated default-update fitting witness

The existing populated array fixture supplies the sole logical base-fitting
premise of TargetDefaultInit.updates_fit; the original law proves simultaneous
fitting of every generated update. A nonempty-list control excludes an empty
generated replacement. No new per-case fixture or production theorem is added.
Four sequence laws already have witness rows, so additional trial applications
were removed and none is counted again. The initial trial passed with an unused
binder warning; its receipt remains historical, separate from the final source.

All 54 guards pass at source head 83ca445d1aed1e9099d398193543abe4643e2561:
3.04 seconds, peak aggregate RSS 723800064 bytes, no resource stop. Of three new
guards, the base premise is axiom-free and the application and nonempty control
use propext, Classical.choice and Quot.sound. Original guard expectations remain.
The complete module has 10 axiom-free, 5 propext-only and 39 standard-three guards.

The reference ledger adds exactly one frozen row: 69 mapped, comprising 57 joint
bundles and 12 data inhabitants, with 3212 of 3281 conservative rows uncovered.
Historical complete-validation and source receipts remain historical; only this
module was freshly checked. Finder and skeptic independently reviewed the
narrowed source without Lean or its server and found no remaining findings.
This is symbolic-slot coverage, not actual Source or physical adequacy. H121
producer implementation, original proofs/coverage and final gates remain open.

Checkpoint-234 static trust reports 6628 sources, 289 inventoried sites and
zero findings; registration reports 6612 reachable and no orphans or disallowed
modules. Strict pins remain FAIL: 16678 pins, zero errors, 88 unrecorded and zero
baselined changes. The three new entries match their measured guards; no shared
inventory is rewritten. The bounded prerequisite records Lean 4.24.0 commit
797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Lake 5.0.0-src+797c613 and a passing
KeySort build. Prior full-build, strict-doc and timing failures remain retained.


## Checkpoint 235: authorized unchanged H24 assembly packet

Coordinator approval resolves V10-H121-V07. Fresh published master
05d2c25872c4bb963a0ca7f605905e6e1e99eedc has neither SourceRefusal nor
GraphAdmissionAssembly. Only those two files are integrated from the verified
V07 branch commit 8ab717749c4dcf4cd5932e7fea800af1ddca5a87, not its unrelated
branch history. Their SHA256 values remain respectively
2b7ed2b93dd8064086673b198d12c426931b01c9ca2a080fd9bf8cfe0cd5c0a0 and
1abed888a138c2c58c21bed309a0a9369d48a1e7ea5e211f761b70ca42dc362c.
Generated module registration accompanies the exact packet; no master push or
claim of coordinator publication is made. Six frozen P8/P8b files and all Source
implementation files remain unchanged. H16 single-writer restrictions remain.

The serial affected build passes 138 jobs in 6.65 seconds, aggregate RSS peak
830517248 bytes, no resource stop. Existing unused-simp warnings belong to the
unchanged packet/imports; no warning suppression or budget change is introduced.
Finder and skeptic independently verified provenance and scope without Lean or
its server, finding no proof/provenance issue. Both identified inherited prose
requiring qualification: the blanket P8-vacuity sentence is not justified by
the Nat-only resource obstruction, and PlanWitness's absent-from-master note is
historical. Those sentences are retained to preserve authorized exact bytes;
this paragraph records their current disposition rather than endorsing them.

This is generic conditional H24 assembly plus current-Source refusal laws. Its
empty-environment application is a model result, not actual Source/session or
library lifecycle adequacy. The MRS request at
85b3741d0ac578696e147cf5d455e38c4f8671b6 requires admission and independently
justified origins for the same library-containing Source program/environment
and the same pipeline/fixed parameters. MRS retains G42.04 body/result
implementation. Actual P8 producer/origin and VY5 lifecycle work remain locally
owned unfinished duties; Y04 and separate 4.35 timing/trust remain external.

The exact committed packet head 117f003291195801d295a93dca9d31927cb60d04 also
passes fresh per-file checks: SourceRefusal 3.04 seconds / 835960832 peak aggregate
RSS, GraphAdmissionAssembly 4.88 seconds / 821784576 bytes. All 29 guards pass.
Trust reports 6630 sources and zero findings; registration/layers pass with
6614 reachable modules. Strict pins remain FAIL with 16707 pinned theorems,
zero errors, 117 unrecorded and zero baselined changes. Raw strict docs retain
3 missing / 137 ambiguous references; the same checker on exact published
05d2c25872c4bb963a0ca7f605905e6e1e99eedc has identical findings, zero new/removed.
The frozen comparison remains FAIL with 137 new and 9 removed findings.

## Checkpoint 236: exact-origin H24 necessary constraint

DeclarationGraphConstraints reuses the integrated refusal characterization.
accepted_mapping_free retains input, resolved result, frontend derivation and
artifact; program_mapping_free carries equality of the whole dependent Source
program, preserving environment, pipeline and fixed parameters. The third law
refutes only an accepted origin whose same environment has the supplied nameable
mapping-bearing struct. It is a conditional contradiction, not a simultaneous
positive witness, actual producer or claim that every library input is impossible.
No Nat-resource premise, new failure assumption or per-case copy is introduced.

The three measured guards use only propext, Classical.choice and Quot.sound.
An affected-import build passes 139 jobs. Fresh per-file validation at committed
source head a1d573b61303417756e44df307c35b6feeacbf4f passes in 1.85 seconds,
aggregate RSS peak 579579904 bytes, no resource stop. Finder and skeptic reviewed
the generic statements and proofs without Lean/server and found no findings.
The audit ledger remains 69 mapped / 3212 uncovered; these new P8 constraints
are not counted as new witnesses of frozen audit rows.

Question V10-H121-H24-REFUSAL was sent through coord-ask at
coord-q/codex/solidity-v07-v11-20261030/v10-storage-operations/20261107T055502Z.
It requests the controlled H16/H57 route for the environment-aware Source typing
repair, or exact consumer program/environment evidence for a supported local
case; it never authorizes narrowing the original profile. The earlier V07
packet integration question is resolved. Source/Typing remains untouched.
Actual Source resource/session realization, canonical origins, general graph
admission, Source/lifecycle correspondence and original proof/final gates remain
locally open. Separate Y04 and 4.35 producer waits are unchanged.


## Checkpoint 238: model H24 record after authenticated re-baseline

Fresh fetch verifies published d93f6839c613468610ea488356b174cd183e3772; the
model-only PlanGraphAdmission module is absent there. The previously withheld
proposal is now integrated through the existing shared empty-environment helper.
producer fixes all four PlanWitness models, base_exact preserves planProducer,
and inhabited supplies this model record only. No refusal proof or per-case
implementation is copied. Actual Source/session/library/lifecycle adequacy and
the locally owned producer obligations remain open; this is not their delivery.

The affected build fetches 142 cached jobs, so its 0.64-second success is not
presented as fresh elaboration. A distinct per-file check at committed source
3b4440440d9e668041b4b8d530788e683b962f96 passes all three standard-three guards:
1.86 seconds, aggregate RSS peak 772624384 bytes, no resource stop. Finder and
skeptic independently reviewed source/scope without Lean/server and found no
findings. The historical checkpoint-237 auth failure and withdrawn candidate
receipt remain unchanged; this is a distinct freshly verified adoption.

## Checkpoint 239: premise-free retained-array input domains

Two input inhabitants reuse the existing populated retained fixture for the
logical live-word/none equivalences and primitive write-failure equivalence.
Their three original conclusions are exercised directly, keeping raw retained
access distinct from live refusal. No new fixture or production statement is
introduced. These rows have data parameters only: they add three DATA entries,
not joint logical-premise bundles. Counts become 72 mapped = 57 joint + 15 data,
with 3209 of 3281 conservative rows uncovered. Complete audit/totality and all
original goals remain unfinished. Historical complete-validation markers stay
historical; the source-specific receipt is updated only after kernel success.

All 59 guards pass at source2212d6770a5ed8a4c712957564cccdec1767abe2 in 3.63s,
aggregate RSS peak724922368bytes, no resource stop. Two new guards are axiom-free,
three use only propext/Classical.choice/Quot.sound. The module totals12empty,
5propext-only and42standard-three guards. The first diagnostic failed on missing
explicit Boolean primitive annotation; its receipt is retained, no failing
artifact accepted, and no statement/premise/budget weakening used.

Same-condition focused pre-change check3.62s versus exact committed3.63s is
about0.28percent slower, below the10percent STOP threshold; guarded precommit
check was3.58s. This is no whole-build comparison or statistical speedup claim.
Finder and skeptic independently confirmed the data-only classification and
original-law fidelity without Lean/server; no findings remained.

Published DirtyReadback now provides actual selected-read capture/agreement
and bounded integer/Boolean cleanup roundtrips. Those APIs are reused as
boundaries, not duplicated or promoted to complete Source session adequacy.
Frontend.SpecOriginsV1 is editor/NatSpec provenance, not P8a.SourceOrigins for an
actual Source program. H16/H57 question V10-H121-H24-REFUSAL stays pending for the
mapping-bearing accepted-origin case. No Source typing or frozen interface edit
is made; Y04 and separate4.35 trust/timing waits remain distinct.


## Checkpoint 240: concrete LibraryTry identity intake

The H71 ticket from memory-reference-structs at
7bd9a5d3d06f58ec429312281768bab6e255a484 identifies the existing legacy/via-IR
LibraryTry AST fixtures and retains G42.04 body/result work with that requester.
After fresh fetch, master3a5b9de41 is adopted in merge
5d6b0df2b9fe5b8c7888e72113cbcb22f971f531. No Source implementation or P8 frozen
interface changes arrive in that merge. The new read-only intake tool records
identities for Source construction without implementing a second parser or
pretending an intrinsic ContractWorld import is Source.SrcProg.

Observed input hashes are legacy
7ce034177434e147b9768a6eb10b7be384864cb060161fc0b2546be0a9377784 and via-IR
205b02e0fd5a46728191a1b4da3e841bb6652f204ae5cfbb087817a793bd06b1. Both canonical
JSON AST values are identical. Local raw Source bytes hash to
4376fed4d27beaf3ba4c3b10925d27046d5bb6ac82f2f0616cc3abe951b09384, matching both
recorded header digests. This establishes local byte availability, not an
independent compiler reproduction or actual P8 origin/realization proof. The
requester's separate provenance manifest is not locally delivered, so matching
its expected values is not claimed. Header validationStage remains analysis,
and neither AST is represented as a bytecode artifact.

All 26 declaration records and four functions retain AST IDs, owner/scope,
parameter/result type strings, storage locations and body hashes. Library L is
AST46, L.S is3, L.integer is23, L.stru is45, C is131 and C.t is53. The existing
using directive links46/3; C.g's call targets45 through receiver53. C.f/C.g retain
uint256 and string-memory results, and L.stru retains its struct-storage formal.
AST IDs are explicitly not Source declaration positions or runtime code indexes.
No code-account installation, dispatch body or delegated frame is manufactured.

Five tests pass, including mutations for storage/string identity loss, duplicate
IDs, pipeline/compiler drift and missing provenance. Reports stay off Git;
inputs are not rewritten. Finder and skeptic independently reviewed tools and
reports without Lean/server or edits and found no findings. The intake records
the concrete mapping-free AST shape but is not the formal Source.Env admission
proof; the general mapping-bearing H16/H57 question remains separate.

Next local obligations are actual Source syntax/environment and typed body
construction, canonical accepted-source/artifact binding, full failure-resource
realization and reached caller/library catalogue/frame installation. String
signatures, caller storage aliases, no second payment and all four existing
native observations must be preserved; those observations are requirements,
not a Source adequacy proof. No toy/model substitution, profile narrowing,
frozen weakening or Source single-writer violation is authorized by this intake.

At post-adoption source8e7f0883c83d15862f3e42e1f961ff788e65cc6d, fresh checks
pass the model's3guards in1.81s/639221760bytes aggregate RSS and the audit's
59guards in3.65s/726745088bytes, no resource stops. Actual Lean4.24.0/Lake versions
and KeySort prerequisite pass. The audit source-specific pin records this
new receipt; earlier receipts and complete markers remain historical.

Static trust passes6635sources/289sites/0findings; registration/layers pass
6618reachable/0orphans/0newforbiddenedges. Strict pins remain FAIL:16782pins,
0errors,192unrecorded,0baselined; shared inventories are not rewritten. Exact
raw strict docs at8e7f0883c83d15862f3e42e1f961ff788e65cc6d retain1missing/139ambiguous,
identical to published3a5b9de412b84a13777b6fbf8c8f310e10b3448e (0new/0removed).
Frozen comparison remains FAIL137new/9removed. No raw failure or historical
timing STOP is waived. Entire original/consolidated queues remain incomplete.


## Checkpoint 241: compiler leaf types into intrinsic Source syntax

Rebased the existing lane on published7265ee136d8eef49b969934d250a536edc97f1df
after verifying accepted bf7695fa485a ancestry. Existing untracked runtime files
and historical seals are preserved. Source.elaborate already constructs typed
programs with derivation evidence; the new P8 SourceAstTypes component prepares
its existing Syn type/parameter inputs instead of introducing another AST or
a hand-written resolved program. Source implementation files remain untouched.

The generic leaf converter preserves written qualified struct paths, explicit
storage/memory/calldata locations, anonymous names and string types. Integer
and fixed-byte widths are constructed only with the original intrinsic bounds;
noncanonical leading zeros are refused. Non-leaf conversion is unfinished: its
errors are component gaps, not Source/profile exclusions or parser admission.
No Env, complete syntax unit, resolution, program, origin, failure-resource
realization or reached-state witness is supplied by this leaf component.

Runtime checks reuse the unchanged LibraryTry legacy/via-IR fixtures: all12
parameters/results per fixture convert, including the actual S-storage formal
and anonymous string-memory return. These IO checks are not Source semantic
proofs. Four separate malformed-width/location propositions are kernel proved
and axiom-free. The three main definitions have exact measured guards: elementary
axiom-free; typeNameLeaf and parameter use propext only. No native_decide, new
axiom, statement weakening or heartbeat increase is introduced.

Initial diagnostics found the Lean4.24 String.drop API mismatch. Subsequent
concrete rfl/decide attempts encountered opaque string operations; failed
receipts, including rejected recovery sorryAx reports, remain retained. Width
reading now uses finite character lists, so all four original rejection
statements reduce in the kernel. No failing artifact or forbidden pin is
accepted. Independent finder and skeptic reviewed the final algorithm and
controls without Lean/server and found no findings.

Exact source814ba88f86307e36677cc6e8ae29ea1ce6ee4112 checks pass: definitions
1.90s/330522624bytes aggregate RSS; controls1.23s/320888832bytes, no resource stop.
Affected import build and generated registration/layers pass. Trust reports
6648sources/289sites/0findings. Strict pins remain FAIL:16795pins,0errors,
205unrecorded,0baselined; inventory is not rewritten. The audit ledger remains
72mapped/3209uncovered; these new conversion controls are not frozen-row
witness additions. All original Source/program/lifecycle, physical, coverage
and final-gate requirements and historical STOPs remain open.

### C242 — ordered Source parameter containers

SourceAstParameters converts compiler ParameterList children through the existing
leaf converter into intrinsic Source lists. A generalized-index proof-only
eliminator avoids fixed-index matching: its roundtrip is axiom-free; the exact
mapM order/error theorem and parameterList have measured propext-only guards.
The executable converter does not depend on the noncomputable proof eliminator.
Both unchanged LibraryTry AST fixtures pass input/result container checks and
retain all 12 leaf conversions each, storage formals and string-memory returns.
This supplies no declarations, Env/SrcProg, resolution, admission or lifecycle
adequacy. Recursive types and expression/statement/declaration conversion remain
local implementation work; the mapped audit ledger remains 72/3281.

Prior generated-cache cleanup left a dangling build target; the original target
was recreated and the repository artifact restorer placed four fetched objects.
Failed fixed-index, generic-match, recursive-unfold and executable-recursor
attempts are retained in checkpoint242 evidence. Only the final noncomputable
specification plus executable conversion passes; rejected recovery sorryAx and
compiler panic artifacts are not accepted. No statement, premise, axiom policy,
exclusion or budget was changed. H111 stack and H113 accounting remain unchanged.
Independent read-only finder and skeptic reviewed the final code without Lean
or its server and reported no findings. Registration, fragments, orphans and
layers pass; trust has 6649 sources, 289 sites and zero findings. Shared strict
pin drift and full lane/final-gate requirements remain open; no pin rewrite.

### C243 — existing-body expression syntax conversion

SourceAstExpressions reuses the indexed Source expression/list constructors and
Checked.Lexer hexBody/canonNat for compiler literal bytes and canonical integer
values. Member receivers, positional calls, assignment operands and tuple
components (including holes) retain their syntax and order. Unsupported forms
and finite traversal exhaustion produce conversion errors; these do not change
Source exclusions or resource semantics. No existing definition or statement
was edited. Three exact propext-only guards pin the reader and zero-depth law.

Runtime controls convert all 37 recognized expression nodes in each unchanged
LibraryTry AST. They check delegated receiver t.stru, t.x = 9, successful tuple
order and failure string bytes; malformed hex, separators, compound assignment,
named arguments and numeric units fail explicitly. An initial test precedence
error and rejected recovery diagnostic are retained; the corrected test passes.
These are runtime syntax checks, not resolution, Source execution, artifact
binding, H24 admission or lifecycle adequacy. No independent compiler rerun is
claimed. Both read-only finder and skeptic found no findings, without Lean or
its server. All original program, admission, resource, physical, audit coverage
and final-gate obligations remain open, as do prior STOPs and shared pin drift.

### C244 — recursive compound type syntax

SourceAstCompoundTypes preserves recursive array bounds, optional mapping names
and function-type signatures using existing Source constructors. Recursive
parameter conversion shares its structure through parameterWith; its exact
leaf instantiation equals the unchanged original parameter converter by rfl.
Arrays reuse SourceAstExpressions for fixed bounds; mappings reuse MapKey and
its existing non-payable key grammar restriction. Function parameter/result
lists retain names, locations, visibility and mutability. Conversion fuel is
not an execution resource, accepted-source premise or new Source exclusion.
All three measured guards use propext only; no axiom declaration or budget was
added. The initial optional-bound monadic typing failure and rejected recovery
diagnostic are retained; typed Option syntax mapping fixes the implementation.

Structural runtime controls pass for named mapping/fixed bounds and a nested
function parameter, with depth, payable-key and malformed-bound refusals.
These synthetic conversion controls are not compiler tests or Source acceptance
proofs. Existing LibraryTry leaves remain supported without modifying their
reader. Independent read-only finder and skeptic found no findings, without
Lean or its server. Actual Source unit/declarations/statements, resolution,
elaboration, artifact origin, H24 admission, lifecycle/resource and consumer
correspondence remain unfinished local work. General mapping-bearing H24,
physical Y04 and separate 4.35 trust/timing waits and every prior STOP remain.

### C245 — actual LibraryTry statement bodies

SourceAstStatements reuses the existing expression/type/list readers and body
context. Ordered block mapM retains every supported statement or fails; local
initializers, returns, conditional branches, try success returns and ordered
catch signatures/bodies remain intrinsic syntax. Four complete actual function
bodies in each existing pipeline fixture pass conversion. Runtime controls
check the x=8 prefix, dirty t.x=9 before t.stru, Error(string memory message)
handler returning (19,message), and counts of conditions, tries, handlers,
returns, assignments and calls. Unsupported/malformed/depth cases fail, while
an empty block succeeds. These are syntax checks, not Source elaboration,
execution, artifact origin, H24 admission or lifecycle correspondence.

The initial catch-constructor layout and an over-nested test pattern failed;
corrected layout and decomposed predicates pass. Failed diagnostics, including
rejected error-recovery artifacts, remain retained. The three measured guards
are propext-only; no existing statement/definition, budget, axiom policy or
exclusion was changed. Finder and skeptic reviewed final code read-only without
Lean/server and found no findings. Declarations, complete Source unit,
resolveUnit/elaborate and actual origin/admission/resource/lifecycle producers,
original/consolidated coverage and full final gates remain open. Mapping-bearing
H24, Y04 physical and separate4.35 waits and all historical STOPs remain.

### C246 — complete actual syntax/resolution, failed elaboration acceptance

SourceAstUnit retains L/C ownership, L.S, mutable C.t, using L for L.S,
function signatures and complete original bodies in a Source.Syn.unit. Existing
resolveUnit consumes that unit; both actual pipeline fixtures yield exactly the
eight expected declaration identities. Unsupported inheritance/modifiers/
overrides/declaration forms fail explicitly. Two measured guards are propext
only. No handwritten resolved program, empty model or rewritten caller body
is used. These results are syntax/resolution, not compiler rerun, source-byte
binding, typed SrcProg, actual origin/admission/session/lifecycle adequacy.

The manual full-unit elaboration probe FAILS for BOTH fixtures: L.integer and
L.stru elabBody succeed, but C.f and C.g fail and elaborate.isSome is false.
Source/Infer.lean:672-713 currently handles only contract-receiver try with a
plain catch or unnamed bytes-memory catch. It has no preserved library-call /
Error(string memory) case. Protected H16 Source remains unchanged. Question
V10-C246-SOURCE-TRY was sent via coord-ask, ref20261107T082812Z, requesting
H16-owned extension/approved producer or explicit hold, preserving all frozen
interfaces and H57 obligations. SourceAstUnitControls.lean is a manual diagnostic probe: no automated CI,
default, affected-module or final gate invokes it. Its recorded failure is from
explicit manual runs, not a failing automated gate or a passing expected-failure
test. The required whole-unit acceptance obligation remains open. The probe is
not replaced by the passing resolution-only check. Shared
fixtureInputs/inspect prevent case copies. Original first probe and all failure
logs remain retained. Missing cached objects for the shared test import were
materialized using the repository restorer; this was not a Source repair.

Finder and skeptic reviewed final code and the shared-fixture factoring
read-only without Lean/server and found no findings. Optional integration notes
were handled: the expression depth check now uses fuel1 rejection/fuel2 success
on an actual member; the leaf docstring points at the recursive reader. Source
syntax explicitly defines .tuple to include parenthesized expressions, so that
mapping is retained. Audit arithmetic is 3281 TOTAL =72 mapped+3209 uncovered;
no conversion check adds frozen-row coverage or resolves that remaining audit.

Local independent work remains: accepted-source/artifact linkage and conversion
correspondence, Source producer/resource/lifecycle obligations not requiring the
blocked try support, original/consolidated audit/extraction/generic/backfill
queues and full gates. Actual caller elaboration additionally awaits the exact
H16 producer question above. General mapping-bearing H24, Y04 physical,
separate4.35 trust/timing disposition and all historical STOPs remain separate.

### C247 — ordered container conversion correspondence

SourceAstCorrespondence adds a relational Each proposition over existing lists,
independent of mapM. Both directions of successful Except traversal are proved:
every child has its exact successful result in order; no child can be dropped,
swapped or skipped after failure. A generic typed-container builder law applies
to the unchanged block and Source-unit readers, exposing their exact node-kind
and child-array fields. These are container-level syntax laws relative to the
individual readers, not an independent proof that each child reader matches
the compiler, accepted-artifact binding, Source meaning, origin or admission.
The field hypotheses identify input syntax; they add no Source success filter.

The length law is axiom-free. The six traversal/container proofs use propext
and Quot.sound through the existing lawful-monad mapM equations. Generic kernel
controls cover positive ordered traversal and omission/swap/failure rejection;
three are axiom-free and the omitted-child control uses propext. All have exact
measured guards. No new per-case Source fixture, existing converter edit, axiom
declaration, budget, exclusion or frozen statement change was introduced.
Unused simp arguments found by the linter were removed without disabling it.

Independent read-only finder and skeptic found no findings and confirmed the
limited correspondence scope without using Lean/server/build. Required actual
Source whole-unit elaboration remains open; the manual C246 probe fails; this syntax
correspondence is not its substitute. H16 V10-C246-SOURCE-TRY support, general
mapping-bearing H24 disposition, Y04 physical and separate4.35 trust/timing
waits remain distinct. Local child-reader correspondence, accepted-artifact /
Source-byte binding, original and consolidated proof/backfill/coverage and all
full final gates remain open. No prior STOP or producer hold is released.


### C248 — published baseline and manual-probe coverage clarification

Adopted origin/master f5bfb9ba159d3ba2930d61dc07a2e0bbd5b07eb8 in the existing
branch. SourceAstUnitControls.lean is explicitly a MANUAL diagnostic probe,
excluded from automated gates. The recorded C246 failure therefore supplies
manual evidence of the actual caller elaboration gap, not automated gate
coverage. It raises when either whole-unit elaboration fails; this has not been
converted to a passing expected-failure test. Whole-unit acceptance remains
required and open. This checkpoint changes documentation/docstring only;
no Lean code, acceptance condition, Source implementation or producer hold
changed, and no Lean/build/timing result is claimed from it.

Read-only finder and skeptic reviewed this clarification and found no findings;
neither used Lean/server/build. Import and executable-suffix byte checks pass.

### C249 — receiver, operand and positional-call correspondence

SourceAstExpressionCorrespondence proves exact identifier spelling, member
receiver conversion, assignment left/right conversion and positional callee /
ordered-argument conversion for the unchanged expression reader. The call law
reuses C247 Each/build correspondence. Exact JSON field hypotheses identify
supported syntax, not Source admission or execution filters. These laws remain
relative to recursive child conversion; they do not establish compiler-ID/name
resolution coherence, independent compiler fidelity, artifact binding, Source
meaning/origin/H24 admission or lifecycle adequacy. Literal and tuple structural
correspondence and those semantic obligations remain open.

The successful-Except-bind helper is axiom-free. Identifier/member laws use
propext+Quot.sound; assignment/call laws use the existing standard trio including
Classical.choice. Exact measured guards pin all five; no new axiom declaration
or trust-policy expansion. Initial normalization/elaboration attempts failed;
outer-only unfolding, explicit successful-bind normalization, the equalities
already substituted by case analysis and an explicitly typed intrinsic call
builder resolve them. Failed/recovery diagnostics retained; no failing artifact
or sorryAx pin accepted. No statement, converter definition, Source file,
proof budget or exclusion was changed.

Existing SourceAstExpressionsControls reuses the same 37 actual expression
nodes per pipeline; only its import changes to cover the new proofs. All receiver,
dirty-write, tuple/bytes and refusal/nonzero-depth checks pass. No cloned case
fixtures were added. Finder and skeptic reviewed final code read-only without
Lean/server/build and found no findings. Manual C246 full-unit elaboration
probe remains a historical failed manual check outside automated gates, not
replaced by these proofs; H16 library try/Error(string) support is still pending.
General mapping-bearing H24, Y04 and separate4.35 waits and every STOP remain.
Original/consolidated proof/backfill/coverage and full final gates remain open.

### C250 — tuple components and decoded string bytes

SourceAstTupleCorrespondence proves the existing tuple child adapter agrees
with the shared optional-expression reader, null remains a hole, and successful
tuples contain a nonempty ordered Each correspondence for every component.
Empty-tuple rejection is proved as the existing explicit conversion gap, not a
Source exclusion. Ordinary string conversion retains exactly the bytes returned
by the existing decoder under exact field/digit/decoded-result hypotheses;
this is not source provenance or independent compiler fidelity.

Two adapter/hole guards use propext; three tuple/rejection/string laws use
propext+Quot.sound. All five have exact measured guards. No reader definition,
Source file, frozen statement/interface/premise/budget/exclusion or trust policy
changed. Initial proofs failed while the optional reader and selected tuple
branch were hidden; unfolding that existing reader and exposing the selected
branch before the extensional adapter rewrite fixes the proof. Failed diagnostics
and rejected recovery reports are retained, never accepted or pinned.

Existing expression controls retain all37actual expressions per pipeline and
add generic hole/empty/inline-array conversion boundaries with regression intent
in the docstring. No per-case Source fixture copies or new phase folders.
Finder and skeptic reviewed final code read-only without Lean/server/build and
found no findings. This is structural syntax progress only; actual Source
origin/H24/lifecycle and S03-PANIC41 producers remain undelivered local H121b
obligations. C246 remains a historical failed MANUAL elaboration probe outside
automated gates, not replaced by these proofs. H16 library try support, separate
mapping-bearing H24, Y04 physical,4.35 trust/timing waits and all STOPs remain.
Original/consolidated coverage, child/declaration/statement correspondence,
accepted-artifact binding and full final gates remain open.

### C251 — remaining supported literal values

Adopted published 7de6f66ad29488d70e3c31c6b2a4798b72a0a209, preserving
in-flight work. SourceAstLiteralCorrespondence proves supported
ordinary/Unicode/hex string constructor and byte preservation, canonical integer
value under all three existing no-unit field encodings, both Boolean values and
exact literal expression wrapping. All four measured guards use propext and
Quot.sound. Input field/decoder premises describe existing reader behavior;
they are not Source feasibility assumptions, independent compiler fidelity or
provenance evidence. No reader, Source file, existing statement/interface/premise/
budget/exclusion, axiom declaration, trust policy or resource limit was changed.

Existing expression controls keep all 37 actual expressions per pipeline and
all previous boundary checks. Generic controls add string-kind byte distinctions,
both Booleans, each no-unit spelling, malformed Boolean and noncanonical-number
refusals. No per-case Source fixture copies or new phase folders were added.
C251 initial and guarded focused checks passed. Lane history records read-only
finder and skeptic reviews for C251 with no findings; neither reviewer used
Lean, its server or build commands. This records that checkpoint's review,
not a new review or validation result for later heads.

The literal laws do not supply actual Source origin/H24/lifecycle/S03-PANIC41
or artifact binding; those H121b duties remain local and open. The C246
elaboration probe remains historical manual failure evidence outside automated
gates. At C251, protected inference/typing/elaboration/resolved files had no
published changes releasing its hold. H16 exact try support, separate
mapping-bearing H24, Y04 physical and 4.35 trust/timing waits, all prior STOPs,
inherited proofs/coverage and full final gates remain open.

### C252 — parameter and array structural correspondence

SourceAstParameterCorrespondence proves exact parameter converted type,
location and anonymous/named spelling; recursive parameter containers preserve
every child in order through C247 Each/build law. Array conversion retains its
converted base and exact optional bound through the existing optional-expression
reader, covering null/dynamic and explicit/fixed syntax. Input-field/child-result
premises describe conversion only, not Source feasibility or admission.

Two parameter guards use the standard trio; the array guard uses propext+
Quot.sound. All have exact measured guards. No reader/decoder, protected Source,
frozen statement/interface/premise/budget/exclusion/trust policy or axiom
declaration changed. Initial array proofs failed on match/bind distribution and
the null-bound case; explicit JSON constructor analysis and the null equality
fix the proof without changing its statement. Failed/recovery diagnostics are
retained; no rejected artifact or sorryAx pin accepted.

Existing compound controls keep named mapping/fixed bound, nested function and
refusal/depth checks; added generic anonymous/default and named storage/calldata
syntax controls guard qualifier/name preservation. Scalar storage/calldata test
syntax is NOT claimed to be an accepted Source program. No per-case Source
fixture copies or phase folders. Finder and skeptic reviewed read-only without
Lean/server/build, no findings. Actual Source origin/H24/lifecycle/S03-PANIC41,
artifact binding and remaining correspondence/coverage/full gates remain open.
The historical C246 manual failed probe remains outside automated gates; H16
exact try support, separate mapping-bearing H24, Y04 physical,4.35 trust/timing
waits and all STOPs remain unchanged. Original/consolidated goal not complete.

### C254 — mapping and function-type correspondence

SourceAstTypeCorrespondence proves optional-name absence/spelling, exact
converted mapping key/value and both names, and function argument/result lists,
visibility and mutability. C252 ordered-list correspondence applies to both
parameter readers. Exact field/child-output premises describe supported syntax,
not Source feasibility, admission, provenance or execution. The two name laws
are axiom-free; mapping/function laws use propext and Quot.sound. All four
measured guards pass. No reader/decoder, protected Source, frozen statement/
interface/premise/budget/exclusion, axiom declaration or trust policy changed.
An initial reserved binder spelling failed; renaming it fixes syntax without
changing the statement. Its failed receipt is retained, not accepted.

Existing compound controls retain all earlier cases. The empty-result function
fixture is factored through a generic builder without changing its data; added
checks retain a nonempty string-memory result and internal/nonpayable versus
external/payable qualifiers. These are syntax checks, not accepted Source
program witnesses. No Source case copies or phase folders were added. C254 lane
history records read-only finder/skeptic reviews with no findings; neither used
Lean, its server or build commands.

Actual Source origin/H24/lifecycle/S03-PANIC41 and artifact binding remain open
local H121b duties. The C246 manual failed probe is outside automated gates and
is not replaced by these structural laws. H16 exact library try support,
separate mapping-bearing H24, Y04 physical and 4.35 trust/timing waits and all
STOPs remain. Original/consolidated proof/backfill/coverage and full gates remain
unfinished; no semantic producer or whole-lane completion is delivered here.

### C255 — block, return and local statement correspondence

SourceAstStatementCorrespondence proves exact block output, expression statement,
optional return value and complete single-local type/location/name/initializer
preservation through unchanged readers. Field and child-result premises describe
syntax conversion, not Source validity, admission, provenance or execution.
Unsupported tuple declarations remain a converter gap, not a Source exclusion.
Three measured guards use propext and Quot.sound; the local law uses the standard
trio. All four guards pass. No existing reader, protected Source, frozen statement/
interface/premise/budget/exclusion, axiom declaration or trust policy changed.

Existing statement controls retain all four complete actual function bodies per
pipeline and original prefix/handler/census/refusal checks. Added generic bare
return and uninitialized-local boundaries ensure no value or initializer is
invented. They are syntax checks, not valid Source-program witnesses. No Source
case copies or new phase folders. C255 lane history records read-only finder and
skeptic reviews with no findings; neither used Lean, its server or build commands.
Initial and guarded focused checks passed without a failed proof attempt.

Actual Source origin/H24/lifecycle/S03-PANIC41 and artifact binding remain local
H121b obligations, undelivered here. The historical C246 manual failed probe is
outside automated gates and is not replaced by structural laws. H16 exact library
try support, separate mapping-bearing H24, Y04 physical,4.35 trust/timing waits
and all STOPs remain. Original/consolidated proofs, backfill, coverage and full
final gates remain unfinished; no whole-lane completion is claimed.

### C256 — conditional and catch correspondence

SourceAstBranchCorrespondence proves condition/branch preservation with absent
or present else, plain catch preservation, and complete named/unnamed catch
signature and body preservation. Exact fields and child-results expose syntax;
these laws do not supply Source typing, admission, artifact provenance or
execution. Both conditional guards use propext and Quot.sound; both catch guards
use the standard trio. All four measured guards pass. No reader, protected
Source, frozen statement/interface/premise/budget/exclusion, axiom declaration
or trust policy changed. An initial else proof failed before bind normalization;
normalizing successful binds fixes it without changing its statement. Failed
and rejected recovery diagnostics remain retained, never accepted or pinned.

Existing statement controls keep all four actual bodies per pipeline and prior
checks. Added generic absent-else, plain catch and unnamed bytes-memory catch
boundaries retain absence, signature and empty body syntax. They are not valid
Source-program witnesses. No Source case copies or phase folders. C256 lane
history records read-only finder/skeptic reviews with no findings; neither used
Lean, its server or build commands.

Actual Source origin/H24/lifecycle/S03-PANIC41 and artifact binding remain local
H121b duties, undelivered here. C246 remains historical manual failure evidence
outside automated gates, not replaced by these structural laws. H16 exact try
support, separate mapping-bearing H24, Y04 physical and 4.35 trust/timing waits
and every STOP remain. Original/consolidated proof/backfill/coverage and full
final gates remain open; no semantic producer or whole-lane completion claimed.

### C257 — try success and ordered handlers

SourceAstTryCorrespondence proves exact converted call, success returns/body,
mandatory first catch and every remaining catch in order through Each/build.
The success header is explicit. A second law proves the existing short-clause
conversion error after call conversion succeeds; no new Source exclusion or
execution-success premise is introduced. One measured guard uses the standard
trio, the other propext and Quot.sound. Both pass. No reader, protected Source,
frozen statement/interface/premise/budget/exclusion, axiom declaration or trust
policy changed. Initial proofs passed; an unused simp argument was removed
without disabling the linter.

Existing controls retain all four actual bodies per pipeline and prior checks.
Added generic success/named Error/plain handler ordering and success-only clause
refusal guard construction boundaries, not Source validity. No Source case
copies or phase folders. C257 lane history records read-only finder/skeptic
reviews with no findings; neither used Lean, its server or build commands.

Actual Source origin/H24/lifecycle/S03-PANIC41 and artifact binding remain local
H121b duties, undelivered here. The historical C246 manual failed probe is outside
automated gates, not replaced by these laws. H16 exact try support, separate
mapping-bearing H24, Y04 physical and 4.35 trust/timing waits and all STOPs remain.
Original/consolidated proof/backfill/coverage and full final gates remain open;
no semantic producer or whole-lane completion claimed.

### C259 — declaration correspondence and shared nonempty traversal

SourceAstDeclarationCorrespondence proves exact struct member types/names,
nonempty struct order through Each, and using-library path/type/global fields.
A generic nonempty traversal law now serves both structs and the existing tuple
proof, whose public statement and axiom guard are unchanged. Same-runtime checks
of the old and refactored tuple proofs both took 1.26 seconds; this is a focused
comparison, not whole-build timing evidence. No reader or protected Source body
changed. New guards retain only the measured standard axioms.

Regression controls preserve ordered Bool/uint members, empty-struct refusal,
typed/untyped using directives and both actual eight-declaration resolutions.
Existing expression controls still convert 37 expressions in each pipeline.
Initial control checks rejected reserved local identifiers; those attempts are
retained, and corrected checks pass. No error-recovery proof is accepted.

Actual Source admission/origin/lifecycle and S03-PANIC41 remain undelivered local
H121b duties. H125/H126 assigns the environment-aware typing repair and actual
library try/Error(string memory) support to vy1-words; consume the published
repair without changing frozen interfaces. C246's failed full-elaboration probe
remains historical manual evidence outside automated gates. The unchanged V07
packet is already integrated. No new issue is filed for these answered requests.
The RO-DRIFT-H19H60-TRANSPORT evidence request is retained: exact 19 signature
pairs and consumer proof references are not supplied by this syntax checkpoint.

Lane history records C259 read-only finder/skeptic reviews; neither uses Lean or
a build. Coverage remains 72 mapped of 3281 conservative rows, 3209 uncovered;
these conversion laws add no audit witness rows. Original/consolidated queues,
Y04 physical and separate 4.35 trust/timing waits, all prior STOPs and required
full final gates remain open. No Source adequacy or whole-lane completion claim.

### C261 — state and function declaration correspondence

The existing declaration correspondence module now proves state_exact and
function_exact. State syntax retains the declared type, visibility, transient
flag, name and optional initializer, with the existing mutable/default-location
checks and override refusal. Function syntax retains argument/result lists,
name, visibility, mutability, virtual flag and optional original body, with the
existing function-kind, modifier and override checks. Child conversion results
are exact premises; no resolved Source program is invented. Both new axiom
guards use propext, Classical.choice and Quot.sound. No reader, Source body,
existing statement, dependent definition body, interface or budget changed.

Existing resolution controls additionally guard initialized transient state,
constant-state refusal, named Bool parameters/string-memory results, function
qualifiers and absent versus nonempty retained bodies. These deliberately
syntax-only inputs establish no typing or execution success. Both actual
LibraryTry pipeline inputs retain the same eight declarations. The initial
proof attempt rejected a reserved binder; the unused simp argument was removed
and both corrected proofs pass. Failed diagnostic evidence remains off Git.
C261 lane history records independent read-only finder and skeptic reviews
with no findings; neither ran Lean, its server or builds.

Actual Source admission/origin/lifecycle, S03-PANIC41 and accepted artifact
binding remain local H121b duties. H125 vy1-words supplies the pending protected
Source library-try/Error(string memory) and H57 environment-aware typing repairs.
C246's manual full-elaboration failure remains outside automated gates until
that actual producer lands. No duplicate issue, Source case copy or phase folder
is added. The 19-signature transport evidence request is still outstanding.
Coverage stays 72 mapped of 3281 conservative rows, 3209 uncovered. Original and
consolidated work/backfill/proof queues, Y04 physical and separate 4.35 waits,
all STOPs and required final gates remain open. No semantic producer is claimed.

### C262 — ordered top-level declaration correspondence

A generic bind_ok_iff_each law retains every ordered child conversion and the
fallible container finish. The existing declaration module instantiates it in
top_ok_iff_each for library, contract and interface headers, including the
existing abstract-library refusal and unknown-kind error. pragma_exact retains
the complete literal-token list. All three guards use propext and Quot.sound.
No reader, existing statement, dependent definition body, protected Source,
frozen interface, budget, exclusion or axiom declaration changed. The initial
implicit-finish application failed elaboration; an explicit finish and
non-generalizing header match passed. The failed receipt remains off Git.

Existing controls now guard two ordered struct children through all three
container kinds, the contract abstract flag, abstract-library and unknown-kind
refusals, failed-child propagation, and pragma token retention. Both actual
LibraryTry pipeline inputs still resolve the same eight declarations. These
checks establish syntax conversion only; no compiler acceptance, typed program,
Source Env/SrcProg, origin, H24 admission or lifecycle adequacy follows.
C262 lane history records independent read-only finder/skeptic review; neither
runs Lean, its server or builds.

Next independent work includes remaining leaf/type conversion correspondence
and artifact-binding obligations within the supported domain. Actual H121b
Source-origin/lifecycle/P8 aggregate-lifecycle and S03-PANIC41 remain local duties.
H125 vy1-words owns pending protected library-try/Error(string memory) support
and the H57 environment-aware typing repair; retain the historical C246 manual
full-elaboration failure until that actual support lands. No duplicate issue or
Source case copy. The 19-signature H19/H60 transport evidence remains requested.
Original/consolidated proof, backfill, coverage and final gates remain open:
72 mapped of 3281 conservative rows, 3209 uncovered. Y04 physical and separate
4.35 trust/timing waits, all prior STOPs and strict inventory failures remain.

### C263 — qualified and elementary leaf correspondence

The existing type correspondence module now proves explicit pathNode priority,
namePath fallback only on lookup failure, non-address elementary conversion,
payable address conversion and both supported plain-address encodings. The
first three guards use propext/Quot.sound; address guards use the standard trio.
Existing readers, statements, definition bodies, interfaces, budgets, exclusions
and axiom declarations are unchanged. No compiler-ID resolution or semantic
meaning is inferred from spelling conversion.

Existing leaf controls guard a conflicting fallback spelling, malformed present
pathNode refusal, empty path-component refusal, string versus bytes, payable
versus plain address and malformed mutability refusal. All prior lexical kernel
controls remain. Both actual LibraryTry pipeline inputs still convert all 12
parameters/results, including storage formals and string-memory returns. No
Source case copy or new phase folder. C263 lane history records independent
read-only finder and skeptic reviews with no findings; neither ran Lean, its
server or builds. Initial proof and control checks pass without repair.

These laws are syntax correspondence only. Remaining lexical/path-validity and
compound-to-leaf correspondence, accepted-source/artifact binding and actual
Source Env/SrcProg/H24/origin/lifecycle/S03-PANIC41 remain open H121b work here.
H125/H128 vy1-words is the protected Source producer for library try/Error(string
memory) and additive v2 envLocOK typing, with v1 negative H24 refusals frozen.
No published repair was consumed here; historical C246 full-elaboration failure
remains manual evidence outside automated gates. The exact-19 H19/H60 transport
evidence request remains assigned and unfulfilled. All original/consolidated
proof/backfill/coverage/final gates, Y04 physical and separate 4.35 waits and
STOPs remain. Coverage is still 72 mapped / 3281 rows, 3209 uncovered; these
conversion laws add no witness rows or whole-lane completion credit.

### C264 — exact-19 source evidence and H16 hold

The coordinator disk helper removed the regenerable pinned .lake/build, leaving
over 2 GB free; sealed evidence and historical failures were preserved. The live
build symlink now needs its target restored before future Lean work. No Lean,
Source check, integration or timing retry was run in this checkpoint.

transport_pairs.py reuses the readonly-call consumer's lexical scanner and pins
the exact inventory bytes. It captures original C6/current source and signatures
for all 19 H19/H60 pairs (11 projections, one balance domain, seven typing
parameters), separately retaining the three missing private identities. Original
signature/context hashes must match; current drift is retained and fails the
observation gate. All 22 current observations match the recorded hashes. The
recorded 6f7002ca commit object is unavailable locally and is explicitly not
verified as retrieved. Current source is tied to its actual captured Git head.
This supplies source-version extracts only: zero transport proofs, zero H57
approvals verified, zero kernel-fidelity or original-obligation credit. No
assumed Fits/mapFree premise substitutes for actual range or typed-program
evidence. The exact-19 proof/authorization portion remains open.

Four Python controls cover original/context tampering, current drift or absence,
exact membership, duplicate identity, unsafe paths and non-promotion to proof.
They pass. C264 lane history records independent read-only finder/skeptic reviews
with no findings; neither used Lean, its server or builds. No production file,
reader, frozen statement, interface, budget, axiom set or exclusion changed.

The vy1-words ticket at 2efd664e52612f4ae39af083180a9a1990ce2ec9 is a DRAFT under
H16 TIMING HOLD, not a merge/retirement/acceptance. Do not integrate TypingV2 or
run Source checks/timing retries against that draft. Aggregate median +9.2046%
is a qualitative H16 hold despite being below the mechanical 10% threshold.
Library try/Error(string memory) remains separate, unimplemented and held.
V1 refusal statements stay frozen; future v2 consumer migration requires the
versioned contracts and actual reproofs. Historical C246 full-elaboration failure
remains. H121b actual Source admission/origin/lifecycle/P8/S03-PANIC41 duties stay
local; Y04 physical and separate 4.35 waits, all STOPs and original/consolidated
proof/backfill/coverage/final gates remain open. No new witness rows: 72 mapped
of 3281, 3209 uncovered.
