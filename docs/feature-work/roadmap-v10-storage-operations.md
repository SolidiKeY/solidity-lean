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
