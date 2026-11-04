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

## Remaining obligations

General Source AST/address/default/value correspondence, complete packing/ABI
and recursive physical emission, aggregate target lifecycle and compiler/world
rollback composition remain open. G27.01–G27.05, G28, G29.01–G29.03, G30 and
Backfill A/B therefore remain partial. Published owner results are reused with
explicit premises; no missing representation or target bridge is assumed closed.
