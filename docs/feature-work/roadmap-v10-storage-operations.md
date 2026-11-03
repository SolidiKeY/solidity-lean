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

## Remaining obligations

General Source AST/address/default/value correspondence, complete packing/ABI
and recursive physical emission, aggregate target lifecycle and compiler/world
rollback composition remain open. G27.01–G27.05, G28, G29.01–G29.03, G30 and
Backfill A/B therefore remain partial. Published owner results are reused with
explicit premises; no missing representation or target bridge is assumed closed.
