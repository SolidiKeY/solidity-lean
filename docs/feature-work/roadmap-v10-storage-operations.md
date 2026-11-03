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

## Remaining obligations

General Source AST/address/default/value correspondence, complete packing/ABI
and recursive physical emission, aggregate target lifecycle and compiler/world
rollback composition remain open. G27.01–G27.05, G28, G29.01–G29.03, G30 and
Backfill A/B therefore remain partial. Published owner results are reused with
explicit premises; no missing representation or target bridge is assumed closed.
