# Local Bool reference deletion

`Solidity.Backend.MemoryOps.source_bool_local_delete_run` executes the existing independent Source delete expression: its default allocates a fresh empty Boolean array, then overwrites the local pointer. The old object is retained.

`source_bool_local_delete_rebind_word` composes that execution and the discarded-result statement with existing intrinsic `Stmt.rebindMem` and published `rebindNewCode`. Initial hypotheses are a represented old Bool array, aligned Source/native destination locals, Source MemOK, legacy word StateRepr, StructAllocatorRepr, positive local base and cursor+1<W. Its conclusions derive the fresh observer and identities, old-object/source-address preservation, MemOK, represented target, allocator and saved stack. It does not assume successful output or a reached representation.

This is an explicit operation adapter, not a theorem that the general compiler selects this code for Source delete. It does not equate local-reference deletion to intrinsic object-content deleteMem. Strong Objects/reference-graph representation, physical bytes, general reference defaults, ABI/storage/copy and Source/V10/compiler/EVM closure remain open.

Additive controls in `SourceReferenceReadControls` reuse the populated shared-child fixture under both pipelines: parent-held aliases retain the old nonempty array, the local selects a genuinely fresh empty object, all existing word cells plus the new header/next cell are recorded, and Source old/fresh reads and low horizons discriminate stale bindings. Prior fixture bodies remain unchanged. Exact standard axiom guards and bounded focused validation are recorded in the handoff; global historical gate failures are separate.
