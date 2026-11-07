# Compound addition after actual Source slice binding

`Solidity/Backend/MemoryOps/SourceUintSliceCompound.lean` composes existing
slice, binding, arithmetic, write/frame and Items producers. Initial byte
payload selection determines the old cell; it is not a supplied decoded value
or a reached-observer premise. Bounds make getD select the actual element;
its fallback is never taken in these in-bounds laws.

`SourceUintMemoryAt.compound_add_observed` derives MemOK, element updates and
heap/world/local frames from the actual compound write.
`source_uint_slice_bind_add` derives the fresh observer, index and RHS
alignment from the binding output, then proves the two-statement Source Items
execution and native allocation/write with old-object frames.
`source_uint_slice_bind_add_overflow` requires checked=true and proves the
actual arithmetic panic before any write, plus the intrinsic checked arithmetic
failure. The successful binding prefix remains in Source globals; Items erases
returned locals on error. There is no rollback or target suffix-state claim.

Initial view/scalar alignment, ordered and bounded window, window capacity,
valid index and MemOK remain explicit. Success requires in-range addition;
unchecked wrapping outside that premise is not equated to checked intrinsic
arithmetic. Sufficient horizons are binding expression fuel+4, compound
expression fuel+3, Items fuel+6, with original nps. These are not minimal-fuel
or source-admission claims; arbitrary runtime lengths/windows remain quantified.

The additive controls in
`Solidity/Backend/MemoryOps/SourceCalldataSliceControls.lean` cover both pipelines
and preserve earlier bodies/vectors. Actual fresh [2,0,max] becomes [5,0,max]
while old [7,0,max] and neighbor [8,9] remain unchanged. The actual fresh
[0,max] binding then checked max+3 panics and retains the prefix. A separately
executed stale-alias compound succeeds at 0+3, changes only the old object to
[7,3,max], and preserves fresh [0,max] and neighbor. Complete ordered native
and Source object tables, local/world frames, byte offsets and operand reads
make the identity distinction visible. Whole program horizon5 times out before
binding and retains input globals; no successful prefix is invented there.

These are kernel Source and intrinsic Heap results. Existing emitted arithmetic
producers are read-only dependencies, but this composition supplies no emitted
fresh-payload allocator, ABI binding, whole word append, byte-memory or external
compiler/EVM correspondence. General graphs/copy/all-profile failures and final
independent Source/V10/target/world obligations remain open.
