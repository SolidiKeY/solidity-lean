# Dynamic compound bounds after actual slice binding

`Solidity/Backend/MemoryOps/SourceUintSliceCompoundBounds.lean` closes the
Source dynamic-array compound bounds application. It retains Source type
array memory uint256 none, and reuses the existing intrinsic ArrTy. The fixed
Source type some N is not cast or substituted.

`SourceUintMemoryAt.compound_add_bounds` executes the actual pure-local RHS,
then the lvalue bounds failure, before old-cell reading, arithmetic or writing.
It needs initial root/index/RHS alignment and the observer's actual length;
there is no arithmetic guard or supplied error run.
`source_uint_slice_bind_add_bounds` derives those premises from the real
slice allocation and local binding, and proves ONE Source Items execution.
The Source index panic retains reached globals while Items erases returned
locals on error. Independently exposed prefix facts include the bound local,
MemOK and fresh representation. Native read returns None and every attempted
native write value returns None. This does not invent a suffix heap or infer
transaction rollback or a word-level panic payload.

Initial calldata view/scalars, window ordering/bounds/capacity and MemOK remain
explicit; arbitrary runtime lengths/indices are quantified without an admission
cap. The original nps is retained. Sufficient horizons are binding expression
fuel+4, compound expression fuel+3, Items fuel+6. `source_uint_add_low` proves
only timeout for expression fuel at most2, not minimal successful fuel.

Additive both-pipeline controls in
`Solidity/Backend/MemoryOps/SourceCalldataSliceControls.lean` preserve all earlier
bodies/vectors. An omitted-end [0,max] slice has length2, binds actual root2,
and then index2 fails. Skipping binding leaves an old length3 root: actual
max+1 instead fails arithmetically, and a retained alias read at2 succeeds.
The distinct panic payloads, complete native/Source tables, full reached local
context, identities, Source allocation counter and world frames discriminate
the two executions. A literal empty dynamic slice is allocated and bound;
index0 rejects without any zero-length fixed-array Source admission. A low
expression horizon retains the independently reached prefix; whole Items
horizon5 instead times out before allocation and retains input globals.

These are kernel Source/intrinsic Heap results. Emitted fresh-payload
allocation, ABI binding, physical bytes, external compiler/EVM execution,
general graphs/copies/all-profile failures and final Source/V10/target/world
correspondence remain open. No reserved producer is modified.
