# Source uint slice binding and reached deletion

The owned adapter in `Solidity/Backend/MemoryOps/SourceUintSliceBinding.lean`
binds the result of the existing slice/copy expression to a memory local, then
executes primitive deletion through that reached root in one Source Items
program. The byte payload is computed by the published RawUint decoder. The
initial view, operand alignment, window ordering/bounds/capacity and MemOK are
explicit. No intermediate observer, decoded payload or successful run is an
input premise.

`source_uint_slice_bind_native` derives actual expression/statement execution,
paired intrinsic allocation, the fresh observer, MemOK, local binding, typed
local separation, old heap extension and occupied Source cell preservation.
`source_uint_slice_bind_delete` derives the suffix index/bounds from those
outputs and proves actual Items execution, native write, final observer/MemOK,
old-object framing, unchanged other locals and world fields.
`source_uint_slice_bind_delete_bounds` retains the successful allocation and
binding prefix when the fresh window rejects the index. Source Items exposes
reached globals and erases returned locals on error; no transaction rollback or
post-revert target machine is inferred.

Horizons are sufficient, not claimed minimal: binding expression fuel+4 and
statement fuel+5; delete expression fuel+3; paired Items fuel+6. The original
nps and both declared pipelines remain quantified. Runtime lists/windows are
arbitrary under the existing capacity premise, without an admission cap.

The additive controls in
`Solidity/Backend/MemoryOps/SourceCalldataSliceControls.lean` retain every earlier
vector. A populated old array and neighbor survive while the actual newly
bound [0,max] slice becomes [0,0]. Complete Source object/native content tables,
locals and world frames distinguish the retained old alias from the rebound
root. An omitted-end window has exact-end index2 rejection and retains [0,max]
and the actual fresh allocation. Literal low-horizon timeout retains the input.
These are kernel Source/intrinsic results; no emitted allocator, word append,
physical-byte equivalence, ABI binder or external compiler/EVM execution is
claimed. General graph/copy/all-profile and final Source/V10/target obligations
remain open. This component does not complete an original parent queue.
