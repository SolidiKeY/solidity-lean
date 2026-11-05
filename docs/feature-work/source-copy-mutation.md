# Source copy, binding and reached mutation

`Solidity/Backend/MemoryOps/SourceCalldataBinding.lean` derives actual
RHS-first local binding after the published Source calldata conversion.
`Solidity/Backend/MemoryOps/SourceCalldataMutation.lean` composes it with an
indexed Boolean assignment in one existing Source `RItems` program.

The initial premises are the finite named-struct/Boolean-child observer,
Source `MemOK`, actual calldata/index/RHS local alignment, an initial
valid index and the existing intrinsic array-length capacity. The decoder
result is computed from the actual frame; a final relation or successful
execution is not supplied. Typed local positions establish that binding the
array pointer cannot overwrite the scalar operands.

`SourceBoolMemoryAt.write_observed` consumes the existing Source and
intrinsic writers. `SourceBoolStructAt.bind_cd_bool_assign` derives the
reached bounds, both Source executions, the full statement sequence, the
intrinsic heap update, old-object `Heap.Keeps`, preservation of every old
occupied Source object, the named observer, `MemOK` and world/local frames.
The Source allocator's real freshness proves address separation; no global
address injectivity premise is introduced.

The populated controls change the newly copied `TFT` object to `TTT` while
retaining the old `TFF` alias, `FTF` neighbor and parent fields. They preserve
the prior ordered fixtures and distinguish a dropped write or stale alias.
Decoder rejection short-circuits before allocation; a separate empty-copy
control executes its allocation/binding prefix before indexed assignment
panics, retaining the reached Source heap. This is not transaction rollback.

These results establish Source execution and paired intrinsic **heap**
operations. They do not supply an intrinsic-local/`Prog` or emitted fresh-copy
program, target allocator/`StateRepr` after copying, ABI-entry correctness,
recursive graph coverage or external compiler/EVM execution.

The published ABI overlapping-view packing and extension schemas remain
separate G34 structural producer obligations. MemoryCopies V2 fitting-input
certificates do not by themselves provide the Source-to-target copy bridge.
