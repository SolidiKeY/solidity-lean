# Physical one-byte stores and live revert observations

`Backend/MemoryOps/PhysicalByteStore.lean` consumes the existing
`Environment.dataStep` and `Failure.Slice.step` MSTORE8 cases read-only.
`mstore8_slices` derives both actual executions, including offset/value order,
UInt8.ofNat truncation and caller tails. `mstore8_revert_live` executes MSTORE8
then REVERT from the reached byte memory; the arbitrary suffix is unexecuted
because of that actual halt. The returned component slice machine is explicit.

`WordFrame.writeByte_outside` and `WordFrame.mstore8_revert` derive complete
numeric word observations from INITIAL representation and actual byte writes.
Their local sufficient separation premise excludes the written byte from every
represented half-open32-byte interval. This is a footprint condition, not a
source profile exclusion or global address-injection assumption. Unrepresented
bytes are unconstrained. The abstract numeric machine is unchanged in these
frame statements; there is no abstract-word MSTORE8 instruction simulation.
The existing natural-index byte slices do not prove gas, expansion or wrapping
address semantics beyond their actual definitions.

`Backend/MemoryOps/PhysicalByteStoreControls.lean` inhabits two nonempty numeric
cells: word7 and a materially high word2^255+9. Actual writes at byte31 and byte96
respect the immediate lower/upper word boundaries, store263 as byte7, and REVERT
reads that changed byte rather than frozen zero. Both complete32-byte reads,
all three numeric machine cells and both saved stack tails are explicit.
An actual overlapping byte63 write clears the last byte of word7. It breaks
WordFrame for the UNCHANGED abstract word, while the complete high neighbour
remains represented. This is not impossibility of representing the update by a
different abstract machine. Empty/one-operand MSTORE8 stacks actually fail.
These APIs have no Source pipeline parameter; no vacuous pipeline tag is added.

`mstore8_revert_checked` proves the existing stackSafe and checkedRun judgments
under the ORIGINAL initial tail.length+4 <= 1024 premise. No suffix guard is
required after an actual halt. Inhabited checked controls retain both complete
boundary observations, reject short operand stacks and refuse an initial1025-word
stack even though MSTORE8 would lower its height. No stack budget is weakened.

Exact standard-only axiom guards cover all new public laws and controls. No
new source/value/state/interpreter, caller rollback, Source-world update,
physical allocator, whole-bytecode/compiler/EVM or full-lane adequacy is supplied.
The broader G32/P6b, G34, G35 and Backfill obligations remain partial.
