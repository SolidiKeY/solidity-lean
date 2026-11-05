# Nested word store and terminal physical byte store

`PhysicalNestedFixedWrite.lean` consumes the exact nested word-store producer.
`PointerFrame.numeric_write` preserves every protected pointer cell distinct
from the changed numeric destination. `nested_fixed_word_byte_store` derives
whole existing nested word-code execution, actual terminal Environment.cryptoStep
MSTORE at the scaled offset, reached numeric and pointer frames, unchanged bytes
outside the selected 32-byte span, and an actual Failure.Slice REVERT observation
of that reached memory. All are conclusions from INITIAL Objects representation,
typed scalar/root selection and bounds, WordFrame, PointerFrame, no-wrap span
and local destination separation. No desired postrelation/run is supplied.
Runtime lengths/index/value remain generic. The source/profile/heap/evaluators
and existing writer/reader algorithms are untouched.

These are intentionally distinct APIs: the complete pointer/index/store code
runs on the word machine; terminal MSTORE runs in Environment.cryptoStep;
REVERT reads its reached memory through Failure.Slice. No Failure.Slice MSTORE,
full Environment.runSlice execution, stack-admission/gas check or emitted byte
pointer-load prefix is claimed. The missing numeric load producer in
PhysicalByteWorldInterface remains explicit; current_mload_boundary says literal
MLOAD is absent, not that every possible implementing program is impossible.
This component is not a concrete inhabitant of ByteWorld.Producer.

The inhabited controls construct a 16-row physical memory image from existing
writeBytes, proving all reads. Numeric cells are [2,3,4,8,9,10,11,16,24,25,26];
pointer cells are [0,1,17,18,19]. Pointer bytes are scaled: cursor32 becomes1024,
root16 becomes512, LEFT8 becomes256 and RIGHT24 becomes768. Numeric values are
not scaled. A real negative proves CellAt(wordMachine,physicalBytes,1) impossible:
the pointer byte image512 differs from numeric16. No pointer image is silently
identified with WordFrame's numeric image.

`nested_physical_prefix` BOTH original pipelines joins the actual nested Source
assignment/expression statement and strong word certificate to the terminal byte
write. Actual selected LEFT index1 means logical cell9 and byte offset288.
Source MemOK, typed objects distinct from the selected child and other Source addresses, locals/heap.next/world
fields, reached strong representation and complete allocator are retained.
The complete 16 physical rows are at word cells
[0,1,2,3,4,8,9,10,11,16,17,18,19,24,25,26], initially encoding
[1024,512,42,1,1,7,0,max,0,3,256,256,768,8,9,10]. Terminal MSTORE changes only cell9
to42; the complete before/after byte tables and a changed-versus-frozen-table
negative are proved. Padding, cursor, all locals, repeated parent pointers and
all child/neighbour contents remain included. REVERT returns the actual newly
written wordBytes42 and retains its exposed slice tail/memory; no Source/world
transaction rollback or byte-target panic-payload equivalence is asserted.

Five headline laws/clients have measured exact standard-axiom guards: pointer
numeric framing and initial byte fixtures use [propext, Quot.sound], the remaining
three use [propext, Classical.choice, Quot.sound]. Initial focused checks passed;
all earlier failed receipts and seals remain preserved. Read-only independent
source/control and committed-artifact reviews are recorded in delivery.

The initial byte image is an explicit fixture, not a proof of a compiled byte
allocator or Source construction. General physical memory, byte-load/emission,
SourceWorld/ABI unwind/byte-origin, full original gates and final Source/V10/
target/world/compiler/EVM adequacy remain open. G32/P6b/G34/G35.02 reference
remainder/G35.03/Backfills A/B stay partial; G33 and G35.01/.04/.05/.06 remain
delegated/open. Goal remains unchanged BLOCKED; no publication claim.

Prepared two-terminal-store runSlice composition is now proved in
PhysicalByteStoreSequence.lean; see nested-fixed-byte-write-delete.md. The
missing byte-load/emission prefix boundary is unchanged.
