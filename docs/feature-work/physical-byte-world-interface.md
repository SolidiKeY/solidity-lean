# P6 BYTE-WORLD typed dependency contract

`Backend/MemoryOps/PhysicalByteWorldInterface.lean` freezes
`Solidity.Backend.MemoryOps.Physical.ByteWorld.Producer`.
Its parameter `loadCode : Nat → Backend.Program` is a static cell-indexed
program in the existing Backend syntax. It cannot inspect initial memory,
a desired value, Source execution or a future proof to choose the code.

The single pending field `Producer.load` quantifies an existing Environment
frame/memory, intrinsic word cell/value and arbitrary caller stack tail.
Initial premises are `32*cell+32 ≤ 2^256`, `tail.length+1 ≤ 1024`, and the exact
32-byte image `readMemory bytes (32*cell) 32 = wordBytes value`.
Its conclusion is ACTUAL `Environment.runSlice frame (loadCode cell)` returning
the canonical value word over that same tail and exactly unchanged memory.
No Producer instance, code implementation or replacement evaluator is supplied.
Concrete code must later carry exact declaration/commit/hash and emission
provenance; satisfying this contract is not Source compiler selection adequacy.

`Producer.load_at` is explicitly conditional on that pending field. It derives
the numeric value from the INITIAL published WordFrame, then relates existing
intrinsic MLOAD and the field's actual byte run, retaining all live word cells.
It does not prove existence of code or discharge the producer obligation.
`current_mload_boundary` separately records that literal MLOAD is currently
absent from the published combined slice. This is not an impossibility theorem
for every possible code; MSTORE and MSTORE8 already exist.

Reuse the already-published `Backend/MemoryOps/PhysicalWordFrame.lean`,
`Backend/MemoryOps/PhysicalByteJournal.lean`, and
`Backend/MemoryOps/PhysicalWorldUnwind.lean` for the existing initial relation,
actual stores, tied checkpoints, Source operation journal and ABI unwind.
Those interfaces are consumed unchanged from public commit6f3eedf0. They are
not replaced by a second World relation here. In particular worldJournal is a
projection of actual Source stores into the existing local byte journal; it
is not a physical encoding of Source accounts/storage or a World codec.

Both headline laws have exact measured standard-only guards. This interface
checkpoint leaves concrete byte-load code/provenance, gas/active-memory and
stack-safe program closure, physical Source/World representation and final
Source/V10/compiler/EVM correspondence explicitly open. It supplies no concrete
P6 producer inhabitant or whole-lane completion evidence.
