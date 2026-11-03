# Physical memory views, adapters and recursive loop transport (VY2)

From the vy2-physical lane: Yul memory views (`Yul/Views/**`), Source/frame
adapters onto the P6 interface (`Yul/Adapters/**`), the P5 loop horizon and the
recursive/mixed loop compiler extension (`Evm/MemoryLoop*Horizon*`,
`Evm/MemoryRecursive*`, `Evm/MemoryMixedLoop*`).

## Proved

- Loop horizon (P5): `Evm/MemoryLoopHorizon.lean`,
  `Evm/MemoryLoopFiniteHorizon.lean`: all-depth and finite-horizon loop
  transport over `TLoop.iterN`, with controls.
- Recursive and mixed loops: certificates, compiler and room metadata
  (`MemoryRecursiveCert`, `MemoryRecursiveCompile`, `MemoryRecursiveRoom`),
  closed mutual correctness (`MemoryRecursiveSound`: `ProgCert.profile_sound`,
  so the top-level `StmtCert.correct` needs no lifting premise), outer-loop
  lifting, nesting and budgets, mixed-body loop transport.
  `MemoryRecursiveDispatch` tries the existing compiler first and falls back on
  refusal; it is additive and not wired into `Compiler.compile`. The recursive
  allocation control keeps its allocator-room premise open (the mixed-loop
  control discharges it).
- Views: byte/word views and codecs, placement and images, scalar codecs,
  static/dynamic `uint` arrays, members, pointers, byte objects, heap
  inventories and preparation, joint and aggregate views. `ByteView` is a
  separate `Nat → UInt8` model beside `Environment.Memory`.
- Adapters: `P6Memory`, `P6ByteMemory`, `P6Inputs`, `MemoryAgreement` relate
  Source and frame memory to bytes for dynamic `uint256` arrays only;
  `FrameMem.st` is not identified with the changed Source heap. Frame
  construction, writeback, physical objects and calldata slices
  (`FrameHeap`, `HeapWriteback`, `ObjectWriteback`, `PhysicalObject`,
  `SourceSliceFrame`, `ImageIdentity`). They use the current `Source.Fr` with
  `cd`.

`MemoryLayoutObligations`, `MemoryWritebackObligations` and
`AllocationRefines` are interfaces with no instance and no consumer.

## Open

Other element types, a Source-heap identification for `FrameMem`, wiring the
recursive dispatch into the compiler, the recursive allocator-room premise,
G36.02 recursive/enclosing transport.
