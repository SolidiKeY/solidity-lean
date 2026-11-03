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
  allocation control derives its one-word demand bound from the actual
  computed certificate and discharges allocator room using the represented
  cursor; both recursive and mixed examples now have concrete room proofs.
- Views: byte/word views and codecs, placement and images, scalar codecs,
  static/dynamic `uint` arrays, members, pointers, byte objects, heap
  inventories and preparation, joint and aggregate views. `ByteView` keeps its lightweight API; `Adapters/MemoryBytes` proves exact
  operation agreement with the existing `Environment.Memory` byte map.
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
recursive dispatch into the compiler, allocation bounds for arbitrary recursive programs,
G36.02 recursive/enclosing transport.

## Canonical nominal memory

`Views/NominalMemory` adds UDVT word decoding through the actual underlying
canonical scalar codec, preserving nominal type indices. Its successful words
reencode exactly; encoded supported values decode identically. Array preparation
uses the existing decoder and actual `Source.heapPut`; every original heap typing
is preserved through its complete success/error result. Declaration lookup is
checked separately from the layout fallback. Controls inhabit a real allocated
heap and observe updates through two actual Source aliases.

The explicit expected array length is a preparation guard, not proof of old
length, capacity or valid output placement. Whole-state unchanged identity is proved from the actual old typed heap data,
declaration and exact header/word encoding facts. For same-length writes to an actual old typed array, output placement is
constructed with unchanged addresses, shapes and free choice. Types, next,
boundedness, unrelated cells and non-heap source fields are preserved; exact
typed payload readback matches the raw canonical words. A changed-snapshot
kernel control inhabits this operation. General nominal allocation provenance and universal nominal heap agreement
remain open. Dirty
words are not cleaned or assigned source/Yul failure semantics by this codec.

`Views/NominalRetained` extends canonical nominal dynamic arrays within an
actual `RetainedAllocation`. Header size is checked against the original
allocated shape, including the length word. Successful preparation derives the
real source write and a current placement with the new length plus original
retained provenance. Unchanged snapshots preserve the complete source state;
every original heap typing survives the complete source result. Kernel controls prove actual shrink-to-zero and regrowth. Runtime controls
observe the same nonzero raw tail, two source aliases, coherent free/zero
words, source type-error and preparation boundaries.
This is canonical snapshot preparation with explicit old typed contents and
retained ownership, not general allocation, dirty-word or assembly adequacy.

## Byte API agreement

`Adapters/MemoryBytes` proves full-map snapshot-copy equivalence between
`Views.copyBytes` and backend `writeBytes` of the old `readMemory` result.
Byte update and read APIs agree definitionally; unchanged snapshot writeback
is identity for the whole mathematical byte map, without size or canonicality
restrictions. This keeps backend imports out of the lightweight Views module.

The actual P6 `copySnapshot` and `store8` byte projections now agree with
`Views.mcopy` and `Views.mstore8`. P6 self-copy uses the common identity proof.
Nonempty self-copy can still change access metadata; physical spans and fit
premises remain unchanged. These laws do not supply target MCOPY execution,
allocation refinement or identification of carried intrinsic state with bytes.

## Recursive one-turn room

`Evm/MemoryRecursiveOneTurn` reduces future-prefix allocation room to initial
body demands when the actual successful body forces its next condition false.
The public full-loop transport uses the real recursive certificate's derived
profile soundness. It does not impose a loop horizon, alter admitted programs or
assume target/source adequacy. The initial body-demand room remains explicit.
`MemoryRecursiveDemandViews` exposes actual constructor cases without assuming
code-list append injectivity. `MemoryRecursiveDemandBounds` combines the finite
head's computed source `prefixBudget`, nonallocating tails and real stopping facts.
`MemoryRecursiveAllocation.demand_bound` proves every demand of its computed
certificate is at most one word. `actual_room` then uses the represented cursor
and `one_word_input`; `correct actual_room` is a closed kernel transport for that
example. This does not discharge room for arbitrary allocating programs.

## Physical byte-write order

`Adapters/P6ByteWriteOrder` composes two actual `writeSpan` operations, deriving
capacity transport for the second span. Disjoint byte regions commute on the
complete existing P6 frame: byte data, logical carrier, key, capacity and exact
high-water count. Frame extensionality explicitly requires metadata as well as
the complete byte image; no byte-only equality is promoted to frame equality.
Empty spans are included even when their offsets lie inside the other span.

Kernel controls instantiate complete-frame order equality for both pipeline
tags and the empty-inside case. Separate runtime controls observe nonzero raw
bytes, exterior preservation, access growth and the expected order sensitivity
of overlapping writes. No overlap is refused by the operation. These are
physical side-frame laws, not typed Source-heap writeback, target execution, gas
accounting or global storage/transaction journal adequacy.

Same-span writes also satisfy full-frame last-write replacement (`writePair_overwrite`). The earlier payload disappears, while unknown exterior bytes and the real access accounting are preserved. The law includes empty spans; it is a physical frame law, separate from Source-heap or transaction-journal adequacy.

`FrameHeap.residual_span_unchanged` connects an actual bounded P6 `writeSpan` on a computed complete heap image to whole Source-state writeback identity. It also proves the complete reached raw map equals that byte write, so modified residual bytes are retained. The canonical support, initial MemOK, Placement, retained allocation, physical capacity and object-complement premises remain explicit. Object separation alone does not establish reserved-word safety, allocation reachability or language admission. The mixed six-root control exercises both pipeline tags.

`FrameHeap.calldata_residual_unchanged` composes the actual bounded Source calldata-slice producer with the computed physical heap image. It derives source success, exact copied bytes/readback and complete Source-state writeback identity, using the real calldata reference bound and destination length. A destination-size mismatch remains successful Source evaluation with preparation `None`; this theorem does not reclassify failures or establish general source/opcode/allocator adequacy.

`P6Inputs.source_hash_local` proves the complete actual Source `keccak256` builtin result/state for a memory-byte local and real heap lookup at every horizon `n + 3`. `copied_builtin_hash` connects this producer to the actual target hash of identical copied calldata; its per-input concrete Fixed equality remains explicit. Concrete-Fixed controls cover both pipelines, wrong preimages, lower-horizon timeout and dangling references. No raw-local cleaning, collision freedom, placement or compiler adequacy follows from these laws.

`HeapWriteback.run_checked` handles arbitrary finite numeric-array write lists, deriving the valid prefix and first invalid index with the existing list traversal and the actual represented array length. It proves complete Source success/error, the prefix word/byte image, unchanged locals/other roots and every-initial-H MemOK. A halt retains the successful prefix and does not execute its suffix. This is local monadic execution, not an implicit transaction rollback or universal memory support.

`HeapWriteback.checked_reads` observes the actual returned state of an arbitrary finite numeric write sequence, whether it succeeds or halts at its first bounds failure. It derives agreement between fresh `readLoc`, every retained local alias expression at horizon `n + 2`, and the complete physical word bytes of the successful prefix. It preserves every initial MemOK; it does not resume execution after an error or infer rollback/intermediate-capture adequacy.

`ObjectWriteback.all_types_checked` computes the first actual `heapPut` type error for arbitrary lists of dependent Source object packets. Only the executed prefix requires the existing DataOK/Top/Inner invariants; unchanged heap typing makes the original type scan valid at every step. Complete success/error state, nonheap fields, unrelated roots and every initial MemOK are retained. Shared-child controls distinguish prefix preservation from suffix execution. This closes Source request sequencing, independently of physical decoder completeness.

`ObjectWriteback.putAll_perm` proves complete Source result/state equality for arbitrary permutations of type-correct dependent object requests to distinct root IDs. It derives pair commutation from actual heap writes and transports typing through the sequence. Same-root aliases and failing type guards are not covered by the order premise; controls show their observable order dependence. Data safety remains the existing separate Prepared/MemOK obligation, and physical serialization adequacy is not inferred.

`PhysicalObject.commit_many_checked` derives owner data invariants directly from concrete byte/string snapshot decoding, then proves complete Source batch success or first type error with exact prefix state and every initial MemOK. It reconstructs the complete raw snapshot without discarding residual bytes. Bytes/string and both-pipeline controls show the first decoded payload surviving a mismatch while the suffix remains unexecuted. This does not infer physical bounds or allocation ownership from decoding.

## Raw local words and physical bytes

`Adapters.RawPhysical` consumes the existing H11 `RawFrame` and bounded P6 byte operations. A store serializes all 256 raw bits; a physical byte-view load records them through the actual raw overlay write. Clean Source locals, world and unrelated raw cells remain separate. The roundtrip is raw-view equality, not administrative identity: a previously absent overlay becomes `some word`. Bool/u8 conversion occurs only at the existing explicit per-pipeline return boundary. Controls distinguish dirty words2/257 from their return values, preserve nonzero exterior bytes and roundtrip the maximum word. These are byte-view transport laws, not emitted MLOAD, dirty storage transport, allocation or universal pipeline adequacy.

The raw-local store now has an actual target instruction link: `RawPhysical.store_target` proves the published `Environment.cryptoStep` MSTORE result, including complete reached bytes and caller stack tail. `source_backend_wordBytes` derives equality of the existing Source/backend encoders; its helper handles arbitrary byte widths without a new encoder definition. Controls discriminate operand order and endianness. This strengthens the store side only: total byte-view reads are still not physical MLOAD steps, and gas/allocation/compiler adequacy remains separate.

`RawPhysical.load_frame` consumes the existing regional P6 WordFrame to derive a nonwrapping bounded byte span, an actual fixed-cell Evm word-machine load, and identical H11 raw-local readback with unchanged clean locals/world. Word indices are explicitly scaled by32, and the regional byte relation survives. Controls distinguish cell1/byte32 from byte1. The optional Bridge already provides external memory macro refinement (`ExternalEvm.MemoryRefinement.load_refines`) under its own Represents, preallocated-capacity and PaddingCorrect premises; those remain separate, rather than being inferred from this core theorem.

## Computed ordinary placement

`Views.ComputedPlacement.prepare` derives existing Placement objects from actual finite Source heaps. It inspects ordinary memory constructors, reports all unsupported occupied IDs, preserves sparse holes, and checks the computed final extent against Word range. Cumulative addresses use actual shape sizes; zero footprints retain size0 and reserve one byte solely for distinct addresses in this witness. It imposes no alignment rule. `Adapters.ComputedFrameHeap.prepare` then computes the canonical object inventory and physical frame, retaining separate placement, frame-room and object-image errors. Its roundtrip theorem proves whole Source identity without supplied coordinates, shape laws, separation or inventory.

The constructor selects a mathematical witness; it is not the Solidity allocator policy, target-chosen placement, retained allocation history, reachability or AllocationRefines. Preparation errors are not source/Yul failures. Existing canonical type support and owner MemOK, actual extent checks and frame bounds remain explicit. Controls cover sparse and zero-footprint objects, empty heaps, scalar-object rejection, huge extent overflow, and two actual Source allocations with complete physical/source roundtrip and residual bytes. The existing oversized-MemOK counterexample and whole memory contracts remain unchanged.

`ComputedFrameHeap.prepare_sound` derives complete Source/writeback soundness from an actual successful result, recovering its checked geometry and frame-room facts instead of asking consumers to restate them. `prepare_reserved` separately preserves real input ReservedOK; no reserved byte is initialized or cleaned. Controls distinguish frame-room and unsupported-child errors and confirm that an input zero-word7 remains7 when ReservedOK is absent. Those failures and bytes are preparation observations, not language admission or allocation decisions.

Successful computed image preparation also yields the original `ObjectWord`/`ObjectByte` read laws (`prepare_word` and `prepare_byte`) without extra MemOK or canonical-decoder support premises: the actual constructor result already supplies typed images, coverage and unique IDs. `prepare_residual` retains separated bytes, and `prepare_prefix` retains every scratch/reserved byte below128 even without ReservedOK. Kernel controls observe headers/payload bytes and retain an invalid zero-word byte7. These are conditional read-side laws; the universal `MemoryLayoutObligations.realize` contract remains open.

`ComputedPlacement.allocRef_geometry` transports the computed witness through actual Source allocation: every occupied old address and shape stays fixed, the fresh logical ID receives the old computed end, and the end advances by the actual shape reservation. Actual allocRef execution and every original-H MemOK follow from existing typed data validity. Zero-size spacing remains this mathematical witness choice; the checked Word extent is a preparation bound, not a language limit or target allocation policy. Target allocator provenance/refinement remains open. Controls retain two real aliases and include a zero-size allocation followed by a nonempty allocation.

`AllocatedComputedFrame.allocation_roundtrip` connects actual allocRef execution to complete computed-frame preparation and whole-source unchanged writeback for that same allocated state. Enlarged-heap codec support is derived from real old/fresh lookups rather than supplied as an output inventory. Initial every-H MemOK, typed object validity, canonical support, computed Word extent and frame capacity remain explicit. Controls preserve a nonzero unrelated tail in both pipelines. The supplied raw free word is not asserted to satisfy ReservedOK; this component neither initializes allocator bytes nor proves target allocation refinement.
