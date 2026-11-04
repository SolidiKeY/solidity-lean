# Inline assembly (Yul)
| Modules | Purpose |
|---|---|
| `Yul.lean`, `Yul/Words.lean`, `Yul/Builtins.lean`, `Yul/Syntax.lean`, `Yul/ExpressionCheck.lean` | Yul library root; words, builtins, intrinsic syntax and checking ([VY1](../feature-work/inline-assembly-vy1.md)). |
| `Yul/BlockTyping.lean`, `Yul/ClosedRun.lean`, `Yul/OpenComposition.lean` | Block typing; closed fuelled execution; direct tier-A runner. |
| `Yul/WordLogic.lean`, `Yul/WordRules.lean`, `Yul/WordAdapterLogic.lean` | Shallow Lean-only word logic and raw-cell runner. |
| `Yul/RawSource.lean`, `Yul/RawSourceAdapter.lean` | Concrete bool-control Source statement adapters. |
| `Yul/Checks/**`, `Frontend/SolcJson/Yul*.lean` | Kernel controls and integer-oracle vectors; solc JSON ingress. |
| `Evm/MemoryLoopHorizon.lean`, `Evm/MemoryLoopFiniteHorizon.lean` (+`Controls`) | P5 all-depth and finite-horizon loop transport ([VY2](../feature-work/yul-physical-memory.md)). |
| `Evm/MemoryRecursiveDemandViews.lean`, `Evm/MemoryRecursiveDemandBounds.lean` | Typed recursive demand/cost cases and allocation-word bounds from computed finite heads and stopping bodies. |
| `Evm/MemoryRecursiveOneTurn.lean` | Stopping-body prefix-room reduction and full recursive loop transport with initial body room. |
| `Evm/MemoryRecursiveCert.lean`, `Evm/MemoryRecursiveCompile.lean`, `Evm/MemoryRecursiveSound.lean`, `Evm/MemoryRecursiveDispatch.lean`, `Evm/MemoryMixedLoop.lean` | Recursive and mixed-body loop certificates, compiler, correctness, dispatch fallback. |
| `Yul/Views/**` | Byte/word memory views, codecs, arrays, objects, heap inventories. |
| `Yul/Adapters/P6ByteWriteOrder{,Controls}` | Complete typed-frame disjoint byte-write commutation, metadata and empty-span controls. |
| `Yul/Adapters/MemoryBytes{,Controls}` | Exact byte-view/backend snapshot-copy and unchanged-map agreement; overlap controls. |
| `Yul/Adapters/RawPhysical{,Controls}` | Existing H11 raw-local frame to bounded P6 physical bytes; explicit readback boundaries and overlay administration |
| `Yul/Views/ComputedPlacement{,Controls}` | Checked actual-heap ordinary placement witness with exact unsupported/overflow accounting. |
| `Yul/Views/ComputedAllocation{,Controls}` | Actual Source allocation preserves computed old geometry and derives fresh extent and every-initial-H MemOK; target refinement remains separate. |
| `Yul/Views/ComputedAllocationWrite{,Controls}` | Incremental typed allocation encoding with computed geometry, whole-map/source identity and exact residual/ReservedOK transport. |
| `Yul/Views/MemoryImageOrder{,Controls}` | All existing typed image constructors: point locality, whole-map disjoint order, generic allocation/FMP order and actual Source program order. |
| `Yul/Views/MixedHeapOrder{,Controls}` | Complete typed-inventory encoding permutation/idempotence and actual unchanged source writeback, with derived separation and tail bounds. |
| `Yul/Views/InventoryDecodeOrder{,Controls}` | Fixed-candidate changed-snapshot visit permutations with exact None, actual Source result and sequential placement/history refresh. |
| `Yul/Views/InventoryCandidateOrder{,Controls}` | Derived owned-pointer candidate order, object decoder invariance, and complete candidate/visit writeback plus sequential refresh permutation. |
| `Yul/Views/InventoryReplay{,Controls}` | Successful changed-snapshot output profile and whole-source replay identity from actual type preservation and retained allocation history. |
| `Yul/Views/SnapshotHashBinding{,Controls}` | Actual source keccak after changed physical-snapshot writeback, using derived exact raw payload and preserved aliases. |
| `Yul/Views/CalldataHashBinding{,Controls}` | Actual calldata-local keccak with implicit memory allocation, clipped payload copy, complete source result and MemOK. |
| `Yul/Adapters/ComputedFrameHeap{,Controls}` | Computed geometry, canonical inventory and complete Source/frame roundtrip; allocator refinement remains separate. |
| `Yul/Adapters/**` | Source/frame-memory agreement with the P6 interface; writeback and slices. |
| `Yul/Compilation/**` | Target-side Yul compilation combinators: stack slots, lowering, opcodes, control ([VY3](../feature-work/inline-assembly-vy3.md)). |
| `Yul/Compilation/PureStatements.lean`, `Yul/Compilation/ScopedStatements.lean` | Intrinsic Yul skip/assignment/sequence and initialized/zero scope compilation; actual Yul evaluator/Scalar certificates, not full Source/G24 adequacy. |
| `Yul/Compilation/OpenExpressions.lean`, `Yul/Compilation/OpenStatements.lean`, `Yul/Compilation/ScopedRawStatements.lean` | Actual VY1 raw binding pack/evaluation/writeback consumers; same-fuel raw Yul/Scalar compilation, with typed Solidity/G24 embedding still open. |
| `Yul/Compilation/NormalControl.lean`, `Yul/Compilation/NormalStackTransport.lean` | Actual intrinsic nested-normal-control compiler evidence; complete stack-only block execution in the existing model, with native/Source/G24 adequacy open. |
| `Yul/Compilation/PhysicalStore.lean` | Actual VY2 byte-view/typed-image agreement with the existing constant-byte compiler slice; native/Source/G24/MemOK closure remains open. |
| `Yul/World/**` | Yul world interface: raw windows, observations, adapters, creation, lifecycle ([VY4](../feature-work/inline-assembly-vy4.md)). |
| `Lowering/P8/FailureProjection.lean`, `Lowering/P8/SourceRealization.lean` | Failure-plan operations on `FailureResources.Bound`; Source session machine; no P8a instance ([VY5](../feature-work/vy5-composition.md)). |
| `Yul/Composition/**` | Generic G01 stage composition with toy controls; P6 MSTORE/REVERT frame correctness. |
| `Bridge/SolidityBridge/Yul/ControlCompleteness.lean` | Bounded vy3-compilation checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/Yul/ControlRealization.lean` | Bounded vy3-compilation checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/Yul/QuotientControl.lean` | Bounded vy3-compilation checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/Yul/QuotientControlControls.lean` | Bounded vy3-compilation checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/Yul/QuotientSelection.lean` | Bounded vy3-compilation checkpoint; typed scope and retained premises are in the module. |
| `Yul/World/SelfDestructBuiltin.lean` | Bounded vy4-world checkpoint; typed scope and retained premises are in the module. |
| `Yul/World/SelfDestructBuiltinControls.lean` | Positive and negative controls for the SelfDestructBuiltin binding; exclusions are stated in the binding module. |
| `Yul/Checks/LocalBoolDivergence.lean` | Constant-true noncompletion and false-condition/timeout controls from inhabited scoped bodies. |
| `Yul/Checks/LocalBoolWhile.lean` | Fuel-boundary, condition-effect, repeated-state and clean Source loop controls. |
| `Yul/LocalBoolDivergence.lean` | Bounded vy1-words checkpoint; typed scope and retained premises are in the module. |
| `Yul/LocalBoolWhile.lean` | Bounded vy1-words checkpoint; typed scope and retained premises are in the module. |
| `Yul/Checks/LocalBoolFor.lean` | Bounded vy1-words checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/LocalBoolFor.lean` | Bounded vy1-words checkpoint; typed scope and retained obligations are stated in the module. |
| `Bridge/SolidityBridge/Yul/BranchModel.lean` | Bounded vy3-compilation checkpoint; typed scope and retained obligations are stated in the module. |
| `Bridge/SolidityBridge/Yul/BranchModelControls.lean` | Bounded vy3-compilation checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/Views/RetainedLocalAlias.lean` | Bounded vy2-physical checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/Views/RetainedLocalAliasControls.lean` | Bounded vy2-physical checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/Compilation/P20InterfaceV1.lean` | Bounded vy3-compilation checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/Compilation/P20InterfaceV1Controls.lean` | Bounded vy3-compilation checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/PrimitivePackets/CheckedAdd/Agreement.lean` | Bounded vy4-world checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/PrimitivePackets/CheckedAdd/Controls.lean` | Bounded vy4-world checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/PrimitivePackets/CheckedAdd/Selected.lean` | Bounded vy4-world checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/PrimitivePackets/CheckedAdd/Source.lean` | Bounded vy4-world checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/PrimitivePackets/CheckedAdd/Target.lean` | Bounded vy4-world checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/Interfaces/P16.lean` | Bounded vy1-words checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/Views/RetainedLocalAliasImage.lean` | Bounded vy2-physical checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/Views/RetainedLocalAliasImageControls.lean` | Bounded vy2-physical checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/Views/NominalInventory{,Laws,Controls}` | Declared UDVT-array snapshot/update dispatch into the existing typed inventory; canonical decode/encode, complete raw reencoding and actual Source safety. |
| `Yul/Views/NominalInventoryUnchanged{,Controls}`, `Yul/Views/NominalInventoryPreparation` | Actual image-derived unchanged-source identity and owner-MemOK completeness of the existing finite heap preparer for the nominal decoder profile. |
| `Yul/Views/NominalInventoryView{,Controls}` | Constructive changed-snapshot Source result, output placement/history and exact full-map realization for canonical nominal inventories. |
| `Yul/Views/NominalInventoryTransport`, `Yul/Views/NominalInventoryReplay{,Controls}` | Actual source-prefix decoder refresh and whole-poststate replay for permutations of nominal output inventories. |
| `Yul/Views/NominalInventoryDynamic{,Controls}` | Exact retained-array/inventory result compatibility, shrink-to-zero/regrowth, original-capacity and constructed output-view controls. |
| `Yul/Views/InventoryTraversal` | Shared typed decode/write/placement/history step with finite inventory traversal. |
| `Yul/Views/InventorySnapshotCursor` | Actual Source-state-indexed physical step, exact Source projection, owner safety and complete raw reencoding. |
| `Yul/Adapters/PhysicalSnapshotSlice{,Controls}` | Actual environment instruction-slice final bytes into typed Source writeback, separate target/preparation outcomes and whole-map bridge. |
| `Yul/Adapters/SelectedPhysicalStore{,Controls}` | Published checked word/byte compiler into actual Source writeback; full Source identity for outside-image byte changes, separate reserved-safety controls. |
| `Yul/Adapters/CheckedResidualStore{,Controls}` | Computed residual-window geometry into compiled byte stores: whole Source identity, complete residual map, both reserved words and state-indexed padding-growth controls. |
| `Yul/Adapters/P6ResidualCopy{,Controls}` | Actual bounded P6 snapshot copies into complete Source/residual views; overlap, reserved bytes, reached accounting and empty-copy identity. |
| `Yul/Adapters/P6ResidualSequence{,Controls}` | Actual P6 request-list execution with derived capacity transport, refreshed complete images and Source identity at every prefix; cascade/order/empty controls. |
| `Yul/Adapters/P6ResidualCapacity{,Controls}` | Executable actual-frame capacity preparation with constructed successful-prefix room proofs, exact pending suffix and Source/residual closure. |
| `Yul/Views/InventorySnapshotHistory{,Controls}` | Changing supplied snapshots with refreshed retained ownership, exact successful prefixes, pending suffix/resumption and final-map reconstruction. |
| `Yul/Views/NominalInventorySequential{,Controls}` | Exact nominal snapshot/sequential Source-result agreement with refreshed candidates, duplicates and capacity controls. |
| `Yul/Adapters/P6ResidualResume{,Controls}` | Existing zero-capacity extension and pending-only checked resumption with chronological full-map/Source closure and replay-sensitive controls. |
| `Yul/Adapters/P6ResidualReserve{,Controls}` | Least sufficient pending-copy word reservation, constructive checked completion and chronological whole-map/Source closure. |
| `Yul/Adapters/P6SnapshotCopy{,Controls}` | Actual P6 copies into owned regions with retained reached frames, canonical Source synchronization, complete reencoding and owner MemOK transport. |
| `Yul/Adapters/P6CopyPreparation{,Controls}` | Canonical nominal update existence from copied words and a concrete changed-field kernel Source/full-map witness on a two-root codec image. |
| `Yul/Adapters/P6CopySource{,Controls}` | Exact prepared Source actions and concrete whole-state/alias result for an owned P6 copy, with typed sibling identity and every-H safety. |
| `Yul/Adapters/P6CopyHistory{,Controls}` | Finite actual P6 copies with per-success Source/cursor refresh, exact stopped synchronization suffix and retained failed physical output. |
| `Yul/Adapters/P6HistoryHash{,Controls}` | Completed-history Source/KECCAK same-payload agreement and raw live-frame hashing across unsupported canonical preparation. |
| `Yul/Adapters/P6HistoryHashRef{,Controls}` | Actual Source subcontext byte hashing after completed copies, exact caller restoration and a nonempty changed-history Source/KECCAK witness. |
| `Yul/Adapters/P6ByteCopyPreparation` | Actual overlapping copy-byte readback and canonical byte-object update existence from header/payload and retained-capacity facts. |
| `Yul/Adapters/P6ChangedPayloadHashControls` | Kernel exact changed-byte Source state, nonempty history and changed-payload Source/KECCAK witness with sibling/alias preservation. |
| `Yul/Adapters/P6ByteObjectCopy{,Controls}` | General payload-only byte copying with derived retained capacity, actual Source action, complete refreshed view and unrelated-cell/layout preservation. |
| `Yul/Adapters/P6ByteFamilyCopy{,Controls}` | Shared bytes/string payload-copy realization preserving intrinsic data types, with exact byte-API specialization and cross-word string controls. |
| `Yul/Adapters/P6RetainedRegionCopy{,Controls}` | Checked header-changing copies in original retained byte/string regions; exact capacity failure, constructed Source/full-map closure and kernel shrink/regrowth. |
| `Yul/Adapters/P6ByteReferenceReads{,Controls}` | Exact Source byte/string-backed memory location formation, length/read/write access and panic laws, with retained shrink/regrowth access controls. |
| `Yul/Adapters/P6ByteReferenceWrite{,Controls}` | Actual Source byte writes and computed bounded MSTORE8 share exact typed writeback, selected full-map encoding, unchanged-state identity and exterior-byte preservation. |
| `Yul/Adapters/P6ByteWriteInventory{,Controls}` | Constructed complete mixed-inventory refresh after actual Source/MSTORE8 byte writes; same-state writeback, whole-map reencoding, retained history and sequential controls. |
| `Yul/Adapters/P6ByteWriteSub{,Controls}` | Actual Source substitution around represented byte writes, with linked success/late halt, exact caller restoration and whole mixed-map reconstruction. |
| `Yul/Adapters/P6ByteAssignment{,Controls}` | Actual resolved Source indexed-byte assignment, exact local-operand horizon/errors and constructive shared Source/physical mixed-inventory result. |
| `Yul/Adapters/P6ChainedByteAssignment{,Controls}` | Actual effectful byte-assignment RHS with two chronological Source/physical inventories and exact inner/outer failure prefixes. |
| `Yul/Views/RetainedLocalAlias{,Controls}` | Actual typed local-assignment capture preserves overwritten entry aliases and returned references, with whole-store identity and dormant-path loss controls. |
| `Yul/Views/RetainedLocalAliasImage{,Controls}` | Actual alias capture drives checked enlarged retained images, source traversal, whole-storage unchanged writeback and exact complementary raw-map reconstruction. |
| `Yul/Views/RetainedAliasOwnership{,Controls}` | One actual alias-plus-Source storage run with success-only complementary journaling, full reencoding, static prefix retention and paired-boundary rollback controls. |
| `Yul/Views/RetainedAliasSequence{,Controls}` | Actual Source-bind ownership sequencing keeps reached journals and capture prefixes through first/late refusals and two successes; checked fields reproduce public preparation. |
| `Yul/Views/RetainedAliasFrames{,Controls}` | Derived actual sequence boundary, paired child/outer rollback and complete prefix/initial raw reconstruction with distinct retained-tail controls. |
| `Yul/Views/RetainedAliasTransaction{,Controls}` | Actual success-only Source endTx sequence, complete persistent reconstruction, transient/journal reset, reached-error prefix and every-H memory safety. |
| `Yul/Views/RetainedAliasSub{,Controls}` | Actual caller-local substitution of the checked ownership sequence with reached pair, full reencoding, late-static prefix and rollback transport. |
| `Yul/Views/RetainedAliasSubSafety{,Controls}` | Universal unchanged heap and every-H caller MemOK through actual ownership substitution on all branches, with restored dormant RefOK and distinct-context controls. |
| `Yul/Views/RetainedCallerCoverage{,Controls}` | Actual saved-caller capture selects duplicate-safe visits and checked child packs, with typed aliases, halted empty-callee source traversal and complete unchanged reconstruction. |
| `Yul/Views/RetainedCallerHeaders{,Controls}` | Declaration-traced saved-child dynamic header registrations in actual prepared source inventories, with pre-alignment cursor, physical slot and typed-length controls. |
| `Yul/Views/RetainedLiveCoverage{,Controls}` | Successful source traversal derives actual header lengths and all generated live fields across child/image inventories; dormant payload and roots-only loss controls. |
| `Yul/Views/PackedCellUpdate{,Controls}` | Actual typed persistent scalar writes preserve complete canonical finite packed views and the entire complementary raw map, with full reencoding and padding/static controls. |
| `Yul/Views/TransientCellUpdate{,Controls}` | Actual typed transient writes preserve finite packed agreement and original complement, with persistent isolation, rollback/reset and declared-root padding/account controls. |
| `Yul/Views/MixedCellSequence{,Controls}` | One actual persistent/transient typed Source bind with same-state complete bank reconstructions, precise static prefixes and paired rollback; equal-slot bank controls. |
| `Yul/Views/RepeatedCellWrites{,Controls}` | Arbitrary finite actual same-field typed Source writes in the computed bank, full raw reconstruction with original complement, every-H safety, rollback and duplicate/static controls. |
| `Yul/Views/FiniteCellWrites{,Controls}` | Arbitrary finite different-path intrinsic requests through one Source run, actual bank dispatch, both complete raw views/original complements, safety/static/rollback and domain-boundary controls. |
| `Yul/Views/DeclarationDefaults{,Controls}` | Zero payloads derived from declaration-selected codecs through relocation/registration/packing; reset-check availability equivalence and actual transient-root full reset controls. |
| `Yul/Views/FixedDeclarationDefaults{,Controls}` | Actual recursive fixed-array/struct and ordered-root packing derives optional default payloads, reset-check availability and empty-store full encode/writeback; None/default distinction controls. |
| `Yul/Views/CellWritesCalldataHash{,Controls}` | One actual typed storage-write/calldata-hash computation with same-state raw banks, clipped same-Fixed payload binding, allocation safety and exact timeout/static prefixes. |
| `Yul/Views/CellHashFinalization{,Controls}` | Transaction finalization of one actual mixed typed-write/calldata-hash run: persistent reconstruction with original complement, transient/default and journal reset, late-timeout prefix controls. |
| `Yul/Views/LinkedCellHash{,Controls}` | Computed account-tagged initial journal complements and whole persistent reencoding from the actual finalized journal, with nonzero unknown-slot and account/bank controls. |
| `Yul/Views/CellHashFrames{,Controls}` | Actual mixed-write/hash external projection, child-prefix rollback, committed-child/enclosing rollback and restored journal-driven full-map reconstruction; retained calldata aliases and real child mutation controls. |
| `Yul/Views/CellHashRollback{,Controls}` | Actual Source mark/write/hash/rollbackTo execution: exact whole reached state with restored external writes and retained heap allocation, journal-driven map reconstruction and late-timeout prefix controls. |
| `Yul/Views/CellHashMemory{,Controls}` | Constructive full physical realization of actual mixed-write/calldata-hash allocation: header/payload/FMP, whole map and unchanged Source writeback, exact residual bytes and same-Fixed observed hash; computed-placement premises retained. |
| `Yul/Views/AllocationRefresh{,Controls}` | Computed placement refresh after actual allocation: occupied-only coordinate/free agreement and typed image transport derive subsequent old reads, sequential allocation/full-map writeback, future-coordinate and zero-footprint controls. |
| `Yul/Views/AllocationSequence{,Controls}` | Finite actual allocation producer certificates with reached-heap validity; constructive full-map/writeback/ReservedOK transport, typed returned-reference validity, pointer-to-prior-object and admission-boundary controls. |
| `Yul/Views/NewMemory{,Controls}` | Actual newArray evaluator with intrinsic uint256-local length, existing size panic/timeout and newData; constructive full physical allocation/writeback with static bytes/bool[] and padding controls. |
| `Yul/Views/NewMemoryOperand{,Controls}` | Universal actual newArray operand decomposition and reached-prefix success/panic/halt transport; physical realization at the reached state, postincrement and late-timeout controls. |
| `Yul/Views/AllocationPointer{,Controls}` | Actual allocated-reference decoding and existing pointer writeback agree with newArray/getV/writeLoc execution, including writer halts and owner safety; aliases, bounds and decoder-boundary controls. |
| `Yul/Views/ArrayWordStore{,Controls}` | Real one-word array patch derives updated codec reads and exact Source member writeback, whole selected-array/complement ByteView reconstruction, new-pointer sink and dynamic-header mutation controls. |
| `Yul/Views/ArrayWordHeap{,Controls}` | Derived image reads for every object after actual array word writes, complete generated-heap reconstruction/unchanged whole Source writeback/MemOK/reserved transport, with four-object consumer and unknown-tail controls. |
| `Yul/Views/ArrayWordRetained{,Controls}` | Existing allocation lineage extends through actual same-shape array word updates; whole-map/Source writeback retains the original capacity snapshot, dormant tail and free pointer after a real shrink/write sequence. |
| `Yul/Views/StructWordStore{,Controls}` | Actual checked heterogeneous field updates derive canonical words and raw mstore/Source writeback equality, selected-struct/complement reconstruction, alias/scalar/bool and preparation-boundary controls. |
| `Yul/Views/StructWordHeap{,Controls}` | Actual struct-field word writes derive every post-write heap image read, complete map reconstruction, whole Source writeback, every-H MemOK and reserved preservation; six-object alias/padding and canonicality/type-error controls. |
| `Yul/Views/StructWordRetained{,Controls}` | Existing allocation history extends through typed struct field writes with whole-map reconstruction and whole Source writeback against the original snapshot; actual pointer/boolean sequence and failure-prefix controls. |
| `Yul/Views/ByteElementStore{,Controls}` | Actual bytes/string memByte writes derive a one-byte patch, complete heap reads/reconstruction, original-history whole Source writeback and every-H MemOK; aliases, second-word byte, padding and exact bounds/static controls. |
| `Yul/Views/ByteElementFrames{,Controls}` | Actual sub success/halt restore caller locals while preserving byte mutations and original-history whole-map/Source writeback; explicit mark/rollbackTo heap retention, caller-prefix/nested-context and bounds controls. |
| `Yul/Views/MemoryDelete{,Controls}` | Actual zeroVal/deleteLoc transport for canonical array/struct defaults and byte elements, complete-map/original-history writeback, timeout/type/index controls and a separately observed reference-allocation boundary. |
| `Yul/Views/ReferenceDelete{,Controls}` | Actual bytes/string reference deletion composes computed empty-object allocation and struct pointer write, deriving exact coordinates/FMP, complete-map/Source writeback, alias/padding and allocation-before-type-error controls. |
| `Yul/Views/ReferenceDeleteRetained{,Controls}` | Allocating reference deletion extends actual retained origin/history with complete-map and whole Source writeback; earlier shrink capacities/dormant words survive, with checked regrowth alias recovery. |
| `Yul/Views/RetainedArrayHeader{,Controls}` | Checked length changes derive all refreshed heap image reads, complete raw-map reconstruction and original-history whole Source writeback; shrink/delete/regrow closure, aliases/padding and capacity boundary controls. |
| `Yul/Views/RetainedByteHeader{,Controls}` | Bytes/string payload computed from one raw map yields all resized heap reads, complete reconstruction and original-history whole Source writeback; sequential regrowth, four aliases, live padding and capacity boundary controls. |
| `Yul/Views/ByteWriteSequence{,Controls}` | Arbitrary finite actual Source byte-write plans derive source erasure, complete reached-prefix map/whole Source writeback and original lineage, including late bounds failures; repeated/cross-word/skipped-suffix and sub-local controls. |
| `Yul/Views/MultiRootByteWrites{,Controls}` | Actual heap lookup derives multi-root byte ownership or unchanged owner errors; arbitrary finite plans reconstruct complete reached-prefix maps and retain whole Source writeback/history, with non-byte/dangling/bounds controls. |
| `Yul/Views/MultiRootByteFrames{,Controls}` | Universal heap-only/type-map preservation and actual sub-local caller transport for multi-root plans; complete caller map/writeback/history with distinct nonempty child/caller aliases and success/halt controls. |
| `Yul/Views/BytePlanHash{,Controls}` | Actual keccak after finite multi-root writes derives final bytes and exact physical preimage from the same reached map, with owner error short-circuiting, restored-caller and noninjective preimage controls. |
| `Yul/Views/BytePlanHashAlias{,Controls}` | Byte/string-backed bytes aliases derive reached hash contents and exact physical preimages after actual multi-root writes, with same-path aliases, prefix failure and caller restoration controls. |
| `Yul/Views/BytePlanHashFrames{,Controls}` | Actual child write/hash return through Source local substitution, with arbitrary valid caller aliases, every-H safety and same-map complete Source writeback on success/halt. |
| `Yul/Views/MultiRootByteBoundary` | Actual multi-root byte writes preserve the raw complement above the placement end, using selected typed object geometry and real source failures. |
| `Yul/Adapters/P6MultiRootByte{,Controls}` | Derives finite-frame Fits for multi-root source byte plans and constructs exact same-map P6 frames with complete source writeback, original-H safety and metadata preservation. |
| `Yul/Views/MultiRootByteAppend` | Exact chronological concatenation of actual multi-root coupled plans, retaining stopped prefixes and skipped suffixes. |
| `Yul/Adapters/P6MultiRootByteRefresh{,Controls}` | Derives next-plan source/frame preparation from actual first output and connects successful sequential physical plans to one concatenated execution, with stale-state and failure controls. |
| `Yul/Adapters/RawPhysicalInventory{,Controls}` | Complete published raw-local cell enumeration in a constructed separated finite frame, preserving all raw bits, clean/world fields and residual bytes while distinguishing absent overlays. |
| `Yul/Adapters/RawPhysicalProducer` | Consumer of the actual bounded P16 Adapter.correct field, transporting its exact reached Source representation through complete raw-local physical capture under the unchanged coherent-input premise. |
| `Yul/Adapters/RawPhysicalWriteback{,Controls}` | Whole raw-map and complete P6-frame identity after unchanged all-cell decode/reencode, retaining residual bytes and distinguishing view equality from overlay administration. |
| `Yul/Adapters/RawPhysicalUpdate{,Controls}` | Derives complete raw-local inventory reencoding/readback after actual RawFrame.write and P6/MSTORE word updates, retaining other cells and residual bytes under explicit span/coordinate guards. |
| `Yul/Adapters/RawPhysicalInterior{,Controls}` | Complete raw-local inventory transport after an interior-byte P6/MSTORE8 update, using exact full-word codecs and retaining other bytes/cells under explicit coordinate/fit guards. |
