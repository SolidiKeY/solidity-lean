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
