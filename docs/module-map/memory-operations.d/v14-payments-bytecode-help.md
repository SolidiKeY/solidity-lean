| `Evm/MemoryLoopHorizonControls.lean` | Populated aliased-memory interface witness at arbitrary horizons; zero/one-turn exit and pending-versus-divergence controls. |
| `Evm/MemoryLoopHorizonAllocControls.lean` | Reached allocation and allocation-before-revert horizon witnesses using the existing owner allocator fixture. |
| `Evm/MemoryLoopFiniteHorizonControls.lean` | Forever-allocating loop with real finite room but impossible all-prefix room; exact cursor/count, false-exit and full-cursor preparation controls. |
| `Backend/Aggregates/ByteSlices.lean`, `Backend/Aggregates/ByteSliceControls.lean` | H10 G18 exact typed Source slice expression, preserved full caller state, entry-derived slice extent/index/object bounds and runtime value import; partial. |
| `Source/CalldataLayout.lean`, `Source/CalldataAggregates.lean`, `Backend/Aggregates/NestedCalldataControls.lean` | H10 S02/G18.04 actual nested calldata reads, string/static-reference slices, typed read-only locations and exact Source state/region/exception controls; partial lowering. |
| `Source/CalldataCopy.lean`, `Backend/Aggregates/CalldataCopyControls.lean` | G18.05 exact ordered validation/copy/conversion outcomes, old cells and staged copy/read controls; Source-only partial. |
| `Source/CalldataCopyAccess.lean`, `Backend/Aggregates/CalldataCopyAccessControls.lean` | G18.05 actual ordered-decoder extent/position and copy/index transport; pre-copy validation versus post-copy bounds failures preserve different full Source states. |
| `Source/MemoryLocalDelete.lean`, `Backend/Aggregates/MemoryLocalDeleteControls.lean` | G18.05 actual identity conversion, total local deletion budgets, protected old aliases and copy/deletion/typed-expression failure-state controls; Source-only partial. |
| `Backend/Aggregates/BoolArrays.lean`, `Backend/Aggregates/BoolArrayControls.lean` | G18.04/.05 actual ABI/validation-derived bool-array value/frame import, bound top local, protected caller heap/locals and Source/intrinsic indexed-read agreement; not fetched/compiler/world correspondence. |
| `Backend/Aggregates/BoolArrayEntry.lean`, `Backend/Aggregates/BoolArrayEntryControls.lean` | G18.04/.05 actual argument decoder/conversion composition and total entry/validation value-frame phase; exact Source diagnostics, independent heaps; not whole-dispatch or machine agreement. |
| `Backend/Aggregates/BoolArrayExpression.lean`, `Backend/Aggregates/BoolArrayExpressionControls.lean` | G18.04/.05 actual typed conversion/scoped argument evaluation; caller-tail restoration, complete Source budget cases and diagnostic/value-frame limits. |
| `Backend/Aggregates/BoolArrayDelete.lean` | Actual typed default allocation/deletion and conditional Source contents transport; general frame/compiler closure remains open. |
| `Backend/Aggregates/IntegerArrays.lean` | Published V07-backed integer array/copy/read/scoped clients; explicit selected-word versus eager-import validation boundary. |
| `Backend/Aggregates/IntegerReadBoundaryWitness.lean` | Inhabited uint8 ABI witness: selected 255 succeeds while later 256 makes eager import revert; native Source observations only. |
| `Backend/Executable/CreationPatchOrder{,Controls}` | Checked immutable/link table commutation and constructor-copy consumers; no fetched-runtime/world claim. |
| `Backend/Executable/CreationFreshness{,Controls}` | Actual successful-creation freshness, heterogeneous account preservation and constructor controls; no allocator/source/EVM correspondence. |
| `Backend/Executable/ConstructorInitialization` | Actual initializer-list composition and exact pipeline-dependent storage/journal observations at argument failure; supplied Source fixtures only. |
| `Backend/Executable/CreationLinkIdentity.lean` | Referenced library bytes derived from actual linking and constructor returns. |
| `Backend/Executable/CreationLinkIdentityControls.lean` | Same-size swapped-link negatives and the empty/unreferenced boundary. |
| `Backend/Executable/CreationReturnInterfaceV1.lean` | H26 generated kernel-return fields and nonempty execution-witness shape; no producer instance. |
| `Backend/Executable/CreationReturnInterfaceV1Controls.lean` | Genuine nonempty input witness and empty-domain/reverted-outcome controls, not a pending-law implementation. |
| `Backend/Executable/CreationReturnInterfaceV1Audit.lean` | Complete interface types and standard-axiom guards. |
| `Backend/Executable/ConstructorFrameSelection.lean` | Concrete checked constructor-argument declaration client: derived frame room, complete caller restoration and order/old-heap controls; native memory-machine scope. |
| `Backend/Executable/ConstructorFrameSelectionAudit.lean` | Exact endpoint signature and scoped standard-axiom guards. |
| `Backend/Executable/CreationReturnProducer.lean` | Concrete H26 kernel-return producer and exact returned-byte equivalence over all referenced library addresses. |
| `Backend/Executable/CreationReturnProducerControls.lean` | Nonempty one-site unused-library equivalence and referenced two-site swap rejection. |
| `Backend/Executable/CreationReturnProducerAudit.lean` | Exact producer/equivalence types and scoped standard-axiom guards. |
| `Backend/Executable/CreationReturnPartition.lean` | Actual constructor-return byte classification with immutable/link/outside certificates and cross-region exclusion. |
| `Backend/Executable/CreationReturnPartitionControls.lean` | Direct classification at an adjacent library boundary, populated patch boundaries and argument-leak negatives. |
| `Backend/Executable/CreationReturnPartitionAudit.lean` | Complete classification signatures and scoped axiom guards. |
