<!-- Generated from docs/module-map/memory-operations.d/ by scripts/coord-tools/fragments.sh; edit the fragments there, not this file. -->
# Memory operation proof components

These modules retain explicit Source/heap/word representation premises. Their
presence does not establish frontend admission or physical EVM correspondence;
see [the checkpoint boundary](../feature-work/memory-operation-proofs.md).

| Module | Holds |
|---|---|
| `Backend/MemoryOps/CalldataAgreementChildren.lean` | Refine actual child footprint transport with INITIAL computed-payload |
| `Backend/MemoryOps/CalldataArrayRead.lean` | Structural observations of every published decoded calldata array type, |
| `Backend/MemoryOps/CalldataChildExtension.lean` | Context/heap extension of actual child-table correspondence. The initial |
| `Backend/MemoryOps/CalldataChildren.lean` | Actual decoded child correspondence at the output heap. Separation is a |
| `Backend/MemoryOps/CalldataNestedChildren.lean` | Compose existing typed child-table observations for reference-containing |
| `Backend/MemoryOps/StructDefaults/*.lean` | G33 finite struct defaults: pair and nested struct `zeroVal`, intrinsic default allocation and compiled `DefaultPlan` runs, with controls ([G33](../feature-work/roadmap-g33-struct-defaults.md)). |
| `Backend/Aggregates/ByteParameters.lean`, `Backend/Aggregates/ByteParameterControls.lean` | G18.04/.05 groundwork: Source `cdArg`/`cdToMem` for a `bytes`/`string` parameter paired with a target state allocating the payload object (single-object relation); no target program or lowering run. |
| `Backend/Aggregates/G18Storage.lean`, `Backend/Aggregates/G18Graph.lean` | G18.02: `Env.pathTy` composition and step typing; `DeclarationGraph` field and storage-path typing ([G18](../feature-work/g18-aggregates.md)). |
| `Backend/Aggregates/G18Memory.lean`, `Backend/Aggregates/G18ReferenceSequence.lean`, `Backend/Aggregates/G18Physical.lean` | G18.03: nested child write with alias observations; rebind then mutate; ordered `uint`-array observations and REVERT endpoint. |
| `Backend/Aggregates/G18{Memory,Distinct}Client.lean`, `Backend/Aggregates/G18{,Distinct,Physical,GraphRoot}Controls.lean` | Fixtures instantiating the consumers; typing, sequencing and wrong-candidate controls. |
| `Backend/Aggregates/G18StorageValues.lean` | Actual Source/IR integer cell relation, derived save availability and disjoint write preservation. |
| `Backend/Aggregates/G18StorageClient.lean` | Inhabited declared Basket array client and composed actual writes with ordered observations. |
| `Backend/Aggregates/G18StorageCellControls.lean` | Populated wrong-output/order/phase, path/slot and width controls for scoped storage consumers. |
| `Backend/Aggregates/G18ScalarMapping.lean` | All-key Source/intrinsic mapping write and published symbolic SLOAD/SSTORE copy consumer. |
| `Backend/Aggregates/G18ScalarMappingControls.lean` | Populated unsigned/signed mapping certificates, complete frame and outcome/alias/width controls. |
| `Backend/Aggregates/G18SourceMapping.lean` | Actual persistent Source read/write phases composed with the captured-key mapping target certificate; static refusal remains distinct. |
| `Backend/Aggregates/G18SourceMappingControls.lean` | Populated actual Env.cellTy client, account postcondition, journal undo, complete Source frame and stale/static controls. |
| `Backend/Aggregates/G18MappingExpression.lean` | Actual resolved Boolean-key integer mapping reference/read/capture/assignment execution, complete success and static empty-revert outcomes. |
| `Backend/Aggregates/G18MappingExpressionControls.lean` | Inhabited Source globals, pipeline/sample baselines, exact low horizons and certificate-derived wrong-output/stale-state controls. |
| `Backend/Aggregates/G18ArrayAccess.lean` | Declared dynamic-array cell typing, actual stored-length/bounds executions and Source-to-intrinsic selected-cell read transport. |
| `Backend/Aggregates/G18ArrayAccessControls.lean` | Populated Basket length/data witness, exact panic branches and missing-length/wrong-location/type-versus-bounds controls. |
| `Backend/MemoryCopies/Interface.lean` | Draft typed memory default/copy certificate signatures (see [memory copies](../feature-work/memory-copies.md)); Source outcomes, finite heap, dynamic length, alias and overlap obligations. |
| `Backend/MemoryCopies/Premises.lean` | Explicit unfinished producer boundaries for allocation panic, aliases and reached location steps; no assumed instances. |
| `Backend/MemoryCopies/InterfaceV2.lean` | Non-vacuous default/copy signatures with concrete fitting allocator witnesses; only the new live-content heap obligation. |
| `Backend/MemoryCopies/InterfaceV2Laws.lean` | Fitting-witness cost bounds, empty-code impossibility and cost-W refutations for both V2 certificates. |
| `Backend/AbiEntry/Interface.lean` | G40 source-boundary obligation signatures only; no runtime, decoder or admission instance (see [ABI entry](../feature-work/abi-entry.md)). |
| `Backend/AbiEntry/CompositionInterface.lean` | Ordered raw entry recursion obligations with actual entries, fuel, head extent and allocation cursor. |
| `Backend/AbiEntry/RejectionInterface.lean` | Conditional rejection-consumer signatures against the existing checked byte-slice runner. |
| `Backend/AbiEntry/WordValidationInterface.lean` | Contracts for emitted primitive word validators in the numeric runner; stack suffix retained. |
| `Backend/AbiEntry/WordValidation.lean` | Actual numeric bytecode for strict unsigned, bool and enum word bounds, with capacity. |
| `Backend/AbiEntry/EntryTransport.lean` | Consumers of the indexed ABI-entry decoder; empty-REVERT classifier for certified entry reverts. |
| `Backend/AbiEntry/RawFreeTransport.lean` | Raw-free entry transport over the existing indexed semantic decoder. |
| `Backend/AbiEntry/EntryComposition.lean` | Structural composition of the indexed entry recursion with exact fuel, cursor and ordered failures. |
| `Backend/AbiEntry/EnumEntry.lean` | Nominal-cardinality consumers of the enum entry decoder. |
| `Backend/AbiEntry/Consumers.lean` | Inhabitants of the rejection and composition interfaces from the entry proofs. |
| `Backend/AbiEntry/Premises.lean`, `Backend/AbiEntry/Premises/CalldataViews.lean`, `Backend/AbiEntry/Premises/CalldataViewExtensions.lean` | Pending G34 overlapping-calldata-view, G35.03 and G24.03 producer premises; no instances. |
| `Backend/TryCall/ProducerInterface.lean` | Typed obligations for checked try-call emitters (see [H8 source model](../feature-work/diamond-try-h8-source-model.md)). |
| `Backend/TryCall/PanicNormalization.lean` | Known-self Panic normalization for the checked try-call specialization. |
| `Backend/TryCall/PanicEmitter.lean` | Checked core emitter for the bounded known-self Panic source. |
| `Backend/TryCall/PanicControls.lean` | Represented positive and negative entries for the same checked emitter. |
| `Backend/FunctionValues/Interface.lean`, `Backend/FunctionValues/Premises.lean` | G42.05 external function value boundary and declared-call premises (see [function values](../feature-work/g42-05-function-values.md)). |
| `Backend/FunctionValues/Representation.lean` | Runtime words reuse the 24-byte source codec. |
| `Backend/FunctionValues/Execution.lean` | Actual `Evm.run` observations for the low-192-bit convention. |
| `Backend/FunctionValues/Inequality.lean` | External-function inequality via actual EQ/ISZERO and the source key. |
| `Backend/FunctionValues/Controls.lean` | Inhabited source/compiled value controls. |
| `Backend/MemoryOps/PhysicalWordFrame.lean`, `Backend/MemoryOps/PhysicalByteJournal.lean` | P6: word cell to 32-byte span; paired word/byte MSTORE; byte journal and REVERT reads ([P6](../feature-work/physical-memory-interface.md)). |
| `Backend/MemoryOps/PhysicalSourceUint.lean`, `Backend/MemoryOps/PhysicalUintWrite.lean`, `Backend/MemoryOps/PhysicalUintDelete.lean`, `Backend/MemoryOps/PhysicalArrayReframe.lean` | `UintArrayAt` Source/intrinsic/word/byte relation; read, write, delete as zero write; reframe cell agreement. |
| `Backend/MemoryOps/PhysicalReferenceStore.lean`, `Backend/MemoryOps/PhysicalPointerFrame.lean` | Reference-array store with scaled-pointer bytes; `PointerFrame`. |
| `Backend/MemoryOps/PhysicalFrameImage.lean`, `Backend/MemoryOps/PhysicalWorldUnwind.lean` | Frame-memory byte image; world journal, reason emitter and local checkpoint unwind. |
| `Backend/MemoryOps/PhysicalReferenceArray.lean` | Typed reference-parent pointer-byte layout and redirection. |
| `Backend/MemoryOps/PhysicalReferenceChild.lean` | Reference parent framing across separated primitive writes. |
| `Backend/MemoryOps/PhysicalLocalDeleteGoal.lean`, `Backend/MemoryOps/Physical{Memory,FrameImage,WorldUnwind}Controls.lean` | Assembly/client target statements with their proofs; concrete controls (`PhysicalMemoryControls` exports the fixture inputs). |
| `Backend/MemoryOps/CalldataRead.lean` | Published decoded calldata objects and typed memory slice reads |
| `Backend/MemoryOps/CalldataSequence.lean` | Option composition of actual immutable decoded transfers. No payload is an |
| `Backend/MemoryOps/CalldataSequenceChildren.lean` | Existing immutable child-table correspondence at actual sequence outputs. |
| `Backend/MemoryOps/CalldataSequenceFixtures.lean` | Concrete decoded primitive fixture tables only; no ABI decoder or Source |
| `Backend/MemoryOps/CalldataSequenceLaws.lean` | Actual decoded-transfer observations and local same-object interval |
| `Backend/MemoryOps/CalldataTransfer.lean` | Actual immutable decoded Boolean array transfer. This consumes the existing |
| `Backend/MemoryOps/CalldataTransport.lean` | Initial element correspondence transports actual immutable decoded reads to |
| `Backend/MemoryOps/CalldataUintTransfer.lean` | Actual immutable decoded uint256 array transfer. This consumes the existing |
| `Backend/MemoryOps/CheckedSnapshot.lean` | Checked bounds around the existing actual-heap captureOverwrite operation. |
| `Backend/MemoryOps/ContextTransport.lean` | Existing locals and slice views across context and heap extension |
| `Backend/MemoryOps/CopyMirrorFrame.lean` | Frame the published recursive typed storage-copy mirror across writes to |
| `Backend/MemoryOps/CopyMirrorSchedule.lean` | Arbitrary finite reached-heap schedules preserve published recursive |
| `Backend/MemoryOps/DisjointOverwrite.lean` | Disjoint overwrite composition on the actual intrinsic heap |
| `Backend/MemoryOps/HeapSnapshot.lean` | Snapshot overwrite adapter over the published intrinsic heap |
| `Backend/MemoryOps/InterstageBuilders.lean` | Actual published multi-object storage/default growth between captures. |
| `Backend/MemoryOps/InterstageCorrespondence.lean` | Existing typed child correspondence across an actual first snapshot, |
| `Backend/MemoryOps/InterstageGrowth.lean` | Growth after an actual first snapshot, before the second capture. |
| `Backend/MemoryOps/IntervalOverwrite.lean` | Captured writes to separated intervals of the same typed object commute. |
| `Backend/MemoryOps/MixedCalldataSequence.lean` | Mixed decoded Boolean/uint transfers compose existing operations only. |
| `Backend/MemoryOps/OverwriteAgreement.lean` | Pointwise agreement with INITIAL contents makes an actual overwrite an |
| `Backend/MemoryOps/OverwriteAgreementExact.lean` | Exact local footprint observations. Actual successful operations provide |
| `Backend/MemoryOps/OverwriteRestoration.lean` | Exact two-write restoration from INITIAL reads. The last write controls its |
| `Backend/MemoryOps/RecaptureRestoration.lean` | Actual memory-to-memory recapture restoration. The second payload comes |
| `Backend/MemoryOps/SequentialSnapshot.lean` | Ordered composition of existing snapshots. The second payload is captured |
| `Backend/MemoryOps/SequentialTransport.lean` | Compose ordered writes/snapshots with real old-footprint growth and child |
| `Backend/MemoryOps/SliceBounds.lean` | Bounds for typed heap slice adapters |
| `Backend/MemoryOps/SliceExtension.lean` | Slice reads across published heap extension |
| `Backend/MemoryOps/Snapshot.lean` | Snapshot and overlap laws for existing typed element lists |
| `Backend/MemoryOps/SnapshotExtension.lean` | Naturality of the actual heap overwrite adapter under preserving growth. |
| `Backend/MemoryOps/SnapshotProvenance.lean` | Backwards index provenance is observation data only. It neither copies |
| `Backend/MemoryOps/SnapshotReferenceSchedules.lean` | Nonprimitive and fixed-array schedule witnesses. Snapshots retain old HRef |
| `Backend/MemoryOps/SnapshotSchedule.lean` | Finite List/Option composition of existing checkedCaptureOverwrite calls. |
| `Backend/MemoryOps/SnapshotScheduleControls.lean` | Runtime schedules and actual intrinsic witnesses. restoreCycles constructs |
| `Backend/MemoryOps/SnapshotScheduleGrowth.lean` | Operation-side finite-schedule growth, consuming published checked-step |
| `Backend/MemoryOps/SourceAlias.lean` | Actual existing Source local assignment and published intrinsic/word memory |
| `Backend/MemoryOps/SourceAssignment.lean` | Supported resolved Source indexed assignment consumes the existing RHS-first |
| `Backend/MemoryOps/SourceDeclaration.lean` | Actual resolved Source default declaration through the published constructor |
| `Backend/MemoryOps/SourceDefault.lean` | Actual published independent Source zero-default construction and existing |
| `Backend/MemoryOps/SourceDelete.lean` | Existing independent Source delete and actual intrinsic memory-address clear. |
| `Backend/MemoryOps/SourceDeleteTarget.lean` | Compose the independent Source primitive delete with the PUBLISHED symbolic |
| `Backend/MemoryOps/SourceIndexedDelete.lean` | Existing resolved Source delete syntax, actual location evaluation and the |
| `Backend/MemoryOps/SourceMemory.lean` | Operation-side observations of the independent published source machine. |
| `Backend/MemoryOps/SourceNestedAssignment.lean` | Actual resolved nested assignment over existing Source syntax, intrinsic |
| `Backend/MemoryOps/SourceNestedDelete.lean` | Existing resolved nested Source delete and published symbolic-word clear. |
| `Backend/MemoryOps/SourceNestedMemory.lean` | INITIAL correspondence of the supported dynamic reference-array -> Boolean |
| `Backend/MemoryOps/SourceNestedMutation.lean` | A selected-child write frame for the existing finite nested observer. |
| `Backend/MemoryOps/SourceNestedSelect.lean` | Actual Source parent indexing followed by local child-reference assignment, |
| `Backend/MemoryOps/SourceReferenceAssignment.lean` | RHS-first resolved parent-element redirection to an existing Boolean |
| `Backend/MemoryOps/SourceReferenceSequence.lean` | Parent redirection followed by deletion through the ACTUAL reached pointer. |
| `Backend/MemoryOps/SourceReferenceWrite.lean` | Existing parent reference slots are redirected to an existing represented |
| `Backend/MemoryOps/SourceSequence.lean` | Actual reached-state composition of published Source statements, intrinsic |
| `Backend/MemoryOps/SourceStructAlias.lean` | Actual local alias rebinding FROM an initially represented struct member. |
| `Backend/MemoryOps/SourceStructAssignment.lean` | Actual resolved named struct-member pointer assignment. Published pointer, |
| `Backend/MemoryOps/SourceStructChild.lean` | Actual named-member-selected Boolean child indexing and mutation. |
| `Backend/MemoryOps/SourceStructDeclaration.lean` | Real context-changing Source default declaration followed by reached named |
| `Backend/MemoryOps/SourceStructDelete.lean` | Actual deletion through the INITIAL named struct's selected Boolean child. |
| `Backend/MemoryOps/SourceStructGrowth.lean` | Paired REAL Source/intrinsic heap allocation for the existing finite named |
| `Backend/MemoryOps/SourceStructMemory.lean` | A finite INITIAL two-field struct correspondence. Source declaration names |
| `Backend/MemoryOps/SourceUintAssignment.lean` | Actual uint256 indexed Source assignment and whole published word program. |
| `Backend/MemoryOps/SourceUintCompound.lean` | A checked numeric update reads the actual reached cell. Existing Source, |
| `Backend/MemoryOps/SourceUintDelete.lean` | Real uint256 primitive deletion, not copying. Actual Source default/unit, |
| `Backend/MemoryOps/SourceUintFixedAlias.lean` | Existing fixed-reference local rebinding, now carrying the INITIAL fixed |
| `Backend/MemoryOps/SourceUintFixedAliasProgram.lean` | Rebinding selects the SAME represented fixed reference, then actual reached |
| `Backend/MemoryOps/SourceUintFixedAssignment.lean` | Actual uint256 indexed Source assignment and whole published word program. |
| `Backend/MemoryOps/SourceUintFixedBumpSequence.lean` | A genuine two-statement Source Items and intrinsic Prog application, not |
| `Backend/MemoryOps/SourceUintFixedCompound.lean` | Whole existing read/binary/write code over genuine fixed Source arrays and |
| `Backend/MemoryOps/SourceUintFixedCompoundSource.lean` | Genuine fixed uint Source compound syntax. The actual old cell is obtained |
| `Backend/MemoryOps/SourceUintFixedDeclaration.lean` | Positive fixed uint Source declaration and the EXISTING typed declaration/ |
| `Backend/MemoryOps/SourceUintFixedDeclareAlias.lean` | Actual fixed declaration then OLD-local rebinding to the NEW root and reached |
| `Backend/MemoryOps/SourceUintFixedDeclareAliasControls.lean` | Typed proof component for SourceUintFixedDeclareAliasControls |
| `Backend/MemoryOps/SourceUintFixedDecrement.lean` | Existing prefix/postfix fixed uint decrement. The independent Source result |
| `Backend/MemoryOps/SourceUintFixedDecrementBounds.lean` | Fixed-array bounds: the actual indexed location |
| `Backend/MemoryOps/SourceUintFixedDecrementBoundsControls.lean` | Fixed-array bounds controls. Populated1,8,1 array, separate9,10,9 child and11,12 |
| `Backend/MemoryOps/SourceUintFixedDecrementLate.lean` | Reached-state fixed-array decrement and checked failure. |
| `Backend/MemoryOps/SourceUintFixedDecrementLateControls.lean` | Reached-state decrement controls. Populated original fixture schema, initial LEFT |
| `Backend/MemoryOps/SourceUintFixedDecrementLateTiming.lean` | Reached-state timeout companion: the actual first prefix succeeds but the second |
| `Backend/MemoryOps/SourceUintFixedDefault.lean` | Genuine fixed Source uint defaults. Existing Data/Heap/typed fixed objects and |
| `Backend/MemoryOps/SourceUintFixedDelete.lean` | Real uint256 primitive deletion, not copying. Actual Source default/unit, |
| `Backend/MemoryOps/SourceUintFixedFuel.lean` | Caller-fuel slack for the actual fixed Source default evaluator. Fuel is |
| `Backend/MemoryOps/SourceUintFixedIncrement.lean` | Existing prefix/postfix fixed uint increment. The independent Source result |
| `Backend/MemoryOps/SourceUintFixedWrite.lean` | Genuine fixed Source element mutation. Existing typed Data, Heap and Source |
| `Backend/MemoryOps/SourceUintMemory.lean` | Existing Source memory uint256 arrays observed against intrinsic typed arrays. |
| `Backend/MemoryOps/SourceUintSequence.lean` | Actual reached-state numeric assignment/deletion sequencing. Existing |
| `Backend/MemoryOps/SourceUintWrite.lean` | Actual numeric Source memSet/writeLoc and intrinsic address updates. |
| `Backend/MemoryOps/SourceWrite.lean` | Independent Source location writes and existing intrinsic singleton copies. |
| `Backend/MemoryOps/CalldataViewPacking.lean` | Bounded v11-memory-operations checkpoint; typed scope and retained premises are in the module. |
| `Backend/MemoryOps/CalldataViewPackingControls.lean` | Bounded v11-memory-operations checkpoint; typed scope and retained premises are in the module. |
| `Backend/MemoryCopies/TraversalControls.lean` | Bounded memory-copies checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryCopies/TraversalFresh.lean` | Bounded memory-copies checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryCopies/TraversalInterface.lean` | Bounded memory-copies checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryOps/SourceCalldataUintDelete.lean` | Actual raw uint copy/bind then reached deletion or bounds rejection; old-object frames. |
| `Backend/MemoryOps/SourceCalldataMixedCopy.lean` | Actual uint copy/bind followed by reached Boolean copy; typed fresh observers and late decode failure. |
| `Backend/MemoryOps/PhysicalReferenceSequence.lean` | Actual parent-pointer redirection and reached primitive child write, dynamic word path and component byte stores. |
| `Backend/MemoryOps/PhysicalReferenceSequenceControls.lean` | Inhabited alias, complete word/byte vector, stale-base and endpoint rejection controls. |
| `Backend/MemoryOps/CalldataViewExtension.lean` | Structural extension of supplied typed views. |
| `Backend/MemoryOps/CalldataViewExtensionControls.lean` | Clients with genuinely noncanonical prior keys; structural view packing only. |
| `Backend/MemoryOps/CalldataViewPacking.lean` | Finite structural packing of supplied coherent typed views into the EXISTING Source.Calldata. |
| `Backend/MemoryOps/CalldataViewPackingControls.lean` | Inhabited structural packing clients. |
| `Backend/MemoryOps/SourceCalldataBinding.lean` | Actual RHS-first Source calldata conversion followed by local reference binding and reached observations. |
| `Backend/MemoryOps/SourceCalldataMutation.lean` | Reached Source mutation after actual raw-input copy/local binding. |
| `Backend/MemoryOps/SourceCalldataUintBinding.lean` | Actual Source numeric copy/local binding and reached read composition. |
| `Backend/MemoryOps/SourceCalldataUintCopy.lean` | Actual independent Source uint256 calldata-to-memory conversion and paired existing intrinsic allocation. |
| `Backend/MemoryOps/SourceCalldataUintCopyControls.lean` | Actual populated uint Source/intrinsic copy clients. |
| `Backend/MemoryOps/SourceCalldataUintMutation.lean` | Actual reached uint mutation after raw-input copy/local binding. |
| `Backend/MemoryOps/SourceCalldataUintTransfer.lean` | One observed typed table object projected from the REAL numeric Source word decoder, then the EXISTING checked transfer. |

| `Backend/MemoryOps/SourceCalldataSlice.lean` | Actual resolved uint calldata slice/conversion: computed shifted offset, ordered bounds and decoder/allocation outcomes. |
| `Backend/MemoryOps/SourceCalldataSliceControls.lean` | Both-pipeline populated slice/copy with checked native allocation, complete old/alias/neighbour frames, exact-end, omitted-end, bounds, timeout and stale-window controls. |

| `Backend/MemoryOps/SourceCalldataBoolSlice.lean` | Actual Boolean calldata slice/conversion with computed shifted decoder and pre-allocation bounds errors. |
| `Backend/MemoryOps/SourceCalldataBoolSliceSequence.lean` | Real Source RItems retain the actual first sliced-copy allocation on a later malformed Boolean decoder error. |
| `Backend/MemoryOps/SourceCalldataBoolSliceControls.lean` | Both-pipeline populated valid/malformed-window clients, complete Source/native alias frames, order/timeout/empty and Option-capacity distinctions. |

| `Backend/MemoryOps/SourceCalldataSliceRead.lean` | Actual one-word calldata indexing through a computed slice, with ordered slice/index/selected-decoder outcomes and unchanged Source state. |
| `Backend/MemoryOps/SourceCalldataSliceReadCopy.lean` | Selected Source reads agree with the read from a separately executed actual checked fresh Boolean copy after computed window-decoder success. |
| `Backend/MemoryOps/SourceCalldataSliceReadControls.lean` | Both-pipeline Bool/uint/max/lazy-versus-eager clients, complete old alias/neighbour data, selected-word failure, empty/index panic and timeout. |

| `Backend/MemoryOps/SourceUintReadAssignment.lean` | Actual RHS-first indexed uint memory read assignment; Source/native/strong Objects frames and allocator transport. |
| `Backend/MemoryOps/SourceUintReadAssignmentControls.lean` | Inhabited computed-RHS distinct/aliased clients, complete twenty-word/Source/native vectors and endpoint/timeout negatives. |

| `Backend/MemoryOps/SourceUintReadSequence.lean` | Reached computed-RHS propagation: actual Source Items/native Prog/full Objects word append, initial bounds and composed allocator/world frames. |

| `Backend/MemoryOps/SourceReferenceRead.lean` | Computed parent-element reference RHS: actual Source/native/published whole pointer write, selected-child derivation, frames and allocator transport. |
| `Backend/MemoryOps/SourceReferenceReadControls.lean` | Inhabited distinct/same-parent/no-op clients, complete five-object/twenty-four-word observations, nested reads and exact bounds/timeout distinctions. |

| `Backend/MemoryOps/SourceReferenceReadSequence.lean` | Computed reference RHS followed by reached nested delete or ordered parent/child bounds rejection; actual Source Items, intrinsic Prog, whole word append and prefix observer/allocator frames. |

| `Backend/MemoryOps/SourceReferenceAliasSequence.lean` | Actual computed reference replacement followed by reached local alias selection; Source Items, intrinsic Prog, full word append and derived observer/local/allocator frames. |

| `Backend/MemoryOps/SourceReferenceAliasDelete.lean` | Computed reference replacement, reached local alias and actual indexed deletion in one Source Items/intrinsic Prog/word append, with derived frames. |

| `Backend/MemoryOps/SourceReferenceAliasReject.lean` | Actual computed replacement and reached local rebinding followed by late indexed-delete rejection; retained prefix observers, Source error globals, intrinsic Prog and full word append. |

| `Backend/MemoryOps/PhysicalByteStore.lean` | Actual MSTORE8 in both byte APIs, disjoint complete numeric-word frames and reached-memory REVERT observations; no abstract-word instruction refinement. |
| `Backend/MemoryOps/PhysicalByteStoreControls.lean` | Inhabited boundary-byte stores, high-word/full-byte observations, truncation/short-stack and overlapping-write frame counterexamples. |

| `Backend/MemoryOps/SourceRhsAssignment.lean` | Actual memory-writing assignment RHS before reached outer location; success/late bounds, one Source expression/statement, native Prog2 and discarded-result word append. |

| `Backend/MemoryOps/SourceRhsValue.lean` | Actual Bool result reload after reached memory-writing RHS/outer assignment, source/native/word result relation, caller/heap/allocator frames and late-failure short-circuit. |

| `Backend/MemoryOps/SourceShortCircuit.lean` | Actual lazy Boolean guard around effectful memory expressions: skipped writes/failures, reached success/error states, and existing word branch execution. |

| `Backend/MemoryOps/PhysicalByteWorldInterface.lean` | Explicit pending static cell-indexed byte-load program contract over real runSlice, conditional initial WordFrame client and current literal MLOAD boundary; no concrete Producer. |
| `Backend/MemoryOps/SourceConditional.lean` | Actual Source and word conditional selection with effectful branches, retained reached states and selected rejection. |

| `Backend/MemoryOps/SourceCalldataBoolSliceNative.lean` | Actual computed Bool slice/decoder classification composed with paired Source and intrinsic allocation; retained old named struct/children/aliases and fresh map/MemOK frames. |

| `Backend/MemoryOps/SourceLocalReferenceDelete.lean` | Actual Source local Bool-array reference deletion paired with native allocating rebind and complete published word code; fresh observer and retained old aliases. |

| `Backend/MemoryOps/SourceLocalReferenceReject.lean` | Actual local-reference allocation/rebinding prefix followed by reached empty-root bounds rejection in Source Items, native Prog and full word append; retained-prefix frames. |

| `Backend/MemoryOps/SourceLocalReferenceOrder.lean` | Actual indexed write then allocating local-reference deletion in Source Items/native Prog/full word append; changed retained aliases and world/allocator frames. |

| `Backend/MemoryOps/SourceMemoryShortCircuit.lean` | Actual initial Bool indexed-write bounds error absorbs arbitrary context-changing Source/native and word continuations; no suffix/allocator premises. |

| `Solidity/Backend/MemoryOps/SourceReferenceGrowth.lean` | Actual paired Source/intrinsic allocation preserves finite reference-parent/Boolean-child observations; no emitted allocator claim. |

| `Solidity/Backend/MemoryOps/SourceReferenceGrowthWrite.lean` | Actual paired allocation then reached parent-slot redirection; derived observers/frames, no emitted allocator. |

| `Solidity/Backend/MemoryOps/SourceReferenceGrowthDelete.lean` | Actual allocation/redirection then nested delete; fresh allocation derives alias separation and old-object frames. |
| `Backend/MemoryCopies/ControlsV2.lean` | Bounded memory-copies checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryCopies/InterfaceV2Roots.lean` | Bounded memory-copies checkpoint; typed scope and retained obligations are stated in the module. |

| `Solidity/Backend/MemoryOps/SourceRawUintDelete.lean` | Published byte-decoder specialization of actual Source Items uint copy/bind/delete, reached bounds failure and old-object frames. |

| `Solidity/Backend/MemoryOps/SourceGuardedUintDelete.lean` | Actual cdTail guard then Source Items uint copy/delete; byte-derived success, early refusal and late bounds failure with explicit initial view alignment. |

| `Solidity/Backend/MemoryOps/SourceUintSliceNative.lean` | Actual byte-derived uint slice expression and guarded paired Source/native allocation with old-object/map frames. |

| `Solidity/Backend/MemoryOps/SourceUintSliceBinding.lean` | Actual uint slice-result local binding and reached successful/rejecting Items deletion with native allocation/write and old-object frames. |

| `Solidity/Backend/MemoryOps/SourceUintSliceCompound.lean` | Byte-derived slice binding followed by actual reached compound addition or checked overflow, with Items execution and heap/world frames. |

| `Solidity/Backend/MemoryOps/SourceUintSliceCompoundBounds.lean` | Dynamic Source compound index rejection after actual slice binding, retained Items prefix, native read/write bounds and low-horizon laws. |

| `Solidity/Backend/MemoryOps/SourceUintSliceCompoundRead.lean` | Actual slice binding, compound update and changed-cell scalar read in one Source Items program, with alias-safe locals, frames and triple-error composition. |

| `Solidity/Backend/MemoryOps/SourceUintAlias.lean` | Dynamic uint contents-aware Source/native/word aliasing with strong Objects/allocator frames and reached different-capacity read rejection. |

| `Solidity/Backend/MemoryOps/SourceUintAliasWrite.lean` | Reached dynamic uint alias-to-write Source Items/native Prog/whole strong word append, preserving Objects and allocator frames. |

| `Solidity/Backend/MemoryOps/SourceUintAliasDelete.lean` | Actual reached dynamic uint alias/delete Source Items/native Prog/whole word success and bounds rejection, strong prefix/final frames. |

| `Solidity/Backend/MemoryOps/SourceUintAliasWriteDelete.lean` | Strong numeric delete bridge and actual reached alias/write/same-index delete Source Items, intrinsic Prog and complete word append with derived frames. |
| `Backend/MemoryCopies/SourceInterface.lean` | Bounded memory-copies checkpoint; typed scope and retained obligations are stated in the module. |

| `Solidity/Backend/MemoryOps/SourceUintAliasWriteRead.lean` | Contents-derived strong scalar read and actual alias/write/read-into-local Source Items/native Prog/full word append, including result/index aliasing. |

| `Solidity/Backend/MemoryOps/SourceUintAliasReadReject.lean` | Actual four-statement alias/write/read/index-rejection composition with retained successful prefix. |

| `Solidity/Backend/MemoryOps/PhysicalByteMaterialize.lean` | Existing arbitrary emitted byte stores across Environment and failure slices, live REVERT and disjoint full-word frames. |
| `Solidity/Backend/MemoryOps/PhysicalByteMaterializeControls.lean` | Populated full-byte/word vectors, actual overlapping order, empty and unsupported boundaries. |

| `Solidity/Backend/MemoryOps/PhysicalByteStack.lean` | Existing checked stack guard for arbitrary emitted byte materialization; transient peak and reached live REVERT. |

| `Solidity/Backend/MemoryOps/SourceRawBoolCopy.lean` | Raw-byte-derived Boolean decode/copy success, ordered first-invalid failure and Source frames. |
| `Solidity/Backend/MemoryOps/SourceRawBoolCopyControls.lean` | Populated objects/aliases, nonzero raw offset, late invalid Boolean and actual padding/empty controls. |

| `Solidity/Backend/MemoryOps/SourceRawBoolEntry.lean` | Actual dynamic entry guard composed with raw Boolean copy under selector/frame binding; ordered refusal and success laws. |

| `Solidity/Backend/MemoryOps/SourceRawBoolSliceSequence.lean` | Initial raw-word facts derive both decoder phases of the existing linked Bool slice Items program, retaining its actual first allocation. |

| `Solidity/Backend/MemoryOps/PhysicalByteStackExact.lean` | Exact nonempty materializer transient/suffix guard and checked-run equations on reached byte memory, with universal caller-stack REVERT classification. |

| `Solidity/Backend/MemoryOps/PhysicalPointerMaterialize.lean` | Actual byte materialization preserves independent scaled-pointer, typed-parent and numeric-word footprints under local interval separation. |

| `Solidity/Backend/MemoryOps/PhysicalPointerWorldUnwind.lean` | Derives a mixed typed-pointer/numeric checkpoint after actual byte materialization, with reached Source world prefix, live ABI reason emission and separate explicit local restoration. |
| `Backend/MemoryOps/PhysicalByteStore.lean` | Bounded v11-memory-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryOps/PhysicalByteStoreControls.lean` | Bounded v11-memory-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryOps/SourceRawBoolCopy.lean` | Bounded v11-memory-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryOps/SourceRawBoolCopyControls.lean` | Bounded v11-memory-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryOps/SourceRawBoolEntry.lean` | Bounded v11-memory-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryCopies/NestedDefaultInterface.lean` | Bounded memory-copies checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryCopies/RuntimeArrayInterface.lean` | Bounded memory-copies checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryCopies/SelectedArrayDefaultInterface.lean` | Bounded memory-copies checkpoint; typed scope and retained obligations are stated in the module. |

| `Solidity/Backend/MemoryOps/PhysicalFixedChildWrite.lean` | Resolved fixed Source assignment/statement and initial-MemOK transport paired with typed updates and terminal word/byte stores, deriving headerless parent/state frames. |
| `Solidity/Backend/MemoryOps/PhysicalFixedChildControls.lean` | Inhabited shared fixed-child parent, nonempty protected neighbour, complete represented vectors, Source endpoint and wrong-header negatives. |

| `Solidity/Backend/MemoryOps/PhysicalFixedChildProgram.lean` | Actual strong whole-word fixed assignment joined to initial physical parent/value bytes, with derived local separation, MemOK and supplied allocator transport. |

| `Solidity/Backend/MemoryOps/SourceUintFixedRefsMemory.lean` | Initial genuine fixed-uint-child reference-parent observer with derived selected values and actual nested Source reads/bounds. |
| `Solidity/Backend/MemoryOps/SourceUintFixedRefsControls.lean` | Inhabited repeated/distinct fixed children, complete Source observations, actual whole-word success/late-revert tables, strong allocator/stack frames and bounds/timeout/type/empty-parent controls. |

| `Solidity/Backend/MemoryOps/SourceUintFixedRefsWrite.lean` | Actual fixed-child nested Source assignment, derived reached reference-parent observer, MemOK and precise alias/address/world frames under local selected-footprint separation. |

| `Solidity/Backend/MemoryOps/SourceUintFixedRefsDelete.lean` | Actual nested fixed-child primitive deletion and initial-to-reached write/delete Source Items composition with MemOK and object/address/world frames. |

| `Solidity/Backend/MemoryOps/SourceUintFixedRefsTarget.lean` | Actual nested fixed-child Source/intrinsic/whole symbolic-word assignment joined through the published Objects pointer/store certificate, with strong representation, allocator and source frames. |

| `Solidity/Backend/MemoryOps/SourceUintFixedRefsBounds.lean` | Actual nested fixed-child Source index panic/state retention and intrinsic/whole-word revert from initial alignment and strong Objects representation. |

| `Solidity/Backend/MemoryOps/SourceUintFixedRefsLate.lean` | Actual nested successful Source/intrinsic/word prefix followed by reached bounds error in Source Items, intrinsic Prog and complete symbolic word append, with explicit prefix frames. |

| `Solidity/Backend/MemoryOps/SourceUintFixedRefsDeleteTarget.lean` | Actual nested uint delete word bridge and Source Items/intrinsic Prog/whole-word write-delete composition with derived strong representation, stack and allocator frames. |

| `Solidity/Backend/MemoryOps/SourceUintFixedRefsExact.lean` | Exact actual nested fixed-child store machine effect from initial typed value/path/bounds and published certificates, enabling complete prefix/final raw word tables. |

| `Solidity/Backend/MemoryOps/PhysicalNestedFixedWrite.lean` | Actual nested whole-word store joined to terminal byte MSTORE and live REVERT bytes, with initial-derived numeric and scaled-pointer footprints; byte-load prefix remains open. |
| `Backend/MemoryCopies/CheckedDefaultInterface.lean` | Bounded memory-copies checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryCopies/NestedDefaults.lean` | Bounded memory-copies checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryOps/PhysicalByteMaterialize.lean` | Bounded v11-memory-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryOps/PhysicalByteMaterializeControls.lean` | Bounded v11-memory-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryOps/PhysicalByteStack.lean` | Bounded v11-memory-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryOps/PhysicalByteStackExact.lean` | Bounded v11-memory-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryOps/SourceCalldataBoolSlice.lean` | Actual resolved calldata slicing followed by the existing Boolean conversion. |
| `Backend/MemoryOps/SourceCalldataBoolSliceControls.lean` | Actual Boolean calldata views select or exclude a malformed word. |
| `Backend/MemoryOps/SourceCalldataBoolSliceSequence.lean` | A real two-statement Source program, with an actual sliced first copy and a later malformed Boolean decoder. |
| `Backend/MemoryOps/SourceRawBoolSliceSequence.lean` | Discharge the existing two-statement slice program's decoder premises from actual raw words. |
| `Backend/MemoryCopies/PublishedStorage.lean` | Exact fields of the published storage endpoint discharge the existing local execution premise. |
| `Backend/MemoryCopies/PublishedStorageInterface.lean` | Consume the published reached-storage endpoint at the unchanged local composition boundary. |
| `Backend/MemoryCopies/CheckedDefault.lean` | Bounded memory-copies checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryCopies/CheckedReferenceInterface.lean` | memory-copies interface only: capacity guard and checked-reference certificate statement; the certificate is not inhabited here. |
| `Backend/MemoryCopies/HeapContents.lean` | Bounded memory-copies checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryCopies/HeapContentsInterface.lean` | Bounded memory-copies checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryCopies/SingletonCopyInterface.lean` | Bounded memory-copies checkpoint; typed scope and retained obligations are stated in the module. |

| `Solidity/Backend/MemoryOps/PhysicalByteStoreSequence.lean` | Actual prepared two-MSTORE Environment slice with initial-derived numeric/pointer intermediate and final frames, same-cell overwrite support and live REVERT observation. |

| `Backend/MemoryOps/PhysicalByteOverwrite.lean` | Actual two-byte-store reached REVERT payload, arbitrary overlap, complete read updates, disjoint represented-word frame and short-stack prefix failure. |
| `Backend/MemoryCopies/SourceControls.lean` | Inhabited Source certificates with populated storage-copy observations, default/timeout controls and size-boundary witnesses. |
| `Backend/MemoryCopies/SourceSize.lean` | Derives new-array oversized-length panic from evaluation, conversion and size hypotheses. |
| `Backend/MemoryCopies/SourceFramesInterface.lean` | Exact Source allocation-frame obligations for all default and storage-load traversal families, including halted runs. |
| `Backend/MemoryCopies/SourceFramesCore.lean` | Source allocation-frame reflexivity/transitivity and bind/read/allocation preservation over the existing Hoare rules. |
| `Backend/MemoryCopies/SourceDefaultFrames.lean` | Generic allocation-frame proofs for all four Source default traversals and exact success-or-Halt outcome certificates. |
| `Backend/MemoryCopies/SourceStorageFrames.lean` | Generic allocation-frame proofs for all five Source storage-load traversals and exact outcome certificates. |
| `Backend/MemoryCopies/SourceRootCopies.lean` | Derives a fresh-parent Source copy certificate from an actual successful load, preserving old objects and nonheap state. |
| `Backend/MemoryCopies/SourceFramesControls.lean` | Declared nested bytes-array copy, fixed reference-array default and partial-timeout controls with retained child allocation. |
| `Backend/MemoryCopies/SourceSizeInputs.lean` | Additive evaluation/conversion/oversize inputs; preserves the published panic premise and failure field. |
| `Backend/MemoryCopies/HeapContentsControls.lean` | Populated nested 2/0/64-length children, fresh parent, struct/fixed holders and wrong-live-value/shadow controls. |
| `Backend/MemoryCopies/DeepCopyContents.lean` | Inhabited fresh snapshot-copy heap certificate and initial live contents after actual old-object overlap schedules, with alias/empty/refusal controls. |
| `Backend/MemoryCopies/AllocationPanicInterface.lean` | Explicit Source allocation-panic state and byte-exact emitted terminal-slice obligation; no size-selector premise hidden. |
| `Backend/MemoryCopies/AllocationPanic.lean` | Derived oversized Source failure joined to reused byte-exact Panic(0x41) emission, packet framing and wrong-result/timeout/zero-length controls. |
| `Backend/MemoryCopies/NestedDefaultControls.lean` | Populated represented inputs with actual selected-code root/cursor/old-word observations and empty-code/wrong-cursor controls. |
| `Backend/MemoryCopies/RuntimeArrays.lean` | Production-selected runtime reference-array loop and scoped declaration correctness, complete parent demand and size-independent code. |
| `Backend/MemoryCopies/RuntimeArrayControls.lean` | Actual populated runtime lengths0/2/64, empty-any-child and same-code controls, scoped declaration execution and wrong-cursor rejection. |
| `Backend/MemoryCopies/AliasBindingInterface.lean` | Actual pointer-compiler selection and emitted alias rebinding success/refusal with allocator framing. |
| `Backend/MemoryCopies/AliasBinding.lean` | Actual selected pointer compiler followed by alias-local store, deriving exact source/target success or bounds refusal. |
| `Backend/MemoryCopies/AliasBindingControls.lean` | Populated indexed-alias source/target observations, bounds refusal and fresh-pointer/empty-code negative controls. |
| `Backend/MemoryCopies/RuntimeRebindInterface.lean` | Allocating runtime-array rebind outcome with exact scoped/target execution and old-object versus fresh-root separation. |
| `Backend/MemoryCopies/RuntimeRebind.lean` | Existing allocating runtime rebind execution plus universal old-object preservation and fresh-root distinction. |
| `Backend/MemoryCopies/RuntimeRebindControls.lean` | Actual declaration-then-rebind composition over populated ownership, retained old parent and empty/long/wrong-cursor/skipped-code controls. |
| `Backend/MemoryCopies/SourceLeafInterface.lean` | Proved Source leaf-constructor and arbitrary-length reference-element default traversal obligations with exact child addresses. |
| `Backend/MemoryCopies/SourceLeafArrays.lean` | Proved bytes/string/empty-dynamic Source leaf defaults, arbitrary-length child traversal with exact addresses and fresh fixed-parent certificate. |
| `Backend/MemoryCopies/SourceLeafControls.lean` | Populated empty/64 bytes arrays, string and nested dynamic children, partial timeout and wrong-parent controls. |
| `Backend/MemoryCopies/SourceConstructionInterface.lean` | Existing Source default success certificates with exact object counts, sufficient horizons and composable child traversal obligations. |
| `Backend/MemoryCopies/SourceConstruction.lean` | Proved Source leaf lift and fixed-array closure with recursive exact object counts, sufficient horizons, parent-last identity and full state framing. |
| `Backend/MemoryCopies/SourceConstructionControls.lean` | Actual nested bytes/string/dynamic defaults, unused large child under empty parent, populated-state frame and wrong-count control. |
| `Backend/MemoryCopies/SourceFieldsInterface.lean` | Actual Source primitive/reference value and heterogeneous field default construction obligations, indexed by existing types and layout. |
| `Backend/MemoryCopies/SourceFields.lean` | Actual primitive/reference Source defaults, heterogeneous field composition and layout-indexed struct construction with exact counts and framing. |
| `Backend/MemoryCopies/SourceFieldsControls.lean` | Declared mixed bytes-array/string struct and dynamically self-referential struct defaults, child contents, partial timeout and wrong-root controls. |
| `Backend/MemoryCopies/SourceBytesInterface.lean` | Actual typed persistent Source length/payload cell inputs for byte traversal, without aggregate-load or physical-layout assumptions. |
| `Backend/MemoryCopies/SourceBytes.lean` | Actual arbitrary-payload Source byte traversal, length/load derivation from typed stored cells and fresh-root copy certificate. |
| `Backend/MemoryCopies/SourceBytesControls.lean` | Declared populated persistent bytes storage, generic fixture-cell read proof, 0/2/64 copies, old/nonheap frame, wrong payload and horizon refusal. |
| `Backend/MemoryCopies/SourceStringsInterface.lean` | Complete Source string-copy family over actual persistent typed length and byte cells, reusing the byte-reader boundary. |
| `Backend/MemoryCopies/SourceStrings.lean` | Actual Source string payload load and complete fresh-root copy family through the proved byte reader and existing allocator. |
| `Backend/MemoryCopies/SourceStringsControls.lean` | Separately declared populated/empty string copies, distinct byte order, old/nonheap frame, reversal rejection and horizon refusal. |
| `Backend/MemoryCopies/SourceNestedBytesInterface.lean` | Actual persistent child-cell inputs and nested Source byte traversal with exact fresh identities and retained payloads. |
| `Backend/MemoryCopies/SourceNestedBytes.lean` | Static cell transport through allocations, actual populated byte-child traversal with sequential fresh IDs and retained payloads, and complete dynamic parent copy. |
| `Backend/MemoryCopies/SourceNestedBytesControls.lean` | Declared populated/empty bytes arrays, exact final child contents, 64-child growth, wrong-root rejection and horizon refusal. |
| `Backend/MemoryCopies/SourceStoredFieldsInterface.lean` | Proved heterogeneous Source loadElem/loadFields families stable through sibling memory allocations, with exact Source object counts. |
| `Backend/MemoryCopies/SourceStoredFields.lean` | Actual primitive/bytes/string load families, heterogeneous storage field traversal and layout-indexed fresh Source struct copying with exact counts. |
| `Backend/MemoryCopies/SourceStoredFieldsControls.lean` | Declared mixed struct storage copy with scalar42, distinct bytes/string contents, fresh child/parent identities, old/nonheap state and refusal controls. |
| `Backend/MemoryCopies/SourceStoredReferencesInterface.lean` | Reference closure obligations for existing Source stored-value certificates: nested structs, empty dynamic arrays and byte arrays with exact counts/horizons. |
| `Backend/MemoryCopies/SourceStoredReferences.lean` | Proved closure of existing Source stored-value certificates for nested structs, empty dynamic arrays and byte arrays. |
| `Backend/MemoryCopies/SourceStoredReferencesControls.lean` | Declared nested struct identities/payloads, empty recursive child arrays, old-state framing and negative Source controls. |
| `Backend/MemoryCopies/SourceStoredElementsInterface.lean` | Existing Source homogeneous element traversal and fixed/dynamic array closure obligations with exact object counts. |
| `Backend/MemoryCopies/SourceStoredElements.lean` | Generic existing Source element traversal and fixed/dynamic stored-value closure with exact allocation frames and counts. |
| `Backend/MemoryCopies/SourceStoredElementsControls.lean` | Populated recursive Node children, fixed scalar payload order, empty traversal, frame and negative Source controls. |
| `Backend/MemoryCopies/TraversalFootprintInterface.lean` | Exact intrinsic copy allocation-count, parent-last identity and sequential subtree separation obligations. |
| `Backend/MemoryCopies/TraversalFootprint.lean` | Live intrinsic object measures and exact copy growth, parent-last, positive footprint and pair root-boundary proofs. |
| `Backend/MemoryCopies/TraversalFootprintControls.lean` | Nested duplicate subtree identities/contents, old-object retention, shadows, empty and64-branch footprint controls. |
| `Backend/MemoryCopies/SelectedArrayDefaults.lean` | Lifts existing production selection through fixed wrappers and reuses runtime reference-array/scoped declaration correctness for supported roots. |
| `Backend/MemoryCopies/SelectedArrayDefaultControls.lean` | Emitted arrays of structs/fixed structs at0/2/64, whole-parent feasibility, nested default identities and actual scoped declaration controls. |
| `Backend/MemoryCopies/SourceCopyHorizonInterface.lean` | Exact non-timeout result/reached-state preservation obligations under additional Source storage-copy traversal fuel. |
| `Backend/MemoryCopies/SourceCopyHorizon.lean` | Generic exact non-timeout result/state extension for all existing Source copy traversals via bind and mutual fuel descent. |
| `Backend/MemoryCopies/SourceCopyHorizonControls.lean` | Nested and64-byte stability, mapping refusal retention, partially allocated timeout/recovery and old-state controls. |
| `Backend/MemoryCopies/SourceDefaultHorizonInterface.lean` | Exact non-timeout default traversal observation/state preservation under additional interpreter fuel. |
| `Backend/MemoryCopies/SourceDefaultHorizon.lean` | Generic default traversal fuel extension and exact canonical results for existing reference/value/field construction certificates. |
| `Backend/MemoryCopies/SourceDefaultHorizonControls.lean` | Guarded recursive defaults, fixed bytes/string children, scalar/empty/64-child stability, refusal and partial-timeout controls. |
| `Backend/MemoryCopies/SourceStoredFreshInterface.lean` | Fresh parent-last reference certificates and exact distinct repeated Source storage-copy obligations. |
| `Backend/MemoryCopies/SourceStoredFresh.lean` | Actual load success inversion, positive parent-last reference copies, distinct repeated copies, retained first state and canonical traversal laws. |
| `Backend/MemoryCopies/SourceStoredFreshControls.lean` | Populated/empty/64-child repeated struct copies, retained payloads/lengths, exact horizons, partial second timeout and shared-root rejection. |
| `Backend/MemoryCopies/CopyPathInterface.lean` | Existing typed Path observations below copied heaps: full live contents and fresh allocation-range reference bounds. |
| `Backend/MemoryCopies/CopyPaths.lean` | Live typed-path contents and absence, fresh descendant bounds, preserving-growth transport and cross-copy reference separation. |
| `Backend/MemoryCopies/CopyPathControls.lean` | Nested/fixed/struct and empty/64-child path observations, shadow/overrun rejection and distinct descendant controls. |
| `Backend/MemoryCopies/SnapshotPathInterface.lean` | Exact typed snapshot-path contents and reference bounds across successful schedules and reached failure prefixes. |
| `Backend/MemoryCopies/SnapshotPaths.lean` | Generic all-path snapshot contents/bounds after actual capture schedules and reached failures, absence and old-reference separation. |
| `Backend/MemoryCopies/SnapshotPathControls.lean` | Nested alias/deep-copy overlap in both directions, retained failure-prefix effects, empty paths and a 65-step schedule. |
| `Backend/MemoryCopies/RuntimeGrowthInterface.lean` | Existing allocator-growth relation for actual emitted runtime-default statements, with represented fitting inputs. |
| `Backend/MemoryCopies/RuntimeGrowth.lean` | Complete allocator cursor uniqueness, reached-to-growth proof, actual emitted runtime declaration/rebind growth and checked next-input transport. |
| `Backend/MemoryCopies/RuntimeGrowthControls.lean` | Populated nested default growth, checked two-statement composition, empty/64 replacements and wrong-growth/room/skipped-code controls. |
| `Backend/MemoryCopies/DefaultSelectionInterface.lean` | Actual existing statement-compiler selection for supported default roots, with availability and capacity kept separate. |
| `Backend/MemoryCopies/DefaultSelection.lean` | Actual statement-compiler support for selected default roots and wrappers, exact allocation cost and checked emitted success with growth. |
| `Backend/MemoryCopies/DefaultSelectionControls.lean` | Actual empty/nested/fixed64/primitive-struct default compiler choices and executions, with unsupported shape and wrong/skipped-code controls. |
| `Backend/MemoryCopies/SingletonCopy.lean` | Populated resolved singleton array emission, actual source heap identity, complete allocator preservation and V2/root-gap certificate construction. |
| `Backend/MemoryCopies/SingletonCopyControls.lean` | Nonzero uint/Boolean payloads, dynamic length, fresh repeated copies, reserved gaps, old-data framing and capacity/code negative controls. |
| `Backend/MemoryCopies/LoadedSingletonInterface.lean` | Existing primitive-expression compiler load followed by populated singleton allocation, with explicit successful/refused source evaluations. |
| `Backend/MemoryCopies/LoadedSingleton.lean` | Existing expression-load simulation feeds singleton copy, exact storage-copy RHS/declaration equations, emitted declaration and checked bounds refusal. |
| `Backend/MemoryCopies/LoadedSingletonControls.lean` | Actual represented storage array, arbitrary uint payloads and identical code for11/23, emitted SLOAD, complete declaration observations and bounds-revert controls. |
| `Backend/MemoryCopies/CanonicalSingletonInterface.lean` | Canonical existing index-zero load from the copied storage path, with path-derived evaluation/support and declaration obligations. |
| `Backend/MemoryCopies/CanonicalSingleton.lean` | Path-derived compiler support/evaluation, canonical storage-copy declaration and exact source/target failed-path propagation. |
| `Backend/MemoryCopies/CanonicalSingletonControls.lean` | Represented nested dynamic storage matrix, canonical singleton-leaf copying for arbitrary payloads and invalid outer-index source/target refusal. |
| `Backend/MemoryCopies/CanonicalRebindInterface.lean` | Canonical singleton storage-copy rebinding with complete allocator, old-object preservation and strict fresh identity. |
| `Backend/MemoryCopies/CanonicalRebind.lean` | Actual canonical storage-copy local rebind, complete reached ownership, old-object preservation, strict freshness and source/target refusal. |
| `Backend/MemoryCopies/CanonicalRebindControls.lean` | Two populated old aliases, arbitrary copied uint, preserved other alias, actual alias-versus-copy observations and failed-path controls. |
| `Backend/MemoryCopies/PrimitiveArrayInterface.lean` | Arbitrary finite populated primitive-array resolved-value copy using existing allocator/stores, typed word relation and nonvacuous V2/root-gap certificates. |
| `Backend/MemoryCopies/PrimitiveArray.lean` | Arbitrary finite primitive payload initialization through existing stores/reservation/adoption, exact source allocation, full allocator and V2/root-gap certificates. |
| `Backend/MemoryCopies/PrimitiveArrayControls.lean` | Inhabited fitting uint-list copies, empty/pair/64-element observations, exact lengths/live contents, old payload preservation and negative controls. |
| `Backend/MemoryCopies/LoadedArrayInterface.lean` | Existing expression loads followed by finite populated array initialization, with explicit source evaluation inputs and full reached allocator contract. |
| `Backend/MemoryCopies/LoadedArray.lean` | Existing expression load simulation, stack-fed finite array stores, complete allocator transport, actual storage-copy declaration and failed-load companion. |
| `Backend/MemoryCopies/LoadedArrayControls.lean` | Represented storage pair reads for arbitrary distinct payloads, empty and64 replicated-read copies, source linkage and failed-load/negative controls. |
| `Backend/MemoryCopies/CanonicalArrayInterface.lean` | Copied-path selection of all finite primitive index loads, checked empty-path prefix and actual declaration/refusal certificates. |
| `Backend/MemoryCopies/CanonicalArray.lean` | Derive all finite index reads from actual copied storage lookup, construct load inputs, guard empty paths and prove full declarations/refusals. |
| `Backend/MemoryCopies/CanonicalArrayControls.lean` | Nested storage paths copying arbitrary finite uint payloads, distinct64-element observations, empty success and invalid empty-path refusal. |
| `Backend/MemoryCopies/PublishedStorageControls.lean` | Actual represented memory-array copy followed by published scalar SSTORE, reached allocator preservation and skipped-store rejection. |
| `Backend/MemoryCopies/RuntimeStorageArrayInterface.lean` | Runtime storage-header/word loop using existing controller and allocator, with actual typed source representation and full reached allocator contract. |
| `Backend/MemoryCopies/RuntimeStorageArray.lean` | Constant storage-header-driven SLOAD/MSTORE loop, finite termination witness, typed source-word extraction and complete allocator/root-gap simulation. |
| `Backend/MemoryCopies/RuntimeStorageArrayControls.lean` | Identical runtime code for actual lengths0/2/64 with distinct data on a populated old heap, read-only store/frame, freshness and negative controls. |
| `Backend/MemoryCopies/RuntimePathArrayInterface.lean` | Existing storage-path compilation feeding runtime array copying, actual declaration/rebinding with full ownership and failed-path certificates. |
| `Backend/MemoryCopies/RuntimePathArray.lean` | Actual checked path simulation feeding runtime array copying, full declaration/rebinding ownership and source/target failed-path propagation. |
| `Backend/MemoryCopies/RuntimePathArrayControls.lean` | Runtime nested-path declarations/rebindings with two old aliases, distinct empty/pair/64-element data, source alias preservation and invalid-empty controls. |
| `Backend/MemoryCopies/PrimitiveArrayLiveInterface.lean` | Live primitive-array normalization certificate, including arbitrary storage shadows. |
| `Backend/MemoryCopies/PrimitiveArrayLive.lean` | Intrinsic live-array bound, copy/representation normalization and actual runtime-copy transport. |
| `Backend/MemoryCopies/PrimitiveArrayLiveControls.lean` | Arbitrary shadows, empty/long certificates and retained-source-slot runtime controls. |
| `Backend/MemoryCopies/RuntimeLiveArrayInterface.lean` | Actual-value path declaration/rebinding certificates for arbitrary primitive arrays and storage shadows. |
| `Backend/MemoryCopies/RuntimeLiveArray.lean` | Actual-value source and runtime path declaration/rebinding proofs, preserving ownership and old aliases. |
| `Backend/MemoryCopies/RuntimeLiveArrayControls.lean` | Shadow-bearing empty/pair/64 path bindings, retained storage, aliases, invalid paths and extra-tail controls. |
| `Backend/MemoryCopies/RuntimeMemoryArrayInterface.lean` | Runtime primitive memory-array deep-copy code and full allocator/identity certificate. |
| `Backend/MemoryCopies/RuntimeMemoryArray.lean` | Actual runtime header/payload loop deep copying primitive memory arrays with ownership-derived separation. |
| `Backend/MemoryCopies/RuntimeMemoryArrayControls.lean` | Populated/empty/64-element runtime deep-copy controls preserving old aliases and rejecting shallow results. |
| `Backend/MemoryCopies/MemoryPathCopyInterface.lean` | Existing selected-pointer contracts for deep-copy execution/refusal and binding a fresh primitive array. |
| `Backend/MemoryCopies/MemoryPathCopy.lean` | Actual selected-pointer copy/refusal and fresh binding with complete state/allocator transport. |
| `Backend/MemoryCopies/MemoryPathCopyControls.lean` | Local empty/pair/64 and indexed copy controls, Source alias distinction, preserved aliases and path refusal. |
| `Backend/MemoryCopies/FixedMemoryCopyInterface.lean` | Headerless fixed primitive memory-copy code and complete allocator/freshness contract. |
| `Backend/MemoryCopies/FixedMemoryCopy.lean` | Actual headerless fixed primitive memory-copy execution and complete allocator adoption. |
| `Backend/MemoryCopies/FixedMemoryCopyControls.lean` | Fixed empty/pair/64 payload copies, old pointer preservation and header/shallow/empty-reservation negatives. |
| `Backend/MemoryCopies/FixedPathCopyInterface.lean` | Selected-pointer fixed-array fresh copy/binding contracts with headerless layout and refusal. |
| `Backend/MemoryCopies/FixedPathCopy.lean` | Actual selected fixed-path copy/refusal and fresh binding with complete state/allocator transport. |
| `Backend/MemoryCopies/FixedPathCopyControls.lean` | Fixed local empty/pair/64 and indexed-child bindings, alias distinction, header/shallow negatives and path refusal. |
| `Backend/MemoryCopies/FixedStorageCopyInterface.lean` | Headerless fixed storage-to-memory runtime-copy certificate with complete allocator and explicit room. |
| `Backend/MemoryCopies/FixedStorageCopy.lean` | Runtime inline storage reads, fixed-object allocator transport and all-value normalization. |
| `Backend/MemoryCopies/FixedStorageCopyControls.lean` | Populated empty, pair and long fixed storage-copy witnesses and negative header/payload controls. |
| `Backend/MemoryCopies/FixedStoragePathInterface.lean` | Actual fixed storage-path copying and Source declaration/rebinding contracts. |
| `Backend/MemoryCopies/FixedStoragePath.lean` | Actual fixed storage-path Source/target declaration, rebinding and refusal proofs. |
| `Backend/MemoryCopies/FixedStoragePathControls.lean` | Nested fixed-child empty/pair/64 bindings, old aliases, Source execution and invalid-path controls. |
| `Backend/MemoryCopies/ForwardOverlapInterface.lean` | Runtime forward-overlap word-copy and checked snapshot-model contracts. |
| `Backend/MemoryCopies/ForwardOverlap.lean` | Shared forward-loop execution, unread-source invariant and V11 checked snapshot-model agreement. |
| `Backend/MemoryCopies/ForwardOverlapControls.lean` | Actual left/self/empty/long overlap executions, boundary cells and rightward corruption counterexample. |
| `Backend/MemoryCopies/RangeOverlapInterface.lean` | Descending and runtime-direction-selected word-copy contracts for both overlap directions. |
| `Backend/MemoryCopies/RangeOverlap.lean` | Descending invariant and runtime direction selection with actual snapshot and checked-list agreement. |
| `Backend/MemoryCopies/RangeOverlapControls.lean` | Both overlap directions, repaired corruption, self/empty/64-word/disjoint copies and endpoint controls. |
| `Backend/MemoryCopies/TypedCaptureInterface.lean` | Typed captureOverwrite runtime-copy contract with complete allocator and frame preservation. |
| `Backend/MemoryCopies/TypedCapture.lean` | Actual captured-array execution with derived capacity and complete heap/allocator transport. |
| `Backend/MemoryCopies/TypedCaptureControls.lean` | Primitive overlaps, dynamic cross-object writes, shallow reference identities, alias/frame and negative controls. |
| `Backend/MemoryCopies/CheckedCaptureInterface.lean` | Guarded typed capture success/refusal contracts using actual dynamic headers and fixed lengths. |
| `Backend/MemoryCopies/CheckedCapture.lean` | Actual checked typed-capture guards, allocator-derived bounds, success and refusal execution. |
| `Backend/MemoryCopies/CheckedCaptureControls.lean` | Inhabited overlap/reference/dynamic execution and bounds refusal controls. |
| `Backend/MemoryCopies/CheckedMemoryArrayInterface.lean` | Runtime capacity guard and total fresh primitive-array copy contract. |
| `Backend/MemoryCopies/CheckedMemoryArray.lean` | Actual loaded-capacity guard and total fresh primitive-array copy execution. |
| `Backend/MemoryCopies/CheckedMemoryArrayControls.lean` | Populated/empty/long copies, inhabited saturation refusals and last-fitting capacity controls. |
| `Backend/MemoryCopies/CheckedDefaultControls.lean` | Inhabited nested defaults, impossible-capacity refusal and unused huge child controls. |
| `Backend/MemoryCopies/CheckedReference.lean` | Actual division-based full-demand guard and total reference-array default execution. |
| `Backend/MemoryCopies/CheckedReferenceControls.lean` | Nested runtime defaults, unused oversized children and inhabited quotient-boundary controls. |
| `Backend/MemoryCopies/CheckedPathCopyInterface.lean` | Selected memory-path checked fresh-copy/binding contracts without a room premise. |
| `Backend/MemoryCopies/CheckedPathCopy.lean` | Total selected-path checked copying, state adoption and fresh local binding. |
| `Backend/MemoryCopies/CheckedPathCopyControls.lean` | Populated/empty/long/indexed binding, aliases, path refusal and inhabited capacity refusal. |
| `Backend/MemoryCopies/CheckedStorageArrayInterface.lean` | Actual storage-header capacity guard and total primitive storage-to-memory copy contract. |
| `Backend/MemoryCopies/CheckedStorageArray.lean` | Actual storage-length/free-cursor capacity checks and total fresh primitive-array copy execution. |
| `Backend/MemoryCopies/CheckedStorageArrayControls.lean` | Inhabited empty/pair/long storage copies, capacity boundaries and actual header-dependent selection. |
| `Backend/MemoryCopies/CheckedStoragePathInterface.lean` | Checked compiled storage paths, declarations/rebinding and explicit capacity refusal contracts. |
| `Backend/MemoryCopies/CheckedStoragePath.lean` | Actual compiled storage-path guarded execution, complete success transport and separate capacity/path refusals. |
| `Backend/MemoryCopies/CheckedStoragePathControls.lean` | Populated/empty/long declarations and rebinding, old aliases, saturated capacity and path-refusal controls. |
| `Backend/MemoryCopies/CheckedFixedStorageInterface.lean` | Guarded fixed storage-copy contracts retaining complete success clauses and explicit target capacity refusal. |
| `Backend/MemoryCopies/CheckedFixedStorage.lean` | Existing guard execution and complete fixed storage-copy success transport, total capacity cases and code-only oversized refusal. |
| `Backend/MemoryCopies/CheckedFixedStorageControls.lean` | Represented empty/pair/long copies, strict capacity boundaries, preserved old values and explicitly code-only huge demand. |
| `Backend/MemoryCopies/CheckedFixedMemoryInterface.lean` | Total guarded fixed memory-copy contracts retaining allocator, framing, gaps and strict fresh identity. |
| `Backend/MemoryCopies/CheckedFixedMemory.lean` | Existing guard and fixed-copy execution transport, complete fresh-copy success and total target capacity cases. |
| `Backend/MemoryCopies/CheckedFixedMemoryControls.lean` | Represented old aliases, fresh empty/pair/long copies, saturation and strict capacity boundaries with code-only huge demand. |
| `Backend/MemoryCopies/CheckedFixedPathCopyInterface.lean` | Total checked fixed-path copy/binding contracts with full state adoption and distinct path/capacity failures. |
| `Backend/MemoryCopies/CheckedFixedPathCopy.lean` | Existing pointer resolution followed by checked fixed-copy/adoption/local binding with distinct path/capacity refusals. |
| `Backend/MemoryCopies/CheckedFixedPathCopyControls.lean` | Represented empty/pair/long and indexed bindings, alias controls, complete saturated inputs and bounds-before-capacity witnesses. |
| `Backend/MemoryCopies/CheckedFixedStoragePathInterface.lean` | Total checked fixed storage-path body/declaration/rebinding with retained Source success and explicit capacity/path refusals. |
| `Backend/MemoryCopies/CheckedFixedStoragePath.lean` | Actual storage-path checked execution, complete prior Source success transport and distinct path/capacity refusal laws. |
| `Backend/MemoryCopies/CheckedFixedStoragePathControls.lean` | Nested fixed-child storage paths, empty/pair/long fresh bindings, old aliases and represented saturation/path-refusal witnesses. |
| `Backend/MemoryCopies/TraversalWordsInterface.lean` | Unconditional intrinsic copy cell-sum growth and old-object reservation obligations. |
| `Backend/MemoryCopies/TraversalWords.lean` | Actual object reservation sum, exact generic copy growth and preservation of old cell counts. |
| `Backend/MemoryCopies/TraversalWordsControls.lean` | Nested/repeated/shadow/empty/long demand witnesses distinguishing words from identities and root size. |
| `Backend/MemoryCopies/DefaultDemandInterface.lean` | Existing finite-plan cost agreement and unconditional intrinsic default-allocation demand obligations. |
| `Backend/MemoryCopies/DefaultDemand.lean` | Actual default-cell demand agrees with successful existing finite planners and their plans. |
| `Backend/MemoryCopies/DefaultDemandControls.lean` | Actual finite plans, nested/long defaults, unused huge children and distinct selector/capacity boundaries. |
| `Backend/MemoryCopies/CheckedFiniteDefaultInterface.lean` | Total guarded finite-plan body and declaration contracts retaining root offsets and complete success fields. |
| `Backend/MemoryCopies/CheckedFiniteDefault.lean` | Guarded existing finite-plan body and declaration execution with complete retained success guarantees. |
| `Backend/MemoryCopies/CheckedFiniteDefaultControls.lean` | Actual nonzero-root plans, declarations, retained old children and represented saturation/refusal controls. |
| `Backend/MemoryCopies/MemoryCopyDemandInterface.lean` | Actual intrinsic snapshot/copy demand, stable recopy cost and zero-allocation alias-rebinding obligations. |
| `Backend/MemoryCopies/MemoryCopyDemand.lean` | Strip-invariant demand, actual snapshot and repeated-copy cell growth, and real alias-rebinding zero growth. |
| `Backend/MemoryCopies/MemoryCopyDemandControls.lean` | Real shared-child heaps, distinct copied descendants, repeated/empty/long demand and same-input intrinsic/compiled alias controls. |
| `Backend/MemoryCopies/EmptyReferenceStorageInterface.lean` | Existing runtime/checked storage code contracts for empty live arrays with arbitrary map-free elements and shadows. |
| `Backend/MemoryCopies/EmptyReferenceStorage.lean` | Actual zero-header runtime/checked storage copying for arbitrary map-free elements with full allocator and fresh empty-object guarantees. |
| `Backend/MemoryCopies/EmptyReferenceStorageControls.lean` | Reference/shadow/unread-store and unused-child runtime witnesses, complete saturated inputs and wrong-header negatives. |
| `Backend/MemoryCopies/EmptyReferenceMemoryInterface.lean` | Existing runtime/checked empty memory-array deep-copy contracts at arbitrary map-free elements, with complete ownership and freshness. |
| `Backend/MemoryCopies/EmptyReferenceMemory.lean` | Actual empty snapshots and ownership-derived source bounds yield fresh runtime/checked copies with complete framing. |
| `Backend/MemoryCopies/EmptyReferenceMemoryControls.lean` | Represented adjacent-source copying, strict freshness, old caller aliases, unused children and saturated refusal controls. |
| `Backend/MemoryCopies/NestedStorageTurnInterface.lean` | Concrete checked storage-child turn and reserved-parent ownership contract; outer traversal/adoption remain open. |
| `Backend/MemoryCopies/NestedStorageTurn.lean` | Actual checked dynamic primitive storage-child copying composes with reserved-parent pointer writes and complete allocator framing. |
| `Backend/MemoryCopies/NestedStorageTurnControls.lean` | Represented parent reservations, child lengths 0/2/64, last index, fresh roots, wrong slot/pointer/payload and saturated refusal controls. |
| `Backend/MemoryCopies/NestedStorageLoopInterface.lean` | Intrinsic dynamic-child vectors, exact aggregate demand and complete checked traversal contract over a reserved parent. |
| `Backend/MemoryCopies/NestedStorageLoop.lean` | Actual complete variable-length child traversal, final-base pointer/frame preservation and bounded checked refusal. |
| `Backend/MemoryCopies/NestedStorageLoopControls.lean` | Mixed final sibling pointers/payloads, fresh repeated children, suffix framing, saturation and later-refusal controls. |
| `Backend/MemoryCopies/NestedStorageParentInterface.lean` | Checked count-operand reservation/traversal/adoption contract for the actual nested storage value and fresh parent. |
| `Backend/MemoryCopies/NestedStorageParent.lean` | Actual checked parent reservation, child traversal, typed adoption and complete nested-copy ownership/content guarantees. |
| `Backend/MemoryCopies/NestedStorageParentControls.lean` | Adopted root/header/identity, mixed retained payloads, old aliases, empty/long/repeated parents and allocation-refusal boundaries. |
| `Backend/MemoryCopies/NestedStorageHeaderInterface.lean` | One represented outer-slot input derives runtime count/data base; full nested-copy result with arbitrary outer shadows. |
| `Backend/MemoryCopies/NestedStorageHeader.lean` | Runtime outer header and symbolic data-base selection derive all nested child inputs and retain full checked-copy guarantees. |
| `Backend/MemoryCopies/NestedStorageHeaderControls.lean` | Stored outer headers 0/3/64, retained mixed payloads, arbitrary shadows, wrong headers and header-dependent capacity controls. |
| `Backend/MemoryCopies/StorageMemoryPipelineInterface.lean` | Actual checked storage-to-memory then memory-to-memory composition and two refusal phases. |
| `Backend/MemoryCopies/StorageMemoryPipeline.lean` | Actual checked storage/memory composition, retained copies and phase-specific capacity refusal. |
| `Backend/MemoryCopies/StorageMemoryPipelineControls.lean` | Represented empty/pair/long pipelines, both refusal phases, last-fitting and negative controls. |
| `Backend/MemoryCopies/NestedMemoryTurnInterface.lean` | Actual checked nested-memory child selection, deep copying and reserved-parent pointer store. |
| `Backend/MemoryCopies/NestedMemoryTurn.lean` | Actual checked child access, fresh copy, reserved-parent store and separate refusal reasons. |
| `Backend/MemoryCopies/NestedMemoryTurnControls.lean` | Repeated source aliases, empty/pair/long retained payloads and bounds/capacity/negative controls. |
| `Backend/MemoryCopies/SnapshotTransportInterface.lean` | Generic typed snapshots and indexed observations under an explicit kept heap extension. |
| `Backend/MemoryCopies/SnapshotTransport.lean` | Generic rank-bounded snapshot and indexed-child transport through kept heap extensions. |
| `Backend/MemoryCopies/SnapshotTransportControls.lean` | Shared aliases, aggregate extensions, absent indices and changed reachable-payload negative controls. |
| `Backend/MemoryCopies/NestedMemoryLoopInterface.lean` | Actual child-copy traversal with heap-derived rows/count, canonical controls and checked capacity refusal. |
| `Backend/MemoryCopies/NestedMemoryRows.lean` | Heap-derived child rows, kept-heap transport and represented traversal-demand bounds. |
| `Backend/MemoryCopies/NestedMemoryLoop.lean` | Finite checked nested-memory traversal, allocator and source preservation, and explicit capacity refusal. |
| `Backend/MemoryCopies/NestedMemoryLoopControls.lean` | Aliased source children, separate destination pointers, retained words and successful-prefix refusal. |
| `Backend/MemoryCopies/NestedMemoryMixedControls.lean` | Actual 2/0/64 source producer composed with memory traversal and full destination representation. |
| `Backend/MemoryCopies/MemoryParentSnapshotInterface.lean` | Complete parent snapshot signature from actual heap-derived primitive child rows. |
| `Backend/MemoryCopies/MemoryParentSnapshot.lean` | Complete parent snapshot and copied-heap agreement from actual heap-derived child rows. |
| `Backend/MemoryCopies/MemoryParentSnapshotControls.lean` | Mixed, empty and aliased snapshot contents, exact word growth and rejected incorrect snapshots. |
| `Backend/MemoryCopies/NestedMemoryParentInterface.lean` | Actual source-header load, checked nested-memory parent copy and complete allocator/snapshot contract. |
| `Backend/MemoryCopies/NestedMemoryParent.lean` | Compiled actual-header nested-memory copy with checked reservation, traversal and complete typed parent adoption. |
| `Backend/MemoryCopies/NestedMemoryParentDemand.lean` | Exact natural parent/child demand equals existing source snapshot word growth. |
| `Backend/MemoryCopies/NestedMemoryParentControls.lean` | Inhabited alias, copied-word, empty/long, explicit refusal and negative parent-entry controls. |
| `Backend/MemoryCopies/NestedMemoryParentMixedControls.lean` | Actual mixed 2/0/64 producer composed with compiled parent entry and complete copy certificate. |
| `Backend/MemoryCopies/NestedLocationPipelineInterface.lean` | Actual nested storage-to-memory-to-memory execution, allocator and phase-refusal obligations; word-machine scope. |
| `Backend/MemoryCopies/NestedLocationPipeline.lean` | Two actual nested copy phases, retained heaps and separate capacity refusals. |
| `Backend/MemoryCopies/NestedLocationPipelineObservations.lean` | Observable returned root, both parent headers, free cursor and machine framing. |
| `Backend/MemoryCopies/NestedLocationPipelineControls.lean` | Inhabited empty/mixed 2/0/64 executions and distinct first/second allocation refusals. |
| `Backend/MemoryCopies/BudgetedDefaultInterface.lean` | Configurable target word budgets, full selected-default success/refusal and 32-byte live-cell address bounds. |
| `Backend/MemoryCopies/BudgetedDefault.lean` | Existing-guard bias, total checked selected defaults, complete allocator contract and live-cell address-fit proof. |
| `Backend/MemoryCopies/BudgetedDefaultControls.lean` | Inhabited certificate, represented empty/nested successes, strict and zero-budget refusals, actual child contents and address-bound controls. |
| `Backend/MemoryCopies/BudgetedFiniteInterface.lean` | Configurable finite-plan guards with complete existing success and actual declaration growth contracts. |
| `Backend/MemoryCopies/BudgetedFinite.lean` | Total configurable finite-plan success/refusal and actual declaration growth, retaining the original full contract. |
| `Backend/MemoryCopies/BudgetedFiniteControls.lean` | Nonzero parent offsets, actual child layout/declaration bindings, retained earlier children and strict/zero budget refusals. |
| `Backend/MemoryCopies/BudgetedReferenceInterface.lean` | Configurable runtime reference-array budget guard and complete actual success/refusal certificate. |
| `Backend/MemoryCopies/BudgetedReference.lean` | Division-based runtime budget checking and total complete allocator success/refusal for the unchanged reference constructor. |
| `Backend/MemoryCopies/BudgetedReferenceControls.lean` | Populated empty/long/reference defaults, oversized unused-child success, overflow/strict-budget refusals and same-heap child contents. |
| `Backend/MemoryCopies/FixedReferenceDeclareInterface.lean` | Contract only for checked fixed-reference declarations with actual successful TRun/StateRepr and separate machine capacity refusal. |
| `Backend/MemoryCopies/FixedReferenceDeclare.lean` | Proved actual intrinsic TRun declaration and checked word-machine local binding with full object StateRepr, allocator and machine capacity refusal. |
| `Backend/MemoryCopies/FixedReferenceDeclareControls.lean` | Inhabited declaration/post-state/local-pointer controls with retained shadows, empty/64-element child and machine capacity refusal. |
| `Backend/MemoryCopies/FixedReferenceDeclareFrameControls.lean` | Nonempty heap/two-alias declaration framing controls, separate inhabited copy-gap transport and overlapping-gap negative control. |
| `Backend/MemoryCopies/FixedReferenceLiveInterface.lean` | Signature-only live normalization contract for all fixed primitive-array children, retaining original copy/representation despite storage shadows. |
| `Backend/MemoryCopies/FixedReferenceLive.lean` | Inhabited intrinsic live normalization preserving exact original storage copy, representation and stripped contents for arbitrary child shadows. |
| `Backend/MemoryCopies/FixedReferenceLiveControls.lean` | Arbitrary-shadow, zero/long/many controls and represented fixed-parent execution retaining original copied heap and stored shadows. |
| `Backend/MemoryCopies/FixedReferenceStorageLoopInterface.lean` | Headerless storage-child traversal with exact intrinsic row copying, pointer/framing/gap guarantees and total capacity refusal. |
| `Backend/MemoryCopies/FixedReferenceStorageLoop.lean` | Finite headerless child-loop execution, exact allocator growth and pointer/framing transport, total size refusal. |
| `Backend/MemoryCopies/FixedReferenceStorageLoopControls.lean` | Mixed 2/0/64-element children, retained pointers/payloads, suffixes, actual later-refusal prefix and zero-count padded reservation. |
| `Backend/MemoryCopies/FixedReferenceMemoryLoopInterface.lean` | Contract only for actual fixed-parent memory child traversal with heap-derived rows, exact demand, headerless stores, source snapshot preservation and total capacity refusal. |
| `Backend/MemoryCopies/FixedReferenceMemoryRows.lean` | Heap-derived fixed child rows, exact length and demand bounds, and snapshot-preserving row transport through actual checked child copies. |
| `Backend/MemoryCopies/FixedReferenceMemoryLoop.lean` | Proved headerless fixed-memory child traversal with exact runtime demand, total capacity refusal, old-source snapshot preservation and fresh sibling copies. |
| `Backend/MemoryCopies/FixedReferenceMemoryLoopControls.lean` | Represented shared-child and zero-outer fixed sources; actual empty/pair/64-element traversal, fresh pointers, later-child refusal and empty-parent padding preservation. |
| `Backend/MemoryCopies/FixedReferenceMemoryTurnInterface.lean` | Contract only for a headerless fixed-memory parent child read, checked deep copy and header0 reservation store, with distinct access/capacity refusals. |
| `Backend/MemoryCopies/FixedReferenceMemoryTurn.lean` | Proved actual fixed-parent memory child selection, checked deep child copy and header0 store preserving allocator, source graph, snapshot and reserved gap, with distinct refusals. |
| `Backend/MemoryCopies/FixedReferenceMemoryTurnControls.lean` | Represented fixed source with shared child aliases; actual empty/pair/64-element copies, distinct access/capacity refusals and header-shift/alias/payload negatives. |
| `Backend/MemoryCopies/FixedReferenceStorageParentInterface.lean` | Signature-only fixed-parent storage-copy contract: source representation, typed adoption, exact demand/growth and refusal. |
| `Backend/MemoryCopies/FixedReferenceStorageParent.lean` | Full fixed storage representation, existing reservation/traversal/typed adoption, exact demand/growth and total size refusal. |
| `Backend/MemoryCopies/FixedReferenceStorageParentControls.lean` | Empty/mixed/64-child typed parents, exact payloads/growth, alias retention, static code refusal and real reservation-prefix child failure. |
| `Backend/MemoryCopies/FixedReferencePathCopyInterface.lean` | Contract only for checked compiled path plus fixed-parent copying of original arbitrary-shadow values, exact allocation and capacity refusal. |
| `Backend/MemoryCopies/FixedReferencePathCopy.lean` | Proved actual compiled path plus checked parent copying for original arbitrary-shadow fixed reference values, full allocator/snapshot/growth and capacity refusal. |
| `Backend/MemoryCopies/FixedReferencePathCopyControls.lean` | Inhabited retained-shadow path-copy execution40to44, empty/64-element child successes and real capacity refusal after path success. |
| `Backend/MemoryCopies/FixedReferencePathInterface.lean` | Contract only for compiled storage-path selection of arbitrary-shadow fixed reference values and their live representation. |
| `Backend/MemoryCopies/FixedReferencePath.lean` | Proved actual compiled path selection of original fixed-reference storage operands with live canonical representation. |
| `Backend/MemoryCopies/FixedReferencePathControls.lean` | Inhabited represented root selection with retained child shadows, empty/64-element child and wrong-slot negative controls. |
| `Backend/MemoryCopies/FixedReferenceRebindInterface.lean` | Contract only for checked fixed-reference local rebinding with intrinsic TRun/post-StateRepr, old-object preservation and machine capacity refusal. |
| `Backend/MemoryCopies/FixedReferenceRebind.lean` | Proved checked intrinsic fixed-reference local rebinding, full post-state/allocator, old-heap and fresh-root preservation, and machine capacity refusal. |
| `Backend/MemoryCopies/FixedReferenceRebindControls.lean` | Populated old-parent/child alias-separation controls, preserved live words, empty/64-element child successes and capacity refusal after path success. |
| `Backend/MemoryCopies/FixedReferenceStorageTurnInterface.lean` | Headerless fixed-parent storage-child step with actual checked copying, allocator/gap/framing and refusal contracts. |
| `Backend/MemoryCopies/FixedReferenceStorageTurn.lean` | Actual checked child copying and header0 pointer-store with complete allocator/gap/framing and total refusal. |
| `Backend/MemoryCopies/FixedReferenceStorageTurnControls.lean` | Actual fixed reservations, empty/pair/64-element child payloads, headerless-pointer negative and represented saturated refusals. |
| `Backend/MemoryCopies/GuardedDefaultDeclarationInterface.lean` | Guard the actual selected declaration code; explicit frame/representation inputs and capacity-free success-or-refusal contract. |
| `Backend/MemoryCopies/GuardedDefaultDeclaration.lean` | Guard the actual selected declaration with complete success state/allocator contract and explicit capacity refusal. |
| `Backend/MemoryCopies/GuardedDefaultDeclarationControls.lean` | Actual body selection, local bindings, stack/payload, full new contents, represented saturation refusal and unsupported-domain controls. |
| `Backend/MemoryCopies/NestedLivePipelineInterface.lean` | Contract only for original shadow-retaining nested values through the existing two-copy pipeline, with full reached states and two refusal phases. |
| `Backend/MemoryCopies/NestedLivePipeline.lean` | Proved original-value nested storage/memory pipeline by exact whole-copy and strip transport, retaining both reached refusal phases. |
| `Backend/MemoryCopies/NestedLivePipelineControls.lean` | Original outer/child shadows, mixed live lengths, two fresh copies, actual final cursor, shallow-copy negative and first/later represented capacity-refusal controls. |
| `Backend/MemoryCopies/NestedMemoryPathFrameInterface.lean` | Additive contract only for gap-preserving selected nested deep binding; frozen binding contract unchanged. |
| `Backend/MemoryCopies/NestedMemoryPathFrame.lean` | Proved additive nested deep binding gap transport at the same full post-state and allocator witnesses. |
| `Backend/MemoryCopies/NestedMemoryPathInterface.lean` | Contract only for selected nested memory paths, checked deep snapshot copying/binding, preserved old contents and distinct path/capacity refusals. |
| `Backend/MemoryCopies/NestedMemoryPath.lean` | Proved selected nested deep copy/binding with full typed adoption, preserved old/new snapshots and separate path/capacity refusal. |
| `Backend/MemoryCopies/NestedMemoryPathControls.lean` | Populated shared-child and overlapping-local controls distinguish alias from deep copy, observe distinct fresh children and actual target words, and test represented capacity refusal. |
| `Backend/MemoryCopies/NestedStorageLiveInterface.lean` | Contract only for live normalization and existing checked dynamic-outer-array copying with arbitrary outer and child storage shadows. |
| `Backend/MemoryCopies/NestedStorageLive.lean` | Proved exact live normalization, ReprAt transport and existing checked dynamic nested runtime copying for original arbitrary outer/child shadows. |
| `Backend/MemoryCopies/NestedStorageLiveControls.lean` | Populated-heap mixed-length dynamic execution, retained outer/child shadows, 64-empty-child success and represented capacity refusal. |
| `Backend/MemoryCopies/NestedStoragePathInterface.lean` | Contract only for actual dynamic-outer storage path copying and intrinsic declaration/rebinding, full post-state/allocator and machine refusal. |
| `Backend/MemoryCopies/NestedStoragePath.lean` | Proved actual dynamic storage paths, exact live demand/growth, checked copy and intrinsic declaration/rebinding with full typed local transport. |
| `Backend/MemoryCopies/NestedStoragePathControls.lean` | Populated dynamic parent/child alias controls for copy growth, declaration, rebinding, empty/long children and machine capacity refusal. |
| `Backend/MemoryCopies/ReferenceDefaultDemandInterface.lean` | Actual runtime reference-array default demand and existing checked guard agreement; compiler selection explicit. |
| `Backend/MemoryCopies/ReferenceDefaultDemand.lean` | Existing runtime default copy, actual live demand, heap-word growth and checked capacity branch agree under explicit compiler selection. |
| `Backend/MemoryCopies/ReferenceDefaultDemandControls.lean` | Actual empty/2/64 and struct-child runs, explicit new contents, unused huge child, refusals and rejected-selection cost control. |
| `Backend/MemoryCopies/SelectedDefaultDemandInterface.lean` | Existing default compiler selection implies exact intrinsic cell demand and checked capacity agreement. |
| `Backend/MemoryCopies/SelectedDefaultDemand.lean` | Actual selected default cost equals live allocation demand; heap growth and checked guard agree without a capacity premise. |
| `Backend/MemoryCopies/SelectedDefaultDemandControls.lean` | Selected/unselected cost controls, actual nested child snapshot, empty/long/unused-huge success, refusal and wrong cursor. |
| `Backend/MemoryCopies/SnapshotRestoreInterface.lean` | Contract only for typed captured-array copy-back after an explicitly executed memory-preserving intervention, with reached-store cleanup and framing. |
| `Backend/MemoryCopies/SnapshotRestore.lean` | Proved typed captured-array restoration after an explicit memory-preserving intervention, with reached-old cleanup and reached-store framing. |
| `Backend/MemoryCopies/SnapshotRestoreControls.lean` | Executed length-changing storage intervention on empty, pair and 64-element captures; actual captured-memory write refutes preservation. |
| `Backend/MemoryCopies/StorageRoundTripInterface.lean` | Contract only for actual primitive-array storage/memory/deep-memory/storage composition with represented destination, cleanup, framing and ordered allocation refusals. |
| `Backend/MemoryCopies/StorageRoundTrip.lean` | Proved actual primitive-array copy-back from the reached two-copy allocator, preserving typed destination overlay, cleanup, storage/memory framing and ordered refusals. |
| `Backend/MemoryCopies/StorageRoundTripControls.lean` | Closed round-trip runs, executable length-first cleanup mutant, same-slot snapshot restoration after explicit changed contents, framing observations and ordered refusals. |
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
