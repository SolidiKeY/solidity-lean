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
