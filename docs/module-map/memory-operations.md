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
| `Backend/MemoryCopies/Interface.lean` | Draft typed memory default/copy certificate signatures (see [memory copies](../feature-work/memory-copies.md)); Finite heap, dynamic length, alias and overlap obligations; Source outcomes are in SourceInterface. |
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
| `Backend/MemoryOps/CalldataViewExtension.lean` | Bounded v11-memory-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryOps/CalldataViewExtensionControls.lean` | Bounded v11-memory-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryCopies/TraversalControls.lean` | Bounded memory-copies checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryCopies/TraversalFresh.lean` | Bounded memory-copies checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryCopies/TraversalInterface.lean` | Bounded memory-copies checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryOps/PhysicalByteWorldInterface.lean` | Bounded v11-memory-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryCopies/ControlsV2.lean` | Bounded memory-copies checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryCopies/InterfaceV2Roots.lean` | Bounded memory-copies checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryOps/PhysicalByteStore.lean` | Bounded v11-memory-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryOps/PhysicalByteStoreControls.lean` | Bounded v11-memory-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryOps/SourceRawBoolCopy.lean` | Bounded v11-memory-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryOps/SourceRawBoolCopyControls.lean` | Bounded v11-memory-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryOps/SourceRawBoolEntry.lean` | Bounded v11-memory-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryCopies/NestedDefaultInterface.lean` | Bounded memory-copies checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryCopies/RuntimeArrayInterface.lean` | Bounded memory-copies checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryCopies/SelectedArrayDefaultInterface.lean` | Bounded memory-copies checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryCopies/SourceInterface.lean` | Bounded memory-copies checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/MemoryCopies/SourceControls.lean` | Inhabited Source certificates with populated storage-copy observations, default/timeout controls and size-boundary witnesses. |
| `Backend/MemoryCopies/SourceSize.lean` | Derives new-array oversized-length panic from evaluation, conversion and size hypotheses. |
| `Backend/MemoryCopies/SourceFramesInterface.lean` | Exact Source allocation-frame obligations for all default and storage-load traversal families, including halted runs. |
| `Backend/MemoryCopies/SourceFramesCore.lean` | Source allocation-frame reflexivity/transitivity and bind/read/allocation preservation over the existing Hoare rules. |
| `Backend/MemoryCopies/SourceDefaultFrames.lean` | Generic allocation-frame proofs for all four Source default traversals and exact success-or-Halt outcome certificates. |
| `Backend/MemoryCopies/SourceStorageFrames.lean` | Generic allocation-frame proofs for all five Source storage-load traversals and exact outcome certificates. |
| `Backend/MemoryCopies/SourceRootCopies.lean` | Derives a fresh-parent Source copy certificate from an actual successful load, preserving old objects and nonheap state. |
| `Backend/MemoryCopies/SourceFramesControls.lean` | Declared nested bytes-array copy, fixed reference-array default and partial-timeout controls with retained child allocation. |
| `Backend/MemoryCopies/SourceSizeInputs.lean` | Additive evaluation/conversion/oversize inputs; preserves the published panic premise and failure field. |
| `Backend/MemoryCopies/InterfaceV2Roots.lean` | Optional fresh-root and preserved-gap companion without changing the published V2 certificate. |
| `Backend/MemoryCopies/HeapContentsInterface.lean` | Live-content roundtrip obligation over the existing intrinsic heap mirror, without a new copy evaluator. |
| `Backend/MemoryCopies/HeapContents.lean` | Generic mirror readback and inhabited V2 live-storage contents certificates via existing rank-fuel independence. |
| `Backend/MemoryCopies/HeapContentsControls.lean` | Populated nested 2/0/64-length children, fresh parent, struct/fixed holders and wrong-live-value/shadow controls. |
| `Backend/MemoryCopies/DeepCopyContents.lean` | Inhabited fresh snapshot-copy heap certificate and initial live contents after actual old-object overlap schedules, with alias/empty/refusal controls. |
| `Backend/MemoryCopies/AllocationPanicInterface.lean` | Explicit Source allocation-panic state and byte-exact emitted terminal-slice obligation; no size-selector premise hidden. |
| `Backend/MemoryCopies/AllocationPanic.lean` | Derived oversized Source failure joined to reused byte-exact Panic(0x41) emission, packet framing and wrong-result/timeout/zero-length controls. |
| `Backend/MemoryCopies/NestedDefaultInterface.lean` | Production-selected nested-array default builder with a real fitting allocator witness; no new compiler or admission filter. |
| `Backend/MemoryCopies/NestedDefaults.lean` | Total production selection for fixed dimensions around empty dynamic defaults, exact cost and existing allocator-growth execution. |
| `Backend/MemoryCopies/NestedDefaultControls.lean` | Populated represented inputs with actual selected-code root/cursor/old-word observations and empty-code/wrong-cursor controls. |
| `Backend/MemoryCopies/RuntimeArrayInterface.lean` | Production-selected child defaults with complete runtime-parent allocation demand and a real fitting input; no unused-child feasibility condition. |
| `Backend/MemoryCopies/RuntimeArrays.lean` | Production-selected runtime reference-array loop and scoped declaration correctness, complete parent demand and size-independent code. |
| `Backend/MemoryCopies/RuntimeArrayControls.lean` | Actual populated runtime lengths0/2/64, empty-any-child and same-code controls, scoped declaration execution and wrong-cursor rejection. |

| `Backend/MemoryCopies/TraversalInterface.lean` | Fresh and strictly ordered sibling identities over the actual typed storage-copy vector fold. |
| `Backend/MemoryCopies/TraversalFresh.lean` | Generic fresh strictly ordered sibling identities and nonaliasing from the existing typed storage-copy fold. |
| `Backend/MemoryCopies/TraversalControls.lean` | Repeated populated nested trees after old ownership, empty/64 vectors and shared-identity negative control. |
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
