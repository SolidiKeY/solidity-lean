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
