# External try execution evidence

| Module | What it defines |
|---|---|
| `Semantics/ExternalTryWitness.lean` | Exact external oracle/decoder equations and normal-return witnesses for all four try alternatives; caller-failure controls. |
| `Counterexamples/DiamondTry.lean` | A reached try admits a caller revert, refuting its universal callback diamond under either payment flag. |
| `Examples/Tactics/ExternalTryWitness.lean` | Source-shaped explicit-oracle controls, ordered storage observations, caller failures and callback refusal. |

## Deterministic try formula witnesses

| Module | Defines |
|---|---|
| `Calculus/Sound/ExternalTryWitness.lean` | State-indexed deterministic diamond transport from explicit normal try and allocated catch-data witnesses; no validity or callback promotion. |
| `Examples/Tactics/ExternalTryFormula.lean` | Concrete success/catch formulas, allocated raw/reason payloads, explicit frame transport and refusal controls. |
| `Examples/Tactics/ExternalTryUniversal.lean` | Countermodel over the actual original source-domain builders: no universal normal-try family, deterministic validity or callback source-profile validity for the quoted Probe. |

## Explicit conditional try outcomes

| Module | Defines |
|---|---|
| `Semantics/TryConditions.lean` | Exact full-result self/oracle and payload-catch conditions, with argument-prefix success/failure transport. |
| `Semantics/TryCreateConditions.lean` | Exact creation-try conditions over the unchanged typed world interface. |
| `Calculus/Sound/TryConditions.lean` | Guarded ordinary formula transport for all results/frames and exact normal-or-exhausted diamond account. |
| `Examples/Tactics/TryConditions.lean` | Arbitrary-state explicitly guarded source success, certified failure boundaries and typed/runtime replay-context refusals. |


## Native self-try entry return bridge

| Module | Defines |
|---|---|
| `Semantics/EntryReturn.lean` | Conditional source/serializer call composition, exact heap/reference/caller capture, failures and bounded-to-ordinary execution agreement. |
| `Tools/EntryReturn.lean` | Exact-declaration, original-prefix-scope entry-only serializer for a primitive prefix plus one source-marked bytes/string memory result, or one return-only external-void function value. |
| `Examples/Tactics/EntryReturn.lean` | Actual native bridge quotations, bytes/once-only kernel snapshots, normal ordinary witnesses and negative admission/input controls. |
| `Examples/Tactics/EntryReturnFlow.lean` | Legacy loop-return, alias-mutation, modifier-continuation and default-memory kernel controls. |
| `Examples/Tactics/EntryReturnFlowIR.lean` | The same controls under existing viaIR modifier frames, with safe kernel declaration factoring for the large quotation. |
| `Examples/Tactics/EntryReturnMetadata.lean` | Signed narrow and fixed-byte return metadata, exact order and empty memory kernel control. |
| `Examples/Tactics/EntryReturnFunction.lean` | Output-only external-function address/selector, bytes24 padding, order and once-only kernel witnesses in both evaluation modes; function-input refusals remain. |

## Creation-try caller continuations

| Module | Defines |
|---|---|
| `Semantics/CreationTryFrame.lean` | Typed pending caller/creation/handler/tail composition over existing World operations, exact failure and allocation laws, universal bounded-to-ordinary approximation. |
| `Frontend/CreationTryImport.lean` | Complete-declaration, identity-resolved stateless unpaid creation-try source compiler with actual constructor, local argument, returned handle and Error payload branches. |
| `Tools/CreationTryReplay.lean` | Bounded native creation source observations with explicit checked runtime context, actual typed world threading and refusal controls. |
| `Examples/Tactics/CreationTrySource.lean` | Complete original creation source outputs, ordinary transport, argument/rollback/installation/wrong-byte kernel controls and malformed replay controls. |
| `Examples/Tactics/CreationTrySourceIR.lean` | Separately compiled viaIR original creation source with both ordered output kernel witnesses. |


## Linked library try source continuation

| Module | Owning role |
|---|---|
| `Semantics/LibraryTryFrame.lean` | Installed library try boundary with total raw extraction, outer decoder, exact caller resume/context/storage/ledger laws and ordinary transport. |
| `Frontend/LibraryTryImport.lean` | Complete checked library/caller declarations and exact scalar/storage-formal mapping into caller-typed programs. |
| `Tools/LibraryTryReplay.lean` | Explicit concrete linked runtime context, canonical Boolean input, once-only world execution and caller-storage observations. |
| `Examples/Tactics/LibraryTrySource.lean` | Original ordered outputs, ordinary-reading equality and actual prefix storage witnesses. |
| `Examples/Tactics/LibraryTryControls.lean` | Wrong role/identity/frame, decoder/input/static refusals, exact storage alias and atomic rollback controls. |
| `Examples/Tactics/LibraryTrySourceIR.lean` | Separately compiled via-IR original linked source with all ordered output certificates. |

M1 try producer side witnesses: `Evm/TryByteImage.lean` bounds scalar-frame
byte images and overlap/snapshots; `Evm/TryByteCapture.lean` reuses typed
allocation and raw halt; `Evm/TryPanicProducer.lean` computes the source-linked
36-byte component. `Examples/Tactics/TryPanicProducer.lean` keeps constructed-call
controls distinct. See [bounded milestone](../feature-work/diamond-try-m1.md); none
admits physical assembly or proves target-byte/original-callee transport.

| Module | Purpose |
|---|---|
| `Evm/TryPanicCarrier.lean` | Closed intrinsic constructed-call carrier; no original-source construction, bytecode adequacy, callback change or source admission is asserted. |
| `Examples/Tactics/TryPanicCarrier.lean` | Nonvacuous constructed-call controls; no source or target adequacy is claimed. |
| `Evm/TryPanicSourcePlan.lean`, `Evm/TryPanicSourceFrame.lean`, `Evm/TryPanicSourceDeterminism.lean` | H8 bounded try/panic source model: `ThreeOp` plan, `BodyCompletedAt`, `FiniteEntry`, completion uniqueness ([H8](../feature-work/diamond-try-h8-source-model.md)). |
| `Frontend/SolcJson/TryPanicSourceData.lean`, `Frontend/SolcJson/TryPanicSourcePlan.lean`, `Frontend/SolcJson/TryPanicSourceCaller.lean`, `Examples/Tactics/TryPanicSource{Plan,Determinism,Whole}.lean` | Quoted pinned AST/input and structural derivations; controls. |
| `Semantics/ContractWorldCertificates.lean` | Published paid-run/source-wrapper operation certificates, reused unchanged from origin/master cc155f36. |
| `Semantics/PaymentWorld.lean` | Typed stipend source frames over actual world calls; send completed-failure handling, transfer exact halt transport, no-op/funding and atomic rollback laws. |
| `Frontend/PaymentPlan.lean` | Complete declaration-resolved creation/send and initializer/receive/transfer/getter source shapes; unknown effects and full-gas calls refused. |
| `Frontend/PaymentImport.lean` | Imports actual receive/getter code, builds typed initializer handle assignment and paid creation/payment compositions with source identities. |
| `Tools/PaymentReplay.lean` | Ordered deterministic source-world observations with actual nested bytes and committed-world audits; gas remains an independent obligation. |
| `Examples/Tactics/PaymentSource.lean` | Kernel-checked original send and debug transfer source snapshots, initialized handle/funding/getter witnesses and wrong handle/kind/bytes controls. |
| `Backend/Creation/Artifact.lean` | G44.02 intrinsic artifact sections, executable CODECOPY/RETURN wrapper, exact minimal PUSH widths, layout and argument extraction laws. |
| `Backend/Creation/ArtifactChecks.lean` | G44.02 inhabited layout, argument separation and negative controls with headline kernel axiom pins. |
| `Backend/Creation/Execution.lean` | Independent byte-consuming PUSH/CODECOPY/RETURN/REVERT slice semantics and exact installed runtime proof. |
| `Backend/Creation/ExecutionChecks.lean` | Inhabited empty, word and PUSH-width boundary installation witnesses, byte-range negative controls and axiom pins. |
| `Backend/Creation/Placement.lean` | Relocated runtime-return slice with arithmetic alignment certificate and minimal offset PUSH width. |
| `Backend/Creation/PlacementChecks.lean` | Inhabited PUSH1/PUSH2 offset transition controls with nonempty runtime and arguments. |
| `Backend/Creation/Regions.lean` | Bounded typed patch regions, assembler overwrite length/frame laws and disjoint commutation. |
| `Backend/Creation/Linking.lean` | Certified absolute/local link metadata, exact 20-byte addresses, unresolved refusal and existing assembler linking through wrapper/arguments. |
| `Backend/Creation/LinkLayout.lean` | Bounds and pairwise disjointness derived from actual assembler link metadata for every successful assembly. |
| `Backend/Creation/LinkingChecks.lean` | Inhabited library-link/install controls, unresolved/missing/wrong-origin/truncated-argument negatives and axiom pins. |
| `Backend/Creation/Immutables.lean` | Typed bounded immutable words, disjoint table checks, per-patch readback/frame laws and certified link/immutable combination. |
| `Backend/Creation/ImmutableChecks.lean` | Immutable bounds/overlap/readback/frame/install and combined library/immutable controls with axiom pins. |
| `Backend/Creation/Constructor.lean` | Independently checked byte-prefix steps composed with exact runtime-return or exact-byte revert wrappers, over arbitrary prefix memory. |
| `Backend/Creation/ConstructorChecks.lean` | Actual copying constructor-prefix witnesses, return/revert separation and nonempty argument controls. |
| `Backend/Creation/ArtifactLaws.lean` | Arbitrary disjoint link permutations, payload determinism, section uniqueness and wrapper decode law. |
| `Backend/Creation/Provenance.lean` | Intrinsic generated/source range records, section bounds and exact provenance byte extraction. |
| `Backend/Creation/LawChecks.lean` | Three-link permutation, overlapping-order negative, metadata/layout and inhabited provenance controls. |
| `Backend/Failure/Immediate.lean` | Big-endian PUSH32 machine immediates and exact numeric reading. |
| `Backend/Failure/Gap.lean` | Base-interface panic boundary gap controls. |
| `Backend/Failure/Emit.lean` | Typed failure/return payloads and actual MSTORE8/RETURN/REVERT instruction emission. |
| `Backend/Failure/EmissionChecks.lean` | Inhabited emission, byte vector, negative and combination controls with axiom pins. |
| `Backend/Failure/Slice.lean` | Independent typed-word PUSH/MSTORE8/RETURN/REVERT byte-memory execution and checked stack heights. |
| `Backend/Failure/Correct.lean` | Exact emitter execution, stack/memory frames, bounded-stack certificate and arbitrary chunk/tail laws. |
| `Backend/Failure/SliceChecks.lean` | Literal instruction, underflow/truncation, memory/frame/chunk, concatenation and1022/1023 stack controls. |
| `Backend/Failure/Observe.lean` | Existing THalt/TRes source observation relation, deterministic payload correspondence and checked emission. |
| `Backend/Failure/ObservationChecks.lean` | Inhabited source assert/require/custom/return, complete-body selector negatives and wrong-observation refutations. |
| `Backend/Failure/Checkpoint.lean` | Independent component-local typed persistent/transient checkpoint relation and compositional restore rules. |
| `Backend/Failure/Unwind.lean` | Checked emitted payload execution before local unwind; success/failure and nested-failure proofs. |
| `Backend/Failure/UnwindChecks.lean` | Inhabited distinct snapshots, nested emitted failures, caller-memory restoration and wrong-snapshot negatives. |
| `Backend/Failure/Composition.lean` | Arbitrary two-write-block byte noninterference, immutable input preservation and checked emitter concatenation/terminal distinction. |
| `Backend/Failure/CompositionChecks.lean` | Inhabited both-executed writes, overlap negative, overlapping ignored suffix and same-bytes terminal controls. |
| `Evm/MemoryStorageCopyLoop.lean` | Runtime counter loops: exact primitive payload writes, explicit zero cleanup, finite termination and slot/frame laws. |
| `Evm/MemoryStorageCopyCode.lean` | Runtime-length memory-array copy code: payload loop, old live tail clearing and final length replacement, with exact execution equation. |
| `Evm/MemoryStorageCopyLaws.lean` | Typed heap snapshot/overlay representation, live/tail reads and destination frames for the iterative array copy. |
| `Evm/MemoryStorageCopySource.lean` | Source assignment simulation through supported pointer/storage paths, destination reversion and fragile-alias invalidation for resizing arrays. |
| `Evm/MemoryStorageStructCopy.lean` | Primitive-member physical offset laws, finite struct copy loop and full typed memory-to-storage assignment simulation. |
| `Evm/MemoryFixedStorageCopy.lean` | Additive typed fixed-array payload refinement, actual inline copy loop, snapshot/frame laws and same-size source simulation; legacy inputs unchanged. |
| `Evm/MemoryFixedShapeCode.lean` | Actual iterative fixed-source conversions: inline padding or dynamic payload/tail cleanup and final header replacement. |
| `Evm/MemoryFixedShapeLaws.lean` | Exact fixed-source snapshot, primitive padding, live/tail and frame representation laws. |
| `Evm/MemoryFixedShapeSource.lean` | Typed fixed-to-dynamic/padded-fixed source assignment simulations with source-before-destination evaluation and failure preservation. |
| `Evm/MemoryFixedMixedCopy.lean` | Dynamic-array/primitive-struct simulations that retain the fixed payload refinement and exact source heap/target memory preservation. |
| `Evm/MemoryFixedCompile.lean` | Intrinsic read-only compiler certificates and admission for fixed copies, mixed copy families, guards, scopes and branches; no unproved heap ownership for mutations/allocations. |
| `Evm/MemoryFixedCopyExamples.lean` | Inhabited public fixed-copy correctness inputs, root/member/mapping and shape observations, deep-copy, failed-destination zero-demand, tail cleanup and reference-element/mutation refusal controls. |
| `Evm/MemoryFixedMixedExamples.lean` | Inhabited fixed-memory compiler input with fixed-array, dynamic-array and primitive-struct source objects; combined source/compiled observations and correctness. |
| `Evm/MemoryStorageObjectCopy.lean` | Typed projection from full object ownership to fixed payloads; source-execution-derived heap/memory preservation restores full ownership and allocator after copies. |
| `Evm/MemoryStorageConstructionCompile.lean` | Sequential composition of published construction/mutation and copy certificates, with exact capacity, base extension, allocator growth and reached-copy bounds. |
| `Evm/MemoryStorageLifecycleExamples.lean` | Inhabited public allocation-initialization-copy-mutation lifecycle for fixed/dynamic/struct sources; live/shadow/tail observations, invalid bound and failed destination controls. |
| `Evm/MemoryCopyBound.lean` | Recursor-based reached successful copy demand for the existing storage representation bound; zero on failed destinations and unreachable suffixes. |
| `Evm/MemoryStorageCopyExamples.lean` | Inhabited public correctness inputs and source/compiled independence, replacement, cleanup, signed/Boolean, invalid-bound, failed/unreachable and refusal controls. |
| `Storage/Representation/Model.lean` | Intrinsic value-independent layout shapes and represented scalar, struct, mapping, fixed/dynamic-array values including retained shadows. |
| `Storage/Representation/Controls.lean` | Inhabited representation witnesses, source reads, negative scalar control and exact axiom pins. |
| `Storage/Representation/Reads.lean` | Exact source scalar/mapping/array reads, failures and source frames. |
| `Storage/Representation/Frames.lean` | Representation locality over existing Occ footprints and nested frames. |
| `Storage/Representation/Words.lean` | Supported full-word key bounds, normalization and injectivity. |
| `Storage/Representation/Updates.lean` | Abstract symbolic replacement and nested mapping source saves. |
| `Storage/Representation/Members.lean` | Source member reads/replacement with whole intrinsic field-store preservation. |
| `Storage/Representation/UpdateControls.lean` | Inhabited member/nested mapping combinations, defaults, alias controls and axiom pins. |
| `Storage/Representation/Arrays.lean` | Fixed/dynamic whole-array source saves, live/retained bounds and exact header/element frames. |
| `Storage/Representation/ArrayControls.lean` | Heterogeneous fixed/dynamic, nested save, defaults, stale aliases, live failures and header controls. |
| `Storage/Representation/Transport.lean` | Finite per-run numeric realization, covered writes/sequences, frames and existing exact source observations. |
| `Storage/Representation/TransportControls.lean` | Inhabited root/hash/data run, source read/save/header combinations and collision/bound/coverage/failure controls. |
| `Storage/Representation/GraphLayout.lean` | Typed storage graph representation component; see [feature document](../feature-work/storage-value-representation.md). |
| `Storage/Representation/GraphFrames.lean` | Typed storage graph representation component; see [feature document](../feature-work/storage-value-representation.md). |
| `Storage/Representation/GraphRepresentation.lean` | Typed storage graph representation component; see [feature document](../feature-work/storage-value-representation.md). |
| `Storage/Representation/GraphCompatibility.lean` | Typed storage graph representation component; see [feature document](../feature-work/storage-value-representation.md). |
| `Storage/Representation/GraphControls.lean` | Typed storage graph representation component; see [feature document](../feature-work/storage-value-representation.md). |
