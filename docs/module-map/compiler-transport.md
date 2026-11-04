# Compiler transport proof components

Scoped intrinsic-program and abstract-machine results; see [their boundary](../feature-work/compiler-transport-proofs.md).

| Module | Holds |
|---|---|
| `Backend/Passes/Boundary.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/CompilerProofChecks.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/CoreBoundary.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/Divergence.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/EmittedTail.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/Frame.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/LoopBoundary.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/LoopReframedCompletion.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/LoopReframedCompletionDraftAxioms.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/LoopReframedFailureControls.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/LoopScopeApplication.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/LoopScopeControls.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/LoopScopeObservations.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/LoopScopeTerminal.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/LoopScopeTrace.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/LoopSequence.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/MappedSequence.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/MappedTail.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/MemoryCallBoundary.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/MemoryCallControls.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/ReframedFailureDraftAxioms.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/ReframedFailureWitness.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/ReframedLoops.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/ReframedSequence.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/RevertWitness.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/Sequence.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/SourceTerminalFailure.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/Stack.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/TailLoop.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/TailMachine.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/TripleSequence.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/SourceAdditionValue.lean` | Bounded v09-compiler-passes checkpoint; typed scope and retained premises are in the module. |
| `Backend/Passes/SourceAdditionValueControls.lean` | Compilation/representation witnesses and wrapping, saved-tail and memory-observation controls for SourceAdditionValue. |
| `Backend/Passes/SourceAdditionValuePins.lean` | Standard-axiom reports for SourceAdditionValue transport and controls. |
| `Backend/Passes/RelatedMemoryCapture.lean` | Bounded v09-compiler-passes checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/Passes/RelatedMemoryCaptureControls.lean` | Bounded v09-compiler-passes checkpoint; typed scope and retained obligations are stated in the module. |

## V09 compiler-pass applications

| Module | Purpose |
|---|---|
| `Backend/Passes/AssignmentAdditionPass.lean`, `AssignmentAdditionControls.lean`, `AssignmentAdditionPins.lean` | Effectful Source assignment/addition through actual captured-prefix maps and value code, with pipeline-sensitive mixed-heap controls. |
| `Backend/Passes/AssignmentMultiplicationPass.lean`, `AssignmentMultiplicationControls.lean`, `AssignmentMultiplicationPins.lean` | Unchecked Source assignment/multiplication through actual capture maps and compiled values, pipeline and unmasked-code controls. |
| `Backend/Passes/MemoryScopeBoundary.lean`, `MemoryScopeControls.lean`, `MemoryScopeAllocation.lean`, `MemoryScopePins.lean` | Exact physical scope cost/Input/maps, actual local-slot reuse and reached failure, positive allocation and axiom guards. |
| `Backend/Passes/MemoryCallScopeBoundary.lean`, `MemoryCallScopeControls.lean`, `MemoryCallScopeObservations.lean`, `MemoryCallScopeFailures.lean`, `MemoryCallScopePins.lean` | Expanded-call scope Input equivalence, private bounds/cost/maps, actual old-alias consumer, failure-prefix transport and complete fixture observations. |
| `Backend/Passes/CompilerCallScopeRecognition.lean`, `CompilerCallScopeControls.lean`, `CompilerCallScopePins.lean` | Actual public scoped-call selection, checked Input/resource/fragment projections, correlated consumer composition and complete runtime controls. |
| `Backend/Passes/CompilerWholeScope.lean`, `CompilerWholeScopeControls.lean`, `CompilerWholeScopePins.lean` | Actual public whole-fixture recognition, physical Input/output and exact allocator growth, with independently typed scope contrast. |
| `Backend/Passes/CompilerScopedFailure{,Pins}.lean` | Actual public whole scoped-call failure certificates, reached costs and arbitrary saved tails. |
| `Backend/Passes/EffectfulConditional{Assignment,Controls,Pins}.lean` | Effectful conditional-expression Source/context transport, compiled captures and actual wrong-order controls. |
| `Backend/Passes/RelatedMemoryCapturePins.lean` | Exact standard-axiom guards for initial Source context alignment, reference capture and selected-map pointer readback. |
| `Backend/Passes/RelatedStorageCapture{,Controls,Pins}.lean` | Plain core storage-alias context transport and symbolic-slot capture/readback. |
| `Backend/Passes/AssignmentAdditionPins.lean` | Exact observed standard-only axiom guards for the corresponding compiler-pass proofs. |
| `Backend/Passes/AssignmentMultiplicationPins.lean` | Exact observed standard-only axiom guards for the corresponding compiler-pass proofs. |
| `Backend/Passes/CompilerCallScopePins.lean` | Exact observed standard-only axiom guards for the corresponding compiler-pass proofs. |
| `Backend/Passes/CompilerWholeScopePins.lean` | Exact observed standard-only axiom guards for the corresponding compiler-pass proofs. |
| `Backend/Passes/MemoryCallScopeFailures.lean` | Reached argument/body failure and unreachable-suffix transport for expanded calls under a scope. |
| `Backend/Passes/MemoryCallScopeObservations.lean` | Complete emitted scope/call/consumer observations and slot-reuse controls. |
| `Backend/Passes/MemoryCallScopePins.lean` | Exact observed standard-only axiom guards for the corresponding compiler-pass proofs. |
| `Backend/Passes/MemoryScopeAllocation.lean` | Inhabited positive allocation across scope exit with exact allocator ownership. |
| `Backend/Passes/MemoryScopePins.lean` | Exact observed standard-only axiom guards for the corresponding compiler-pass proofs. |
| `Backend/Passes/CheckedAdditionCapture.lean` | Public checked-add compilation with fresh capture, full mapped output and shared tails. |
| `Backend/Passes/CheckedAdditionCaptureControls.lean` | Populated heap/caller capture and overflow controls with complete ordered observations. |
| `Backend/Passes/CheckedAdditionCapturePins.lean` | Standard-only axiom guards for checked-add capture headlines. |
| `Backend/Passes/CheckedAdditionReachedOverflow.lean` | Selected two-stage checked-add execution with actual mapped prefix and derived reached-overflow Input. |
| `Backend/Passes/CheckedAdditionReachedOverflowControls.lean` | MAX capture then doubling overflow; complete physical prefix and order/frame controls. |
| `Backend/Passes/CheckedAdditionReachedOverflowPins.lean` | Exact standard-only axiom guards for reached checked-add overflow. |
| `Backend/Passes/CheckedAdditionSequenceSuccess.lean` | Two successful public checked-add captures with both actual mapped outputs and exact second-guard terminal iff. |
| `Backend/Passes/CheckedAdditionSequenceSuccessControls.lean` | Dependent16→23 capture, complete cells/readback, both guards and negative controls. |
| `Backend/Passes/CheckedAdditionSequenceSuccessPins.lean` | Exact standard-only axiom guards for successful checked-add sequencing. |
| `Backend/Passes/MemoryJoinCost.lean` | Exact reached allocation-cell cost for intrinsic/public compiler joins and suffix capacity transport. |
| `Backend/Passes/MemoryJoinCostControls.lean` | Inhabited5+4 allocation budget with actual selected-map suffix Input and unreachable allocation failure control. |
| `Backend/Passes/MemoryJoinCostPins.lean` | Standard-only axiom guards for exact allocation-prefix composition. |
| `Backend/Passes/MemoryJoinedAllocation.lean` | Actual public joined allocation execution with full output, both maps, old-reference identity and nine-cell growth. |
| `Backend/Passes/MemoryJoinedAllocationControls.lean` | Complete fresh-array/old-state observations, public selection, saved tails and map/cursor negatives. |
| `Backend/Passes/MemoryJoinedAllocationPins.lean` | Exact standard-only axioms for joined allocation execution and controls. |
| `Backend/Passes/AllocatedReferenceRead.lean` | Actual selected-map fresh-reference reader and reached old-alias bounds failure after allocating join. |
| `Backend/Passes/AllocatedReferenceReadControls.lean` | Complete memory observations, returned-word/saved-tail controls and public receiver selection. |
| `Backend/Passes/AllocatedReferenceReadPins.lean` | Exact standard-only axioms for post-allocation value sequencing. |
| `Backend/Passes/MemoryJoinFrame.lean` | Exact legacy-memory joined static frame/Input equivalence and derived reached mapped boundary link. |
| `Backend/Passes/MemoryJoinFrameControls.lean` | Actual allocating public admission, scoped slot reuse and static-frame refusal after failure. |
| `Backend/Passes/MemoryJoinFramePins.lean` | Exact standard-only axioms for joined memory admission and controls. |
| `Backend/Passes/MemoryTripleAdmission.lean` | Both dependent memory links derived from one original public three-stage joined admission. |
| `Backend/Passes/MemoryTripleAdmissionControls.lean` | Two allocations and fresh-length capture; three shared maps, both associations and reached failure controls. |
| `Backend/Passes/MemoryTripleAdmissionPins.lean` | Exact standard-only axioms for three-stage admission and inhabited clients. |

| `Solidity/Backend/Passes/MemoryJoinedOutput.lean` | Full public legacy-memory joined output with the actual selected suffix map and reached cost. |
| `Solidity/Backend/Passes/MemoryJoinedOutputControls.lean` | Actual allocation/allocation/capture whole output over saved tails and publicly recognized reached failure. |
| `Solidity/Backend/Passes/MemoryJoinedOutputPins.lean` | Exact standard-only joined-output headline axiom guards. |
