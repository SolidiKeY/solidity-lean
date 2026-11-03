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


| `Backend/Passes/AssignmentAdditionPass.lean`, `AssignmentAdditionControls.lean`, `AssignmentAdditionPins.lean` | Effectful Source assignment/addition through actual captured-prefix maps and value code, with pipeline-sensitive mixed-heap controls. |

| `Backend/Passes/AssignmentMultiplicationPass.lean`, `AssignmentMultiplicationControls.lean`, `AssignmentMultiplicationPins.lean` | Unchecked Source assignment/multiplication through actual capture maps and compiled values, pipeline and unmasked-code controls. |

| `Backend/Passes/MemoryScopeBoundary.lean`, `MemoryScopeControls.lean`, `MemoryScopeAllocation.lean`, `MemoryScopePins.lean` | Exact physical scope cost/Input/maps, actual local-slot reuse and reached failure, positive allocation and axiom guards. |

| `Backend/Passes/MemoryCallScopeBoundary.lean`, `MemoryCallScopeControls.lean`, `MemoryCallScopeObservations.lean`, `MemoryCallScopeFailures.lean`, `MemoryCallScopePins.lean` | Expanded-call scope Input equivalence, private bounds/cost/maps, actual old-alias consumer, failure-prefix transport and complete fixture observations. |

| `Backend/Passes/CompilerCallScopeRecognition.lean`, `CompilerCallScopeControls.lean`, `CompilerCallScopePins.lean` | Actual public scoped-call selection, checked Input/resource/fragment projections, correlated consumer composition and complete runtime controls. |

| `Backend/Passes/CompilerWholeScope.lean`, `CompilerWholeScopeControls.lean`, `CompilerWholeScopePins.lean` | Actual public whole-fixture recognition, physical Input/output and exact allocator growth, with independently typed scope contrast. |

| `Backend/Passes/CompilerScopedFailure{,Pins}.lean` | Actual public whole scoped-call failure certificates, reached costs and arbitrary saved tails. |

| `Backend/Passes/EffectfulConditional{Assignment,Controls,Pins}.lean` | Effectful conditional-expression Source/context transport, compiled captures and actual wrong-order controls. |

| `Backend/Passes/RelatedMemoryCapture{,Controls,Pins}.lean` | Initial Source context alignment through actual reference capture and selected-map pointer readback. |

| `Backend/Passes/RelatedStorageCapture{,Controls,Pins}.lean` | Plain core storage-alias context transport and symbolic-slot capture/readback. |
