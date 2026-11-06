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
| `Backend/InternalFlow/RuntimeFrameV3ScalarRecursiveCall.lean` | Bounded v12-flow-calls checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/InternalFlow/RuntimeFrameV3ScalarRecursiveSource.lean` | Bounded v12-flow-calls checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/Passes/RelatedStorageCapture.lean` | Bounded v09-compiler-passes checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/Passes/RelatedStorageCaptureControls.lean` | Bounded v09-compiler-passes checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/Passes/ReturnedStorageCapture.lean` | Bounded v09-compiler-passes checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/Passes/ReturnedStorageCaptureControls.lean` | Bounded v09-compiler-passes checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/InternalFlow/RuntimeFrameV3ScalarSourceCheck.lean` | Bounded v12-flow-calls checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/InternalFlow/RuntimeFrameV3ScalarSourceCheckLaws.lean` | Bounded v12-flow-calls checkpoint; typed scope and retained obligations are stated in the module. |
| `Optimizer/Controls.lean` | Bounded vo1-optimizer checkpoint; typed scope and retained obligations are stated in the module. |
| `Optimizer/Laws.lean` | Bounded vo1-optimizer checkpoint; typed scope and retained obligations are stated in the module. |
| `Optimizer/Pass.lean` | Bounded vo1-optimizer checkpoint; typed scope and retained obligations are stated in the module. |
| `Optimizer/RoadmapComposition.lean` | Bounded vo1-optimizer checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/InternalFlow/RuntimeFrameScopedSource.lean` | Bounded v12-flow-calls checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/InternalFlow/RuntimeFrameV3RecursiveScopeCheck.lean` | Bounded v12-flow-calls checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/Passes/BitwiseValueContext.lean` | Bounded v09-compiler-passes checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/Passes/BitwiseValueContextControls.lean` | Bounded v09-compiler-passes checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/Passes/ValueReflection.lean` | Bounded v09-compiler-passes checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/InternalFlow/RuntimeFrameV3FrozenScopeFamily.lean` | The exact frozen recursiveSource constructor family with scoped scalar turns and the UNCHANGED Prog.recBase. |
| `Backend/InternalFlow/RuntimeFrameV3RecursiveScopeLaws.lean` | Small construction boundaries for actual scoped recursive quotations. |
| `Backend/InternalFlow/RuntimeFrameV3ScalarRecursiveAgreement.lean` | Successful quotation coherence for actual scalar-result recursion, including callers outside the inhabited successful controls. |
| `Backend/Passes/MemoryScopeAllocation.lean` | Scoped proofs and retained obligations for MemoryScopeAllocation. |
| `Backend/Passes/MemoryScopeBoundary.lean` | Scope exit keeps actual emitted code, reached cost and selected map. |
| `Backend/InternalFlow/RuntimeFrameV3EffectfulScalarSource.lean` | Bounded v12-flow-calls checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/InternalFlow/RuntimeFrameV3EffectfulSourceCheck.lean` | Bounded v12-flow-calls checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/Passes/TupleReturnConsumerControls.lean` | Bounded v09-compiler-passes checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/InternalFlow/RuntimeFrameV3ScalarParentRestore.lean` | Parent restore for scalar frames where the saved reference equals the live cell; only the counter changes. Not a general reference restore. |
| `Backend/InternalFlow/RuntimeFrameV3ScalarUnwind.lean` | Bounded v12-flow-calls checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/Passes/MemoryCallScopeControls.lean` | Bounded v09-compiler-passes checkpoint; typed scope and retained obligations are stated in the module. |
