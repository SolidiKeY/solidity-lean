<!-- Generated from docs/module-map/compiler-transport.d/ by scripts/coord-tools/fragments.sh; edit the fragments there, not this file. -->
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
| `Backend/Passes/AllocatedReferenceRead.lean` | Consume the actual newly allocated reference at its reached selected map. |
| `Backend/Passes/AllocatedReferenceReadPins.lean` | `#guard_msgs` axiom guards for the AllocatedReferenceRead results. |
| `Backend/Passes/AssignmentAdditionPass.lean` | Effectful unchecked addition with actual captured operand order. |
| `Backend/Passes/AssignmentAdditionPins.lean` | `#guard_msgs` axiom guards for the AssignmentAddition results. |
| `Backend/Passes/AssignmentMultiplicationPass.lean` | Effectful unchecked multiplication with actual captured operand order. |
| `Backend/Passes/AssignmentMultiplicationPins.lean` | `#guard_msgs` axiom guards for the AssignmentMultiplication results. |
| `Backend/Passes/CheckedAdditionCapture.lean` | Checked-add result capture through the actual public compiler. |
| `Backend/Passes/CheckedAdditionCapturePins.lean` | `#guard_msgs` axiom guards for the CheckedAdditionCapture results. |
| `Backend/Passes/CheckedAdditionReachedOverflow.lean` | A successful checked-add capture followed by a genuinely reached second checked-add overflow. |
| `Backend/Passes/CheckedAdditionReachedOverflowPins.lean` | `#guard_msgs` axiom guards for the CheckedAdditionReachedOverflow results. |
| `Backend/Passes/CheckedAdditionSequenceSuccess.lean` | Successful counterpart for the same public two-capture program. |
| `Backend/Passes/CheckedAdditionSequenceSuccessPins.lean` | `#guard_msgs` axiom guards for the CheckedAdditionSequenceSuccess results. |
| `Backend/Passes/ComparisonReferenceCapture.lean` | A publicly selected runtime comparison chooses an actual reference and captures it. |
| `Backend/Passes/CompilerCallScopePins.lean` | `#guard_msgs` axiom guards for the CompilerCallScope results. |
| `Backend/Passes/CompilerCallScopeRecognition.lean` | A concrete public compiler result is used directly. |
| `Backend/Passes/CompilerScopedFailure.lean` | Whole public recognition of the existing scoped argument/body failure fixtures. |
| `Backend/Passes/CompilerScopedFailurePins.lean` | `#guard_msgs` axiom guards for the CompilerScopedFailure results. |
| `Backend/Passes/CompilerWholeScope.lean` | Concrete whole-program public recognition for the existing allocating scoped-call fixture. |
| `Backend/Passes/CompilerWholeScopePins.lean` | `#guard_msgs` axiom guards for the CompilerWholeScope results. |
| `Backend/Passes/DeferredCondition.lean` | Compile an existing deferred Boolean operand without reading its value again after its private context is dropped. |
| `Backend/Passes/DeferredConditionFailure.lean` | Exact internal failure alternatives for existing deferred Boolean operands. |
| `Backend/Passes/EffectfulConditionalAssignment.lean` | The published effectful conditional expression, its actual compiled prefix, and captured-result readback. |
| `Backend/Passes/EffectfulConditionalPins.lean` | `#guard_msgs` axiom guards for the EffectfulConditional results. |
| `Backend/Passes/FramedMemoryBoundary.lean` | The published scalar framed-lowering interface keeps all nonstack fields. |
| `Backend/Passes/MemoryAssociation.lean` | Association transport for actual legacy-memory compiler selections. |
| `Backend/Passes/MemoryAssociationPins.lean` | `#guard_msgs` axiom guards for the MemoryAssociation results. |
| `Backend/Passes/MemoryCallScopeBoundary.lean` | Scope transport for the expanded-call compiler branch. |
| `Backend/Passes/MemoryCallScopeFailures.lean` | Scoped call failure reached after the actual successful allocation prefix. |
| `Backend/Passes/MemoryCallScopeObservations.lean` | Heap/array observations of the scoped call controls. |
| `Backend/Passes/MemoryCallScopePins.lean` | `#guard_msgs` axiom guards for the MemoryCallScope results. |
| `Backend/Passes/MemoryJoinCost.lean` | Exact reached-prefix cost for the existing intrinsic program and public memory compiler join. |
| `Backend/Passes/MemoryJoinCostPins.lean` | `#guard_msgs` axiom guards for the MemoryJoinCost results. |
| `Backend/Passes/MemoryJoinFrame.lean` | Exact static frame and reached allocation admission for the public legacy memory compiler. |
| `Backend/Passes/MemoryJoinFramePins.lean` | `#guard_msgs` axiom guards for the MemoryJoinFrame results. |
| `Backend/Passes/MemoryJoinedAllocation.lean` | Execute the allocating suffix whose reached admission was proved by MemoryJoinCost. |
| `Backend/Passes/MemoryJoinedAllocationPins.lean` | `#guard_msgs` axiom guards for the MemoryJoinedAllocation results. |
| `Backend/Passes/MemoryJoinedOutput.lean` | Full legacy-memory output composition for an actual public joined certificate. |
| `Backend/Passes/MemoryJoinedOutputPins.lean` | `#guard_msgs` axiom guards for the MemoryJoinedOutput results. |
| `Backend/Passes/MemoryScopePins.lean` | `#guard_msgs` axiom guards for the MemoryScope results. |
| `Backend/Passes/MemoryTripleAdmission.lean` | Three public legacy-memory stages obtain both physical links from one original admitted joined Input. |
| `Backend/Passes/MemoryTripleAdmissionPins.lean` | `#guard_msgs` axiom guards for the MemoryTripleAdmission results. |
| `Backend/Passes/P12ConditionExecution.lean` | Consume the published request-specific P12 condition contract. |
| `Backend/Passes/P12MemoryCapture.lean` | Conditional consumer of the exact published P12 request. |
| `Backend/Passes/P12StorageCapture.lean` | Exact published P12 storage-capture fields, conditional on their producer. |
| `Backend/Passes/RelatedMemoryCapturePins.lean` | `#guard_msgs` axiom guards for the RelatedMemoryCapture results. |
| `Backend/Passes/RelatedStorageCapturePins.lean` | `#guard_msgs` axiom guards for the RelatedStorageCapture results. |
| `Backend/Passes/ReturnedMemoryCapture.lean` | A returned memory reference is read through the ACTUAL selected output map, including when the compiled program allocates it. |
| `Backend/Passes/ShiftCapture.lean` | Public shift selection followed by capture and old-count mutation. |
| `Backend/Passes/SignedDivisionCapture.lean` | Consume the published signed-division family, then capture its value before mutating the old divisor. |
| `Backend/Passes/SignedRemainderCapture.lean` | Capture a publicly selected signed remainder before zeroing the old divisor. |
| `Backend/Passes/SignedSubtractionCapture.lean` | Capture the public unchecked int256 subtraction result before changing the old subtrahend. |
| `Backend/Passes/TupleReturnConsumer.lean` | Consume the published checked mixed-tuple emitter through the existing Compilation.memoryCalls constructor and its ACTUAL returned map. |
| `Backend/Passes/UnsignedDependentCapture.lean` | Capture a quotient, then evaluate the next remainder at the ACTUAL new context: (a/d) % a. |
| `Backend/Passes/UnsignedDependentFailure.lean` | Immediate versus actually reached zero-divisor failure. |
| `Backend/Passes/UnsignedDependentScope.lean` | Scope exit after dependent quotient/remainder capture, followed by real slot reuse. |
| `Backend/Passes/UnsignedWidthCapture.lean` | Publicly selected low-bit cleanup, captured before clearing its operand. |
| `Backend/Passes/MachineSar.lean` | Signed `>>` in the memory compiler (`shr_int_inFrag`, `sarCode_simT` via `Evm.tail_simT`; machine lemmas in `Evm/Signed.lean`), agreement with the Scalar endpoint `intShr`, unclamped-`SAR` negative control and saturated positive witness. |
| `Backend/Passes/MachineSarPins.lean` | `#guard_msgs` axiom guards for the MachineSar results. |
| `Optimizer/CSE.lean` | O03 common-subexpression elimination: typed syntactic equality on pure values (`Val.pbeq_eq`), available-expression invariant; `ConstFold.Prog.cse_empty_runC`. |
| `Optimizer/ConstFold.lean` | O02 constant folding on the typed `Val`; failing operations kept; `Val.cfold_evalT` (equal result in every state). |
| `Optimizer/DeadCode.lean` | O02 dead code after halting statements (`Prog.cut`, `cut_scope`, `Prog.dce_runC`) and dead local stores (`Prog.dse_runC`). |
| `Optimizer/DeadStore.lean` | X06 dead store elimination: last store at a state variable or static memory slot wins (`sstore_dead_runC`, `mstore_dead_runC`, `Heap.writeAddr_writeAddr`); `Prog.dstore_runC`. |
| `Optimizer/Inline.lean` | O03 inlining of void internal calls with value arguments (`inlineBlock_runC` via `Prog.run_wk`); `ConstFold.Prog.inl_runC`. |
| `Optimizer/LICM.lean` | X06 loop-invariant code motion under the loop guard (`licm_runC`, `TLoop.hoist_run`; frame from `Prog.run_frame`/`Prog.run_keeps`); `Prog.licm_runC`. |
| `Optimizer/Loads.lean` | X06 redundant load elimination: static loads, root-separated storage and field-sensitive memory alias analysis; `Prog.rle_empty_runC`. |
| `Optimizer/Pipeline.lean` | Certified O02/O03 pipeline (`round`, `Prog.optimize n`): inline, propagate, simplify, fold, dead code, CSE, loads, dead stores, LICM, unused-variable elimination; `Prog.optimize_runC`. |
| `Optimizer/Propagate.lean` | O02 constant and copy propagation with a fact invariant on locals; `Prog.cprop_empty_runC`. |
| `Optimizer/Simplify.lean` | O02 solc-rule expression simplifier restricted to checked-safe identities; `Val.simp_evalT`, `Prog.simplify_runC`. |
| `Optimizer/StmtFold.lean` | Expression passes lifted to `Prog` (`ValPass`, `Prog.vopt_runC`), dead-branch/`require(true)`/`while(false)` elimination, `Prog.cfold_runC`. |
| `Optimizer/UnusedVar.lean` | O02 unused-variable elimination: proved strengthening (`Prog.str?_wk`) and `Prog.run_wk`; `Prog.uve_runC`. |
