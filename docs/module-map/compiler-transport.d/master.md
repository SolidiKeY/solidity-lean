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
