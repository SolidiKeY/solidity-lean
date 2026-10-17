import Solidity.TestSuite.ScopedProblems

/-! Obligations new at solkey `473da8944c`: `&`'s operand order, loop jumps
under invariants, modifier continuations, the dangling-storage claims (an
empty push saves only the length) and shifts. -/

open Solidity
open scoped Scoped

theorem Solkey.TestSuite.bitAndOperandEvaluation.proved : ⊢ Solkey.TestSuite.bitAndOperandEvaluation.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.invariantForContinueRunsUpdate.proved : ⊢ Solkey.TestSuite.invariantForContinueRunsUpdate.problem := by
  sol_prove (steps := 128)
  case leaf1 =>
    sol_leaf
    sol_close
  case leaf2 =>
    sol_leaf
    sol_close

theorem Solkey.TestSuite.modifierRepeatedReturnAndLocals.proved : ⊢ Solkey.TestSuite.modifierRepeatedReturnAndLocals.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.modifierReentersArguments.proved : ⊢ Solkey.TestSuite.modifierReentersArguments.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.modifierLoopBodyReturnStaysInFrame.proved : ⊢ Solkey.TestSuite.modifierLoopBodyReturnStaysInFrame.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.modifierWhileJumps.proved : ⊢ Solkey.TestSuite.modifierWhileJumps.problem := by
  sol_prove (steps := 256)

theorem Solkey.TestSuite.modifierDoWhileJumps.proved : ⊢ Solkey.TestSuite.modifierDoWhileJumps.problem := by
  sol_prove (steps := 256)

theorem Solkey.TestSuite.testDeleteArrayLeavesDataPastLength.proved : ⊢ Solkey.TestSuite.testDeleteArrayLeavesDataPastLength.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.testDanglingReferenceSurvivesPush.proved : ⊢ Solkey.TestSuite.testDanglingReferenceSurvivesPush.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.testArrayCopyKeepsDestinationTail.proved : ⊢ Solkey.TestSuite.testArrayCopyKeepsDestinationTail.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.testDanglingInnerArrayReappearsAfterPush.proved : ⊢ Solkey.TestSuite.testDanglingInnerArrayReappearsAfterPush.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.testShiftLeftFitsUint8.proved : ⊢ Solkey.TestSuite.testShiftLeftFitsUint8.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.testUnsignedParameterNonnegative.proved : ⊢ Solkey.TestSuite.testUnsignedParameterNonnegative.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.bitAndOneValues.proved : ⊢ Solkey.TestSuite.bitAndOneValues.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.bitAndGeneralValues.proved : ⊢ Solkey.TestSuite.bitAndGeneralValues.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.testShiftRightNegativeRoundsDown.proved : ⊢ Solkey.TestSuite.testShiftRightNegativeRoundsDown.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.logicalAndStorageAssignment.proved : ⊢ Solkey.TestSuite.logicalAndStorageAssignment.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.logicalOrStorageAssignment.proved : ⊢ Solkey.TestSuite.logicalOrStorageAssignment.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.storageAssignmentValueNested.proved : ⊢ Solkey.TestSuite.storageAssignmentValueNested.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.storageAssignmentValueIndexOnce.proved : ⊢ Solkey.TestSuite.storageAssignmentValueIndexOnce.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.storageAssignmentValueRhsBeforeIndex.proved : ⊢ Solkey.TestSuite.storageAssignmentValueRhsBeforeIndex.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.logicalAndStorageAssignmentSkipsIndex.proved : ⊢ Solkey.TestSuite.logicalAndStorageAssignmentSkipsIndex.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.logicalOrStorageAssignmentSkipsIndex.proved : ⊢ Solkey.TestSuite.logicalOrStorageAssignmentSkipsIndex.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.arithmeticAssignmentValues.proved : ⊢ Solkey.TestSuite.arithmeticAssignmentValues.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.testShiftOperandEvaluation.proved : ⊢ Solkey.TestSuite.testShiftOperandEvaluation.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.arithmeticDiscardKeepsSideEffects.proved : ⊢ Solkey.TestSuite.arithmeticDiscardKeepsSideEffects.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.arithmeticDiscardKeepsZeroDivisorRevert.proved : ⊢ Solkey.TestSuite.arithmeticDiscardKeepsZeroDivisorRevert.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.storageArrayMethodReferences.proved : ⊢ Solkey.TestSuite.storageArrayMethodReferences.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.storageArrayMethodReferencesCallReceiver.proved : ⊢ Solkey.TestSuite.storageArrayMethodReferencesCallReceiver.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.storagePopReferenceOutOfBounds.proved : ⊢ Solkey.TestSuite.storagePopReferenceOutOfBounds.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.storagePopReferenceCallOutOfBounds.proved : ⊢ Solkey.TestSuite.storagePopReferenceCallOutOfBounds.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.memoryIndexWriteStorageRefOutOfBoundsReverts.proved : ⊢ Solkey.TestSuite.memoryIndexWriteStorageRefOutOfBoundsReverts.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.memoryIndexWriteStorageRefSourceOutOfBoundsReverts.proved : ⊢ Solkey.TestSuite.memoryIndexWriteStorageRefSourceOutOfBoundsReverts.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.arithmeticRemainderBoundAllSigns.proved : ⊢ Solkey.TestSuite.arithmeticRemainderBoundAllSigns.problem := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close

theorem Solkey.TestSuite.modifierSkippedPlaceholder.proved : ⊢ Solkey.TestSuite.modifierSkippedPlaceholder.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.modifierTakenPlaceholder.proved : ⊢ Solkey.TestSuite.modifierTakenPlaceholder.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.modifierReturnResumesOuterSuffix.proved : ⊢ Solkey.TestSuite.modifierReturnResumesOuterSuffix.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.conditionalCallee.proved : ⊢ Solkey.TestSuite.conditionalCallee.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.conditionalCalleeEffects.proved : ⊢ Solkey.TestSuite.conditionalCalleeEffects.problem := by
  sol_prove (steps := 128)
