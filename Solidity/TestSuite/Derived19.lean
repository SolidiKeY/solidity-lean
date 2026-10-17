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
