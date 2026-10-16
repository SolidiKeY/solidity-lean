import Solidity.TestSuite.ScopedProblems

/-! Unannotated upstream loops use automatic `whileUnwind` and the existing
bounded proof search, including symbolic branch refutation from storage facts. -/

open Solidity
open scoped Scoped

/-- The unannotated counting loop reaches three. -/
theorem Solkey.TestSuite.whileCountsUp.proved : ⊢ Solkey.TestSuite.whileCountsUp.problem := by
  sol_prove (steps := 512)

/-- A local declared in the loop body is fresh each iteration. -/
theorem Solkey.TestSuite.whileBodyDeclaresLocal.proved :
    ⊢ Solkey.TestSuite.whileBodyDeclaresLocal.problem := by
  sol_prove (steps := 512)

/-- Breaking at four leaves the outer counter at four. -/
theorem Solkey.TestSuite.whileBreakLeavesLoop.proved :
    ⊢ Solkey.TestSuite.whileBreakLeavesLoop.problem := by
  sol_prove (steps := 512)

/-- Continue skips only the remainder of its while iteration. -/
theorem Solkey.TestSuite.whileContinueSkipsRest.proved :
    ⊢ Solkey.TestSuite.whileContinueSkipsRest.problem := by
  sol_prove (steps := 512)

/-- Continue in a for loop still executes the update. -/
theorem Solkey.TestSuite.forContinueStillUpdates.proved :
    ⊢ Solkey.TestSuite.forContinueStillUpdates.problem := by
  sol_prove (steps := 512)

/-- A for-loop break suppresses the following counter update. -/
theorem Solkey.TestSuite.forBreakKeepsCounter.proved :
    ⊢ Solkey.TestSuite.forBreakKeepsCounter.problem := by
  sol_prove (steps := 512)

/-- Do-while executes its body before the first guard. -/
theorem Solkey.TestSuite.doWhileRunsBodyFirst.proved :
    ⊢ Solkey.TestSuite.doWhileRunsBodyFirst.problem := by
  sol_prove (steps := 512)

/-- A required storage length bounds the loop that writes the array. -/
theorem Solkey.TestSuite.forWritesStorageArray.proved :
    ⊢ Solkey.TestSuite.forWritesStorageArray.problem := by
  sol_prove (steps := 512)

/-- A return exits both nested loops and leaves their caller's result intact. -/
theorem Solkey.TestSuite.returnLeavesNestedLoops.proved :
    ⊢ Solkey.TestSuite.returnLeavesNestedLoops.problem := by
  sol_prove (steps := 1024)

/-- The framed counting invariant proves the final array-length equality. -/
theorem Solkey.TestSuite.invariantForCountsArrayLength.proved :
    ⊢ Solkey.TestSuite.invariantForCountsArrayLength.problem := by
  sol_prove (steps := 256)
  all_goals sol_leaf
  all_goals sol_close
