import Solidity.TestSuite.ScopedProblems
import Solidity.TestSuite.Derived17MemoryLoop
import Solidity.TestSuite.MemoryLoopReplay.Refusals


open Solidity
open scoped Scoped

theorem Solkey.TestSuite.whileCountsUp.proved : ⊢ Solkey.TestSuite.whileCountsUp.problem := by
  sol_prove (steps := 512)

theorem Solkey.TestSuite.whileBodyDeclaresLocal.proved :
    ⊢ Solkey.TestSuite.whileBodyDeclaresLocal.problem := by
  sol_prove (steps := 512)

theorem Solkey.TestSuite.whileBreakLeavesLoop.proved :
    ⊢ Solkey.TestSuite.whileBreakLeavesLoop.problem := by
  sol_prove (steps := 512)

theorem Solkey.TestSuite.whileContinueSkipsRest.proved :
    ⊢ Solkey.TestSuite.whileContinueSkipsRest.problem := by
  sol_prove (steps := 512)

theorem Solkey.TestSuite.forContinueStillUpdates.proved :
    ⊢ Solkey.TestSuite.forContinueStillUpdates.problem := by
  sol_prove (steps := 512)

theorem Solkey.TestSuite.forBreakKeepsCounter.proved :
    ⊢ Solkey.TestSuite.forBreakKeepsCounter.problem := by
  sol_prove (steps := 512)

theorem Solkey.TestSuite.doWhileRunsBodyFirst.proved :
    ⊢ Solkey.TestSuite.doWhileRunsBodyFirst.problem := by
  sol_prove (steps := 512)

theorem Solkey.TestSuite.forWritesStorageArray.proved :
    ⊢ Solkey.TestSuite.forWritesStorageArray.problem := by
  sol_prove (steps := 512)

theorem Solkey.TestSuite.invariantForCountsArrayLength.proved :
    ⊢ Solkey.TestSuite.invariantForCountsArrayLength.problem := by
  sol_prove (steps := 256)
  all_goals sol_leaf
  all_goals sol_close
