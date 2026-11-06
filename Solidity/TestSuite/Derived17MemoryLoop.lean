import Solidity.TestSuite.MemoryLoopReplay.Assemble09
open scoped Solidity.Scoped
example : Solidity.Proves Solkey.TestSuite .all [] .nil .tt := by
  fail_if_success finish_memory_replay
  exact .closeTrue rfl

resume_memory_replay Solkey.TestSuite.returnLeavesNestedLoops.problem
example : Solidity.Proves Solkey.TestSuite .all [] .nil .tt := by
  fail_if_success finish_memory_replay
  exact .closeTrue rfl

resume_memory_replay Solkey.TestSuite.returnLeavesNestedLoops.problem
/-- The original 1024-step proof, decomposed into kernel-checked shared equations. -/
theorem Solkey.TestSuite.returnLeavesNestedLoops.proved :
    ⊢ Solkey.TestSuite.returnLeavesNestedLoops.problem := by
  finish_memory_replay
