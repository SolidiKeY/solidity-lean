import Solidity.TestSuite.MemoryLoopReplay.Discover09
open scoped Solidity.Scoped
-- A real fully discovered checkpoint is not yet an assembled proof.
resume_memory_replay Solkey.TestSuite.returnLeavesNestedLoops.problem
example : Solidity.Proves Solkey.TestSuite .all [] .nil .tt := by
  fail_if_success finish_memory_replay
  exact .closeTrue rfl

-- Nonempty residual leaves have no replay rule in this helper.
resume_memory_replay Solkey.TestSuite.returnLeavesNestedLoops.problem
run_elab do
  let some j ← Solidity.Seq.MemoryReplay.job.get | throwError "missing test checkpoint"
  let hints := j.hints.set! 0 {j.hints[0]! with residual := true}
  let rejected ← Lean.tryCatchRuntimeEx (do
    let _ ← Solidity.Seq.MemoryReplay.expected {j with hints} 0
    pure false) (fun _ => pure true)
  unless rejected do throwError "residual-leaf proposal incorrectly accepted"
  Solidity.Seq.MemoryReplay.job.set none
