import Solidity.Backend.StructuredFlow.BranchSelector

/-! G36.01 relative-exit composition over actual existing instructions.
The caller supplies the exact skipped code. Source outcome/label/frame and G24
compilation facts are not inferred from a pending target skip. -/
namespace Solidity.Backend.StructuredFlow.Exit
open Solidity.Evm

def emit (distance : Nat) : List Instr := [.jump distance]

theorem run_skip (distance : Nat) (initial : Machine) :
    run (emit distance) initial = .ok initial distance := rfl

/-- Skipped instructions may write, revert or fault; none is executed. -/
theorem skips (skipped continuation : List Instr) (initial : Machine) :
    run (emit skipped.length ++ (skipped ++ continuation)) initial =
      run continuation initial := by
  rw [run_append_skip (run_skip skipped.length initial)]
  simpa only [Nat.add_zero, run] using exec_skip_append skipped continuation 0 initial

/-- A selected left exit crosses the emitter's jump-over-else, the else arm,
and the caller's skipped suffix. Every machine field at the real condition
post-state survives; the continuation retains its actual complete outcome. -/
theorem branch_left {condition right skipped continuation : List Instr}
    {initial post : Machine}
    (test : run condition initial = .ok (post.push (.val (bword true))) 0) :
    run ((Branch.emit condition (emit (right.length + skipped.length + 1)) right ++ skipped) ++
      continuation) initial = run continuation post := by
  have selected : run (Branch.emit condition
      (emit (right.length + skipped.length + 1)) right) initial = .ok post skipped.length := by
    rw [Branch.true_pending_skip (post := post) (skip := right.length + skipped.length)
      test (run_skip (right.length + skipped.length + 1) post)]
    exact exec_skip right skipped.length post
  rw [List.append_assoc, run_append_skip selected]
  simpa only [Nat.add_zero, run] using exec_skip_append skipped continuation 0 post
end Solidity.Backend.StructuredFlow.Exit
