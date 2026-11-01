import Solidity.Backend.InternalFlow.CompletedLoopFrame
import tests.«internal-flow».SuccessfulLoopFacts

/-! Close the source-frame bridge on the SAME successful C18 allocating loop.
The actual caller writer supplies the counterexample to an unconditional frame. -/
namespace Solidity.Backend.InternalFlow.CompletedLoopChecks
open Evm Evm.Memory PublishedLoopChecks SuccessfulLoop

def actualLoop : Stmt C Caller Caller := .loop .auto (condition true) SuccessfulLoop.body

theorem actual_loop : actualLoop.run callMid.st = .ok finalOut := by
  have singleton : (program true).run callMid.st = actualLoop.run callMid.st := by
    change TRun.seq actualLoop.runR TRun.nil callMid.st = actualLoop.runR callMid.st
    unfold TRun.seq
    cases actualLoop.runR callMid.st <;> rfl
  exact singleton.symm.trans source_run

/-- No target endpoint, desired frame or finite horizon is supplied. -/
theorem completed_frame : TGFrameM .view callMid.st finalOut.st finalOut.ext ∧
    TLocAgreeM finalOut.ext 0 (Prog.writesAt 0 SuccessfulLoop.body) callMid.st.env finalOut.st.env :=
  scoped_loop_completed_frame .view SuccessfulLoop.body allocation_body_within
    .auto (condition true) callMid.st finalOut actual_loop

theorem all_old_contents : Heap.Keeps finalOut.ext callMid.st.heap finalOut.st.heap :=
  completed_frame.1.keeps

theorem roots_and_transaction : finalOut.st.storage = callMid.st.storage ∧
    finalOut.st.net = callMid.st.net ∧ finalOut.st.tx = callMid.st.tx ∧
    finalOut.st.selfBalance = callMid.st.selfBalance :=
  ⟨(completed_frame.1.keepsSt (by decide)).1,
    (completed_frame.1.keepsSt (by decide)).2,completed_frame.1.tx,
    completed_frame.1.selfBalance (by decide)⟩

theorem writer_guard_refused : Prog.withinM .view followup = false := by decide +kernel

theorem writer_not_kept : ¬ Heap.Keeps usedOut.ext finalOut.st.heap usedOut.st.heap := by
  intro kept
  have equal := congrArg (fun obj => (MObj.elems .dyn obj)[1]?)
    (kept (returned.wk finalOut.ext))
  have old : (MObj.elems .dyn (MObj.wk usedOut.ext A
      (finalOut.st.heap.get (returned.wk finalOut.ext))))[1]? =
      some (indexValue (wmod 11)) := by decide +kernel
  dsimp only at equal
  rw [use_elements.1,old] at equal
  have bad := congrArg (fun v : PrimTy.uint.Denote => v.1) (Option.some.inj equal)
  change (99 : Int) = 11 at bad
  omega

#print axioms scoped_loop_completed_frame
#print axioms actual_loop
#print axioms completed_frame
#print axioms all_old_contents
#print axioms roots_and_transaction
#print axioms writer_guard_refused
#print axioms writer_not_kept
end Solidity.Backend.InternalFlow.CompletedLoopChecks
