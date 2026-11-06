import Solidity.Lowering.Readonly.CallbackFrame
import Solidity.Lowering.Readonly.Controls

/-! Actual child writes/revert and static refusal from a live caller checkpoint.
These controls do not assert the still-open universal dispatch induction. -/
namespace Solidity.Lowering.Readonly.HistoryRollbackControls
open Solidity.Source Solidity.Source.SemanticsExamples

def global : Glob EB := GB (fun _ => .answer (.success []))
def entry : St EB := {sB with ex := sB.ex.apply Controls.writeOp}
def credited : St EB := {entry with ex := entry.ex.apply (.account thisC fun old => old.withBalance (word 5))}
def live := (entry.ex.journal.length, entry.logs.length, entry.heap)
def child (static : Bool) := (enterInstance global 20 thisC ext (word 0) (selOf "poke()") static "C" 2 live).run (L0 EB, credited)
def childFor (pipeline : Solidity.Roadmap.Pipeline) (static : Bool) :=
  (enterInstance {global with pipeline := pipeline} 20 thisC ext (word 0) (selOf "poke()") static "C" 2 live).run (L0 EB, credited)
def staleChild := (enterInstance global 20 thisC ext (word 0) (selOf "poke()") false "C" 2
  (0, entry.logs.length, entry.heap)).run (L0 EB, credited)
def dispatched (static : Bool) :=
  (dispatch global (Solidity.Backend.Passes.SourceCallFrame.childFrame thisC ext (word 0)
    (selOf "poke()") static "C" 2) 19 (selOf "poke()")).run (L0 EB, {credited with heap := Solidity.Source.Heap.empty})
def dirty : St EB := {credited with ex := credited.ex.apply (.account thisC fun old => old.withBalance (word 7))}

/-- Kernel observations of real writes/revert, inherited-static refusal and
live versus stale marks; no expected fixture or budget was changed. -/
theorem observations :
(Solidity.Lowering.Readonly.HistoryRollbackControls.child false).1 = .ok (.revert []) ∧
 Solidity.Source.SemanticsExamples.readX (Solidity.Lowering.Readonly.HistoryRollbackControls.child false).2.2 = some 4 ∧
 Solidity.Source.SemanticsExamples.readT (Solidity.Lowering.Readonly.HistoryRollbackControls.child false).2.2 = some 4 ∧
 (Solidity.Lowering.Readonly.HistoryRollbackControls.child true).1 = .ok (.revert []) ∧
 Solidity.Source.SemanticsExamples.readX (Solidity.Lowering.Readonly.HistoryRollbackControls.child true).2.2 = some 4 ∧
 Solidity.Source.SemanticsExamples.readX Solidity.Lowering.Readonly.HistoryRollbackControls.staleChild.2.2 = some 3 ∧
 Solidity.Source.SemanticsExamples.readX Solidity.Lowering.Readonly.HistoryRollbackControls.entry = some 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- Distinguish an ordinary child's two writes from static refusal BEFORE
rollback, rather than inferring refusal merely from equal final values. -/
theorem mechanism :
(Solidity.Lowering.Readonly.HistoryRollbackControls.dispatched false).2.2.ex.journal.length =
 Solidity.Lowering.Readonly.HistoryRollbackControls.credited.ex.journal.length + 2 ∧
 (Solidity.Lowering.Readonly.HistoryRollbackControls.dispatched true).2.2.ex.journal.length =
 Solidity.Lowering.Readonly.HistoryRollbackControls.credited.ex.journal.length := by decide

/-- Both existing Source pipelines execute the same checkpoint/refusal control. -/
theorem pipelines :
∀ pipeline : Solidity.Roadmap.Pipeline,
 (Solidity.Lowering.Readonly.HistoryRollbackControls.childFor pipeline false).1 = .ok (.revert []) ∧
 Solidity.Source.SemanticsExamples.readX (Solidity.Lowering.Readonly.HistoryRollbackControls.childFor pipeline false).2.2 = some 4 ∧
 Solidity.Source.SemanticsExamples.readT (Solidity.Lowering.Readonly.HistoryRollbackControls.childFor pipeline false).2.2 = some 4 ∧
 (Solidity.Lowering.Readonly.HistoryRollbackControls.childFor pipeline true).1 = .ok (.revert []) ∧
 Solidity.Source.SemanticsExamples.readX (Solidity.Lowering.Readonly.HistoryRollbackControls.childFor pipeline true).2.2 = some 4 := by
  intro pipeline
  cases pipeline <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rfl

end Solidity.Lowering.Readonly.HistoryRollbackControls
