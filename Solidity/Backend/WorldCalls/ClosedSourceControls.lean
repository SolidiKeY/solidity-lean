import Solidity.Lowering.Readonly.SourceAllHistoriesV2
import Solidity.Backend.WorldCalls.SourceCallHistoryControls

/-! Concrete all-value unknown Source calls and clients of CLOSED Source laws.
No argument-capture, frontend, Source/Core or native correspondence is inferred. -/
namespace Solidity.Backend.WorldCalls.ClosedSourceControls
open Solidity.Source Solidity.Source.SemanticsExamples
open Solidity.Lowering.Readonly
def entry : St EB := {HistoryRollbackControls.entry with ex := {HistoryRollbackControls.entry.ex with
  world := HistoryRollbackControls.entry.ex.world.set thisC ((HistoryRollbackControls.entry.ex.world.accounts thisC).withBalance (word 10))}}
def global (out : Solidity.Roadmap.Outcome) := GB (fun _ => .answer out)
def run (amount : Solidity.Roadmap.Word) (out : Solidity.Roadmap.Outcome) :=
  (callAddr (global out) FC 30 ext amount [4,5] false).run (L0 EB,entry)
def successRun := run (word 3) (.success [5,6])
def revertRun := run (word 3) (.revert [7,9])
def insufficient := run (word 11) (.success [5,6])
def balance (s : St EB) := (s.ex.world.accounts thisC).balance
def reentrant (out : Solidity.Roadmap.Outcome) :=
  (callAddr (GB (SourceCallHistoryControls.callee out)) FC 30 ext (word 3) [4,5] false).run (L0 EB,entry)
theorem successful_bytes : successRun.1 = .ok (.success [5,6]) := by rfl
theorem actual_debit : balance successRun.2.2 = 7 := by decide
theorem storage_after_debit : readX successRun.2.2 = some 4 := by decide
theorem journal_extends : successRun.2.2.ex.journal.length = entry.ex.journal.length+1 := by decide
theorem raw_revert : revertRun.1 = .ok (.revert [7,9]) := by rfl
theorem debit_rollback : balance revertRun.2.2 = 10 ∧ readX revertRun.2.2 = some 4 := by decide
theorem live_mark_retained : revertRun.2.2.ex.journal.length = entry.ex.journal.length := by decide
theorem insufficient_refused : insufficient.1 = .ok (.revert []) := by rfl
theorem insufficient_no_debit : balance insufficient.2.2 = 10 := by decide
theorem insufficient_no_call : insufficient.2.2.events = [] := by rfl
theorem reentrant_change : readX (reentrant (.success [1,2])).2.2 = some 5 := by decide
theorem reentrant_revert : readX (reentrant (.revert [7,9])).2.2 = some 4 ∧
    balance (reentrant (.revert [7,9])).2.2 = 10 := by decide
theorem inherited_value_halt :
    ((callAddr (global (.success [])) {FC with static := true} 30 ext (word 1) [] false).run (L0 EB,entry)).1 =
      .error (.revert []) := by rfl
theorem depth_before_value_guard :
    ((callAddr (global (.success [])) {FC with static := true, depth := 1024} 30 ext (word 1) [] false).run
      (L0 EB,entry)).1 = .ok (.revert []) := by rfl
theorem closed_positive_bound : SourceHistory.At (global (.success [1,2])) 30 :=
  SourceDispatchV2.all_at _ _
theorem closed_callbacks : EnvironmentHistory.CallbackHistories (global (.success [1,2])) true 30 :=
  SourceDispatchV2.all_callbacks _ _ _
theorem closed_storage :
    StaticJournal.SameStorage
      ((callAddr (global (.success [1,2])) FC 30 ext (word 0) [4,5] true).run (L0 EB,entry)).2.2.ex entry.ex :=
  SourceDispatchV2.static_call_storage _ _ _ _ _ _ _ _ rfl
theorem closed_reentrant_storage :
    StaticJournal.SameStorage
      ((callAddr (GB (SourceCallHistoryControls.callee (.success [1,2]))) FC 30 ext (word 0) [4,5] true).run
        (L0 EB,entry)).2.2.ex entry.ex :=
  SourceDispatchV2.static_call_storage _ _ _ _ _ _ _ _ rfl
end Solidity.Backend.WorldCalls.ClosedSourceControls
