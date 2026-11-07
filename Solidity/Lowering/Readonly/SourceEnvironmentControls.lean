import Solidity.Lowering.Readonly.SourceEnvironmentEffects
import Solidity.Lowering.Readonly.HistoryRollbackControls
import Solidity.Lowering.Readonly.SourceHistoryBase

/-! Actual environment moves, including read-only reentry and failed children.
Credits can change balances while static; storage is the preservation claim. -/
namespace Solidity.Lowering.Readonly.SourceEnvironmentControls
open Solidity.Source Solidity.Source.SemanticsExamples
open SourceHistory
def scripted (target : Solidity.Roadmap.Address) (value : Solidity.Roadmap.Word)
    (requested : Bool) (input : Solidity.Roadmap.Bytes)
    (answer : Solidity.Roadmap.Outcome := .success [1,2]) : Solidity.Roadmap.Strategy :=
  fun events => if events.isEmpty then .reenter target user value input requested else .answer answer
def readBody : RBody EB := body0 [] (.stmt (.expr (.state dX dX_ty)) .nil)
def readProgram : Program EB := { PB with body := fun d => if d.name = "cb" then some readBody else PB.body d }
def run (mode requested : Bool) (value : Solidity.Roadmap.Word := word 0)
    (input : Solidity.Roadmap.Bytes := selOf "cb()") (state : St EB := sB)
    (readonly : Bool := false) (depth : Nat := 1) (fuel : Nat := 30)
    (pipeline : Solidity.Roadmap.Pipeline := .legacy) :=
  let base := GB (scripted thisC value requested input)
  let program := if readonly then readProgram else PB
  (envLoop {base with prog := program, pipeline := pipeline} fuel depth mode).run (L0 EB, state)
def balance (s : St EB) := (s.ex.world.accounts thisC).balance
def ordinary := run false false
def inherited := run true false
def reading := run true false (readonly := true)
def requested := run false true
def rolled := run false false (word 5) (selOf "poke()") HistoryRollbackControls.entry
def creditRun (mode : Bool) (state : St EB := sB) :=
  (envLoop (GB (fun events => if events.isEmpty then .credit thisC (word 5) else .answer (.success [3])))
    10 1 mode).run (L0 EB, state)
def fullBalance : St EB :=
  {sB with ex := {sB.ex with world := sB.ex.world.set thisC ((sB.ex.world.accounts thisC).withBalance (word (2^256-1)))}}
def missing :=
  (envLoop (GB (scripted ext (word 0) false [])) 10 1 true).run (L0 EB, sB)
def rawRevert :=
  (envLoop (GB (fun _ => .answer (.revert [7,9]))) 1 1 true).run (L0 EB, sB)
theorem ordinary_answer : ordinary.1 = .ok (.success [1,2]) := by rfl
theorem ordinary_mutation : readX ordinary.2.2 = some 4 := by decide
theorem inherited_answer : inherited.1 = .ok (.success [1,2]) := by rfl
theorem inherited_kept : readX inherited.2.2 = some 3 := by decide
theorem inherited_child_refused : inherited.2.2.events.contains (.reentered (.revert [])) = true := by decide
theorem readonly_child_succeeds : reading.2.2.events.contains (.reentered (.success [])) = true := by decide
theorem readonly_kept : readX reading.2.2 = some 3 := by decide
theorem requested_child_refused : requested.2.2.events.contains (.reentered (.revert [])) = true := by decide
theorem requested_kept : readX requested.2.2 = some 3 := by decide
theorem rollback_prefix : readX rolled.2.2 = some 4 ∧ readT rolled.2.2 = some 4 := by decide
theorem rollback_balance : balance rolled.2.2 = 0 := by decide
theorem rollback_journal : rolled.2.2.ex.journal.length = HistoryRollbackControls.entry.ex.journal.length := by decide
theorem static_credit : balance (creditRun true).2.2 = 5 ∧ readX (creditRun true).2.2 = some 3 := by decide
theorem static_balance_not_frozen : balance (creditRun true).2.2 ≠ balance sB := by decide
theorem overflow_refused : (creditRun true fullBalance).1 = .error (.revert []) := by rfl
theorem missing_refused : missing.2.2.events.contains (.reentered (.revert [])) = true := by decide
theorem depth_refused : (run false false (depth := 1024)).2.2.events.contains (.reentered (.revert [])) = true := by decide
theorem static_value_refused : (run true false (word 1)).2.2.events.contains (.reentered (.revert [])) = true ∧
    balance (run true false (word 1)).2.2 = 0 := by decide
theorem raw_revert_data : rawRevert.1 = .ok (.revert [7,9]) := by rfl
theorem zero_exhausts : (run true false (fuel := 0)).1 = .error .timeout := by rfl
theorem child_exhausts : (run true false (fuel := 1)).1 = .error .timeout := by rfl
theorem both_pipelines : ∀ pipeline : Solidity.Roadmap.Pipeline,
    (run true false (readonly := true) (pipeline := pipeline)).2.2.events.contains (.reentered (.success [])) = true := by
  intro pipeline
  cases pipeline <;> decide
theorem actual_answer_client :
    Effect true (envLoop (GB (fun _ => .answer (.success [3]))) 1 1 true) := by
  exact envLoop_succ _ 0 (at_zero _) 1 true
end Solidity.Lowering.Readonly.SourceEnvironmentControls
