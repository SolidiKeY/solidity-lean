import Solidity.Source.MonetaryRollback
import Solidity.Source.FailureMachineControls

/-! Inhabited actual Source controls with an existing heap alias, saved
function locals, event/log prefixes and nonempty persistent journal. -/
namespace Solidity.Source.MonetaryExecution.Controls
open Solidity.Roadmap (Address Word)
open FailureExecution.Controls (E caller)

def address : Address := ⟨9,by decide⟩
def value : Word := ⟨3,by decide⟩
def seed : St E := { FailureExecution.Controls.seed with
  ex := FailureExecution.Controls.seed.ex.apply
    (.account address (fun account => account.withBalance 17)) }
def wideSeed : St E := { seed with
  ex := seed.ex.apply (.account address (fun account => account.withBalance (2^256))) }

theorem seed_journal : seed.ex.journal.length = 1 := by rfl

theorem seed_alias : seed.heap.next = 1 := by rfl

theorem successful :
    (creditRollback address value : EM E [.bytes .memory,.bool] (Except Halt Unit)).run
      (caller,seed) = (.ok (.ok ()),(caller,seed)) := by
  have accepted : (seed.ex.world.accounts address).balance + value.val < 2^256 := by decide
  simp only [creditRollback_run, accepted, if_true]

theorem refused :
    (creditRollback address value : EM E [.bytes .memory,.bool] (Except Halt Unit)).run
      (caller,wideSeed) = (.ok (.error (.revert [])),(caller,wideSeed)) := by
  have rejected : ¬ (wideSeed.ex.world.accounts address).balance + value.val < 2^256 := by decide
  simp only [creditRollback_run, rejected, if_false]

/-- Attempt alone keeps the actual credited balance and new journal entry. -/
theorem capture_is_not_rollback :
    let result := (EM.attempt (credit address value) :
      EM E [.bytes .memory,.bool] (Except Halt Unit)).run (caller,seed)
    result.1 = .ok (.ok ()) ∧
    (result.2.2.ex.world.accounts address).balance = 20 ∧
    result.2.2.ex.journal.length = 2 := by
  have accepted : (seed.ex.world.accounts address).balance + value.val < 2^256 := by decide
  simp only [attempt_run, credit_run, accepted, if_true, ExecState.journal_apply]
  decide

/-- Reverting to the wrong zero mark destroys the retained prefix. This is
not the selected mark captured by creditRollback. -/
theorem wrong_mark_loses_prefix :
    let result := (rollbackTo (0,0,seed.heap) : EM E [.bytes .memory,.bool] Unit).run (caller,seed)
    result.2.2.ex.journal.length = 0 ∧ result.2.2.logs = [] ∧ seed.logs ≠ [] := by decide

/-- Equal numeric balance is not full journal restoration. Even a zero credit
has a real saved account entry before explicit rollback. -/
theorem zero_credit_still_journals :
    let result := (credit address ⟨0,by decide⟩ : EM E [.bytes .memory,.bool] Unit).run (caller,seed)
    (result.2.2.ex.world.accounts address).balance = 17 ∧
    result.2.2.ex.journal.length = 2 := by
  have accepted : (seed.ex.world.accounts address).balance + (0 : Nat) < 2^256 := by decide
  simp only [credit_run, accepted, if_true, ExecState.journal_apply]
  decide

/-- A genuine Source byte read after the captured rollback sees the original
full nonempty heap payload, not merely its length or a projected balance. -/
theorem continuation_reads_full_alias :
    ((do
      let outcome ← creditRollback address value
      let bytes ← heapBytes 0
      pure (outcome,bytes)) : EM E [.bytes .memory,.bool] (Except Halt Unit × List UInt8)).run
        (caller,seed) = (.ok (.ok (),[0xDE,0xAD]),(caller,seed)) := by
  rw [Hoare.run_bind, successful]
  rfl

end Solidity.Source.MonetaryExecution.Controls

/-- info: 'Solidity.Source.MonetaryExecution.Controls.seed_journal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryExecution.Controls.seed_journal
/-- info: 'Solidity.Source.MonetaryExecution.Controls.seed_alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryExecution.Controls.seed_alias
/-- info: 'Solidity.Source.MonetaryExecution.Controls.successful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryExecution.Controls.successful
/-- info: 'Solidity.Source.MonetaryExecution.Controls.refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryExecution.Controls.refused
/-- info: 'Solidity.Source.MonetaryExecution.Controls.capture_is_not_rollback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryExecution.Controls.capture_is_not_rollback
/-- info: 'Solidity.Source.MonetaryExecution.Controls.wrong_mark_loses_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryExecution.Controls.wrong_mark_loses_prefix
/-- info: 'Solidity.Source.MonetaryExecution.Controls.zero_credit_still_journals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryExecution.Controls.zero_credit_still_journals
/-- info: 'Solidity.Source.MonetaryExecution.Controls.continuation_reads_full_alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryExecution.Controls.continuation_reads_full_alias
