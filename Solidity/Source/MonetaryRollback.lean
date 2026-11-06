import Solidity.Source.MonetaryExecution
import Solidity.Source.Hoare

/-! Actual monetary-operation rollback with exact caller-state restoration.
This is a selected Source execution law, not world/compiler adequacy or a
whole-program balance invariant. No transaction finalization is inferred. -/
namespace Solidity.Source.MonetaryExecution
open Solidity.Roadmap (Address Word)
variable {E : Env} {Γ : RCtx}

theorem mark_run (locals : Locals E.layout Γ) (state : St E) :
    (mark : EM E Γ (Nat × Nat × Heap E.layout)).run (locals,state) =
      (.ok (state.ex.journal.length,state.logs.length,state.heap),(locals,state)) := by rfl

theorem rollback_run (locals : Locals E.layout Γ) (state : St E)
    (saved : Nat × Nat × Heap E.layout) :
    (rollbackTo saved : EM E Γ Unit).run (locals,state) =
      (.ok (), (locals,{state with
        ex := state.ex.undoN (state.ex.journal.length - saved.1),
        logs := state.logs.drop (state.logs.length - saved.2.1)})) := by rfl

theorem rollback_preserves (locals : Locals E.layout Γ) (state : St E)
    (saved : Nat × Nat × Heap E.layout) (fit : state.ex.BalancesFit) :
    ((rollbackTo saved : EM E Γ Unit).run (locals,state)).2.2.ex.BalancesFit := by
  simp only [rollback_run]
  exact state.ex.undoN_balancesFit _ fit

/-- Capture the actual credit outcome, then explicitly undo to the actual
mark. Attempt alone retains post-state and performs no rollback. -/
def creditRollback (address : Address) (value : Word) : EM E Γ (Except Halt Unit) := do
  let saved ← mark
  let outcome ← EM.attempt (credit address value)
  rollbackTo saved
  pure outcome

theorem attempt_run {α : Type} (operation : EM E Γ α) (locals : Locals E.layout Γ)
    (state : St E) :
    (EM.attempt operation).run (locals,state) =
      (.ok (operation.run (locals,state)).1,(operation.run (locals,state)).2) := by rfl

/-- Full pre-state, including nonempty journal/log prefixes, heap aliases,
locals, function locals and resource cursor, is restored on both branches. -/
theorem creditRollback_run (locals : Locals E.layout Γ) (state : St E)
    (address : Address) (value : Word) :
    (creditRollback address value : EM E Γ (Except Halt Unit)).run (locals,state) =
      (.ok (if (state.ex.world.accounts address).balance + value.val < 2^256 then
        .ok () else .error (.revert [])),(locals,state)) := by
  simp only [creditRollback, Hoare.run_bind, mark_run, attempt_run, credit_run]
  by_cases guard : (state.ex.world.accounts address).balance + value.val < 2^256
  · simp only [guard, if_true, rollback_run, ExecState.journal_apply,
      Nat.add_sub_cancel_left, ExecState.undoN, ExecState.undo_apply,
      Nat.sub_self, List.drop_zero]
    rfl
  · simp only [guard, if_false, rollback_run,
      Nat.sub_self, ExecState.undoN, List.drop_zero]
    rfl

end Solidity.Source.MonetaryExecution

/-- info: 'Solidity.Source.MonetaryExecution.mark_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryExecution.mark_run
/-- info: 'Solidity.Source.MonetaryExecution.rollback_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryExecution.rollback_run
/-- info: 'Solidity.Source.MonetaryExecution.rollback_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryExecution.rollback_preserves
/-- info: 'Solidity.Source.MonetaryExecution.attempt_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryExecution.attempt_run
/-- info: 'Solidity.Source.MonetaryExecution.creditRollback_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryExecution.creditRollback_run
