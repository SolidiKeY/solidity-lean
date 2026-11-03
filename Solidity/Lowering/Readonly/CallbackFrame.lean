import Solidity.Lowering.Readonly.HistoryRollback
import Solidity.Lowering.Readonly.EnvironmentHistory
import Solidity.Backend.Passes.SourceCallFrame

/-! Source callback-frame induction step, using actual dispatch at the smaller
horizon and the live pre-credit checkpoint. No intrinsic P1 class is involved. -/
namespace Solidity.Lowering.Readonly.CallbackFrame
open Solidity.Source StaticJournal
variable {E : Env}

/-- The source-dispatch component needed at the preceding induction bound. -/
def DispatchHistory (global : Glob E) (n : Nat) : Prop :=
  ∀ (frame : Fr) (input : Solidity.Roadmap.Bytes) (state : St E),
    History state.ex frame.static ((dispatch global frame n input).run (L0 E, state)).2.2.ex

/-- Actual child entry, including a reverting child. The prefix starts at
its caller's pre-credit checkpoint; rollback cannot erase earlier effects. -/
theorem enter_history (global : Glob E) (n : Nat) (smaller : DispatchHistory global n)
    (entry credited : St E) (a sender : Solidity.Roadmap.Address)
    (value : Solidity.Roadmap.Word) (input : Solidity.Roadmap.Bytes) (mode : Bool)
    (code : String) (depth : Nat) (prior : History entry.ex mode credited.ex) :
    History entry.ex mode
      ((enterInstance global (n + 1) a sender value input mode code depth
        (entry.ex.journal.length, entry.logs.length, entry.heap)).run (L0 E, credited)).2.2.ex := by
  let frame := Solidity.Backend.Passes.SourceCallFrame.childFrame a sender value input mode code depth
  have body := smaller frame input {credited with heap := Heap.empty}
  rcases execution : (dispatch global frame n input).run
      (L0 E, {credited with heap := Heap.empty}) with ⟨result, locals, dirty⟩
  rw [execution] at body
  have joined : History entry.ex mode dirty.ex := JournalLeaves.chain body entry.ex prior
  cases result with
  | ok bytes =>
    rw [Solidity.Backend.Passes.SourceCallFrame.enter_success global n a sender value input bytes mode code depth
      (entry.ex.journal.length, entry.logs.length, entry.heap) credited dirty locals execution]
    exact joined
  | error halt =>
    cases halt with
    | revert bytes =>
      rw [Solidity.Backend.Passes.SourceCallFrame.enter_revert global n a sender value input bytes mode code depth
        (entry.ex.journal.length, entry.logs.length, entry.heap) credited dirty locals execution]
      change History entry.ex mode (dirty.ex.undoN (dirty.ex.journal.length - entry.ex.journal.length))
      rw [HistoryRollback.rewind joined]
      exact .start _ _
    | stuck why =>
      rw [Solidity.Backend.Passes.SourceCallFrame.enter_halt global n a sender value input mode code depth
        (entry.ex.journal.length, entry.logs.length, entry.heap) credited dirty locals (.stuck why)
        (by intro bytes; simp only [ne_eq, reduceCtorEq, not_false_eq_true]) execution]
      exact joined
    | timeout =>
      rw [Solidity.Backend.Passes.SourceCallFrame.enter_halt global n a sender value input mode code depth
        (entry.ex.journal.length, entry.logs.length, entry.heap) credited dirty locals .timeout
        (by intro bytes; simp only [ne_eq, reduceCtorEq, not_false_eq_true]) execution]
      exact joined

/-- Callback histories are a Source induction consequence, not a P1 class.
The dispatch component at strictly smaller bounds is retained verbatim. -/
theorem callbacks (global : Glob E) (mode : Bool) (bound : Nat)
    (dispatches : ∀ n, n < bound → DispatchHistory global n) :
    EnvironmentHistory.CallbackHistories global mode bound := by
  intro n below depth state target sender value input requested code credited choice guard lookup creditRun
  have prior := StaticJournal.credit_history target value (L0 E)
    (EnvironmentSteps.entered state target sender value input requested) (requested || mode)
  rw [creditRun] at prior
  cases n with
  | zero => exact prior
  | succ n =>
    exact enter_history global n (dispatches n (Nat.lt_trans (Nat.lt_succ_self n) below))
      state credited target sender value input (requested || mode) code (depth + 1) prior

/-- Actual base of the simultaneous Source history induction. -/
theorem dispatch_zero (global : Glob E) : DispatchHistory global 0 := by
  intro frame input state
  exact .start _ _

end Solidity.Lowering.Readonly.CallbackFrame
