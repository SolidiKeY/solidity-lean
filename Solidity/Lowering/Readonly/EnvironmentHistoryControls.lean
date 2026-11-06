import Solidity.Lowering.Readonly.EnvironmentHistory
import Solidity.Lowering.Readonly.EnvironmentCreditControls
import Solidity.Lowering.Readonly.EnvironmentControls

/-! Inhabited conditional-history clients. Exact one-step callback histories
are produced from real credit+exhausted-child runs, not a frame premise. A
separate strategy explicitly has only credits/answers, and changes balances.
Neither example produces general non-exhausted child histories. -/
namespace Solidity.Lowering.Readonly.EnvironmentHistoryControls
open Solidity.Source Solidity.Source.SemanticsExamples
open StaticJournal EnvironmentHistory EnvironmentSteps

/-- A real zero-horizon child retains the actual preceding credit state.
This discharges the bounded P1 input for one environment step, for any mode. -/
theorem one_step_children (global : Glob E) (mode : Bool) : CallbackHistories global mode 1 := by
  intro n bound depth state target sender value input requested code credited choice guard lookup creditRun
  have zero : n = 0 := by omega
  subst n
  have prior := credit_history target value (L0 E)
    (entered state target sender value input requested) (requested || mode)
  rw [creditRun] at prior
  exact prior

/-- This concrete strategy never requests a callback, independently of mode
or declaration metadata. Its credit/answer execution is still nonempty. -/
theorem credit_only_children (mode : Bool) (bound : Nat) :
    CallbackHistories (GB (EnvironmentCreditControls.strategy thisC (word 5))) mode bound := by
  intro n hn depth state target sender value input requested code credited choice
  simp only [GB, EnvironmentCreditControls.strategy] at choice
  split at choice <;> cases choice

theorem static_credit_history :
    History sB.ex true
      ((envLoop (GB (EnvironmentCreditControls.strategy thisC (word 5))) 2 1 true).run
        (L0 EB, sB)).2.2.ex :=
  loop _ true 2 (credit_only_children true 2) 1 sB

theorem static_credit_storage :
    SameStorage EnvironmentCreditControls.fundedFinal.ex sB.ex := by
  have kept := EnvironmentHistory.storage _ 2 1 sB (credit_only_children true 2)
  rw [EnvironmentCreditControls.static_credit_finishes] at kept
  exact kept

/-- A storage history does not entail balance equality, even while static. -/
theorem balance_frame_false :
    (EnvironmentCreditControls.fundedFinal.ex.world.accounts thisC).balance ≠
      (sB.ex.world.accounts thisC).balance := EnvironmentCreditControls.static_balance_changes.2

/-- A real callback attempt is present: this is not a callback-free input. -/
theorem exhausted_callback_history :
    History EnvironmentControls.start.ex true EnvironmentControls.credited.ex := by
  have h := loop EnvironmentControls.global true 1 (one_step_children _ true) 1 EnvironmentControls.start
  rw [EnvironmentControls.child_exhaustion] at h
  exact h

theorem exhausted_callback_keeps_storage :
    SameStorage EnvironmentControls.credited.ex EnvironmentControls.start.ex :=
  exhausted_callback_history.storage rfl

end Solidity.Lowering.Readonly.EnvironmentHistoryControls
