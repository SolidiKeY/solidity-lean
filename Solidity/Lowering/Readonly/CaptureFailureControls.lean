import Solidity.Lowering.Readonly.CaptureFailures
import Solidity.Lowering.Readonly.ReceiverControls

/-! Inhabited source failures: exhausted receiver evaluation and no-code
admission after a real argument assignment. Capture rejection keeps the
post-argument local and does not execute the callee/environment strategy. -/
namespace Solidity.Lowering.Readonly.CaptureFailureControls
open Solidity.Source Solidity.Source.SemanticsExamples
open Solidity.Backend.Passes.SourceTypedCall
open Solidity.Backend.Passes.SourceCallControls (dCallOut)
open ReceiverControls (target arguments before after)

def noCode : Glob EB := { GB answerOnly with hasCode := fun _ _ => false }

theorem rejected_after_arguments :
    (evalE noCode FC 7 (.extCall target dCallOut ReceiverControls.signature (lit 0) arguments)).run before =
      (.error (.revert []), after) := by
  exact CaptureFailures.code_rejected noCode FC 6 dCallOut ReceiverControls.signature
    target (lit 0) arguments ext 0 (by decide) (.cons (.address (addr 4)) .nil)
    (wordBytes (toWord 4)) none before before before after after after
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)

theorem effect_not_rolled_back :
    after.1 = .cons (.address (addr 4)) .nil ∧ after.1 ≠ before.1 := by
  constructor
  · rfl
  · intro same
    cases same

theorem no_callee_events :
    ((evalE noCode FC 7 (.extCall target dCallOut ReceiverControls.signature (lit 0) arguments)).run before).2.2.events =
      before.2.events := by
  rw [rejected_after_arguments]
  rfl

theorem receiver_exhaustion :
    (evalE (GB answerOnly) FC 1
      (.extCall target dCallOut ReceiverControls.signature (lit 0) arguments)).run before =
      (.error .timeout, before) :=
  CaptureFailures.target_failed _ _ _ _ _ _ _ _ _ _ _ rfl

/-- The identical source argument is admitted when actual code presence is
supplied; this does not change its mutation or replace its receiver. -/
theorem admitted_control :
    CapturedAt (GB answerOnly) FC 6 target dCallOut ReceiverControls.signature (lit 0) arguments
      before after ReceiverControls.captured := ReceiverControls.actual_capture

end Solidity.Lowering.Readonly.CaptureFailureControls
