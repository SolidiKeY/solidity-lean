import Solidity.Backend.WorldCalls.ExternalCalls
import Solidity.Backend.WorldCalls.PaymentControl
import Solidity.Lowering.Readonly.FullCaptureControls

/-! Components of the external boundary inhabited with actual core runs.
The reference P10 Returndata-to-Source/target adapter is deliberately NOT
fabricated from a payment status or decoder success. -/
namespace Solidity.Backend.WorldCalls.ExternalControls
open Solidity.Source Solidity.Source.SemanticsExamples
open Solidity.Lowering.Readonly

/-- Actual reached CALL, independently of code-occurrence labels. -/
theorem reached_call :
    PaymentControl.code.full[PaymentControl.fetched_call.pc]? = some Evm.Instr.call :=
  PaymentControl.fetched_call.instruction

theorem executed_call : Evm.Instr.step .call PaymentControl.fetched_call.reached =
    PaymentControl.fetched_call.result := PaymentControl.fetched_call.execute

/-- Existing source invocation/decoder is inhabited without any external
Returndata relation being assumed to have an implementation. -/
theorem empty_declared_result :
    (evalE PaymentControl.origin.global PaymentControl.origin.frame (PaymentControl.origin.horizon + 1)
      (.extCall PaymentControl.origin.target PaymentControl.origin.declaration PaymentControl.origin.signature
        PaymentControl.origin.value PaymentControl.origin.arguments)).run PaymentControl.origin.before =
      (.ok RVal.unit, (PaymentControl.origin.after.1, PaymentControl.sourceFinal)) := by
  rw [CallerResume.invocation PaymentControl.origin _ _ PaymentControl.source_raw]
  rfl

/-- Actual canonical/malformed declared-return source controls remain intact. -/
theorem canonical_uint :
    (evalE (ResumeControls.global (.success (wordBytes (word 1)))) FC 7
      (.extCall ReceiverControls.target ResumeControls.dG ResumeControls.signature (lit 0) .nil)).run
      FullCaptureControls.before =
      (.ok (.val (.int 1 (by decide))),
        (FullCaptureControls.before.1, ResumeControls.final (.success (wordBytes (word 1))))) :=
  FullCaptureControls.full_canonical_return

theorem malformed_one_byte :
    (evalE (ResumeControls.global (.success [1])) FC 7
      (.extCall ReceiverControls.target ResumeControls.dG ResumeControls.signature (lit 0) .nil)).run
      FullCaptureControls.before =
      (.error (.revert []), (FullCaptureControls.before.1, ResumeControls.final (.success [1]))) :=
  FullCaptureControls.full_malformed_expression

end Solidity.Backend.WorldCalls.ExternalControls
