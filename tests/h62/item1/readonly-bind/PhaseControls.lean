import Solidity.Lowering.Readonly.CaptureFailureControls

/-! Actual evaluator timeout witnesses for two capture phases. -/
namespace Solidity.H62.ReadonlyBind.PhaseControls
open Solidity.Source Solidity.Source.SemanticsExamples
open Solidity.Lowering.Readonly
open Solidity.Backend.Passes.SourceCallControls (dCallOut)
open ReceiverControls (arguments before signature)

theorem value_timeout :
    (evalE (GB answerOnly) FC 2
      (.extCall (.this "C") dCallOut signature (lit 0) arguments)).run before =
      (.error .timeout, before) := by
  exact CaptureFailures.value_failed (GB answerOnly) FC 1 dCallOut signature
    (.this "C") (lit 0) arguments FC.this before before before .timeout
    (by rfl) (by rfl)

theorem arguments_timeout :
    (evalE (GB answerOnly) FC 3
      (.extCall (.this "C") dCallOut signature (lit 0) arguments)).run before =
      (.error .timeout, before) := by
  exact CaptureFailures.arguments_failed (GB answerOnly) FC 2 dCallOut signature
    (.this "C") (lit 0) arguments FC.this 0 (by decide)
    before before before before .timeout (by rfl) (by rfl) (by rfl)

end Solidity.H62.ReadonlyBind.PhaseControls
