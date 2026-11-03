import Solidity.Backend.WorldCalls.SourceExpressionFailure
import Solidity.Backend.WorldCalls.SourceIssuerControls

/-! Kernel Source controls distinguishing failed argument/capture from entered
call failure. No native, transaction rollback or target correspondence claim. -/
namespace Solidity.Backend.WorldCalls.SourceFailureControls
open Solidity.Source Solidity.Source.SemanticsExamples
open Solidity.Roadmap
open Solidity.Lowering.Readonly
open Solidity.Backend.Passes.SourceTypedCall
open Solidity.Backend.Passes.SourceCallControls
open SourceExpressionControls

def refusedCapture := (capture SourceIssuerControls.missingCode FC 8
  targetC dCallOut (lit 0) effectArgs).run before
def refusedExpression := (evalE SourceIssuerControls.missingCode FC 9
  (.extCall targetC dCallOut callOut_signature (lit 0) effectArgs)).run before

theorem capture_halt : refusedCapture.1 = .error (.revert []) := by rfl
theorem argument_write_retained : readX refusedCapture.2.2 = some 4 := by decide
theorem expression_error : refusedExpression.1 = .error (.revert []) := by rfl
theorem expression_keeps_prefix : readX refusedExpression.2.2 = some 4 := by decide
theorem no_call_event : refusedExpression.2.2.events = [] := by rfl

theorem decoder_failure_after_capture :
    ∃ after captured, CapturedAt shortGlobal FC 8 targetC dG signature_g (lit 0) .nil
      before after captured ∧
      (resume shortGlobal FC 8 dG [uint] captured).run after =
        (.error (.revert []),shortRun.2) := by
  have classification := SourceExpressionFailure.classify shortGlobal FC 8 dG signature_g
    targetC (lit 0) .nil before shortRun.2 (.revert [])
    (Prod.ext malformed_declared_return rfl)
  rcases classification with failed | resumed
  · have captured : (capture shortGlobal FC 8 targetC dG (lit 0) .nil).run before =
        (.ok ⟨ext,word 0,.nil,selOf "g()"⟩,before) := by rfl
    rw [captured] at failed
    cases failed
  · exact resumed

def revertOrigin : InvocationFrame.Invocation EB [.address false] ⟨none,"I"⟩ [] [] :=
  { Controls.origin with
    global := GB (fun _ => .answer (.revert [7,9]))
    execution := by rfl }
def revertExpression := (evalE revertOrigin.global revertOrigin.frame (revertOrigin.horizon+1)
  (.extCall revertOrigin.target revertOrigin.declaration revertOrigin.signature
    revertOrigin.value revertOrigin.arguments)).run revertOrigin.before
theorem callee_revert_bytes : revertExpression.1 = .error (.revert [7,9]) := by rfl
theorem revert_storage :
    (revertExpression.2.2.ex.world.accounts revertOrigin.frame.this).storage =
      (revertOrigin.after.2.ex.world.accounts revertOrigin.frame.this).storage :=
  SourceExpressionConsumer.storage revertOrigin rfl
end Solidity.Backend.WorldCalls.SourceFailureControls
