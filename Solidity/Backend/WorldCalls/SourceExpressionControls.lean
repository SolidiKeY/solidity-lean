import Solidity.Backend.WorldCalls.SourceExpressionConsumer
import Solidity.Lowering.Readonly.Controls

/-! Actual resolved expression controls: postincrement before a nonself call,
declared-return caller failure, and permitted inherited-static read-only reentry.
These kernel Source observations are not native or compiler observations. -/
namespace Solidity.Backend.WorldCalls.SourceExpressionControls
open Solidity.Source Solidity.Source.SemanticsExamples
open Solidity.Lowering.Readonly
open Solidity.Backend.Passes.SourceCallControls
def targetC : RExpr EB [.address false] (.contract ⟨none, "C"⟩) :=
  .convExplicit (.local .here) (by decide)
theorem callOut_signature : dCallOut.fnSig EB = some ([.address false], []) := by rfl
def effectRun := (evalE (GB answerOnly) FC 9
  (.extCall targetC dCallOut callOut_signature (lit 0) effectArgs)).run before

theorem argument_before_call : readX effectRun.2.2 = some 4 := by decide
theorem argument_return : effectRun.1 = .ok RVal.unit := by rfl
theorem input_uses_old_value : effectRun.2.2.events.contains
    (.call ext (word 0) (selOf "callOut(address)" ++ wordBytes (toWord 3)) false) = true := by decide
theorem precapture_storage_not_restored : readX effectRun.2.2 ≠ readX before.2 := by decide

def dG : Decl := ⟨.function, "g", some "C", false, fn "g" .nil pUint⟩
theorem declared_g : EB.declOf .function ⟨some "C", "g"⟩ = some dG := by rfl
theorem signature_g : dG.fnSig EB = some ([], [uint]) := by rfl
def shortGlobal := GB (fun _ => .answer (.success [1]))
def shortRun := (evalE shortGlobal FC 9
  (.extCall targetC dG signature_g (lit 0) .nil)).run before
theorem malformed_declared_return : shortRun.1 = .error (.revert []) := by rfl
theorem callee_was_success :
    ((callAddr shortGlobal FC 8 ext (word 0) (selOf "g()") false).run (L0 EB,before.2)).1 =
      .ok (.success [1]) := by rfl
theorem caller_failure_storage : readX shortRun.2.2 = some 3 := by decide

def reentryRun := (evalE Controls.readOrigin.global Controls.readOrigin.frame
  (Controls.readOrigin.horizon+1)
  (.extCall Controls.readOrigin.target Controls.readOrigin.declaration
    Controls.readOrigin.signature Controls.readOrigin.value Controls.readOrigin.arguments)).run Controls.readOrigin.before
theorem reentry_returns : reentryRun.1 = .ok RVal.unit := by rfl
theorem reentry_not_suppressed :
    reentryRun.2.2.events.contains (.reentered (.success [])) = true := by decide
theorem reentry_expression_storage :
    (reentryRun.2.2.ex.world.accounts Controls.readOrigin.frame.this).storage =
      (Controls.readOrigin.after.2.ex.world.accounts Controls.readOrigin.frame.this).storage :=
  SourceExpressionConsumer.storage Controls.readOrigin rfl
end Solidity.Backend.WorldCalls.SourceExpressionControls
