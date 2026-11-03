import Solidity.Backend.WorldCalls.SourceExpressionIssuer
import Solidity.Backend.WorldCalls.SourceExpressionControls

/-! Actual successful-expression issuance and refusal controls. These do not
supply native/target or whole-body provenance. -/
namespace Solidity.Backend.WorldCalls.SourceIssuerControls
open Solidity.Source Solidity.Source.SemanticsExamples
open Solidity.Roadmap
open Solidity.Lowering.Readonly
open Solidity.Backend.Passes.SourceTypedCall
open Solidity.Backend.Passes.SourceCallControls
open SourceExpressionControls

theorem argument_issued :
    ∃ after captured,
      CapturedAt (GB answerOnly) FC 8 targetC dCallOut callOut_signature (lit 0) effectArgs
        before after captured ∧
      (resume (GB answerOnly) FC 8 dCallOut [] captured).run after =
        (.ok RVal.unit,effectRun.2) :=
  SourceExpressionIssuer.capture_of_success (GB answerOnly) FC 8 dCallOut
    callOut_signature targetC (lit 0) effectArgs before effectRun.2 RVal.unit
    (Prod.ext argument_return rfl)

theorem static_expression_issued :
    ∃ after captured,
      CapturedAt Controls.readOrigin.global Controls.readOrigin.frame Controls.readOrigin.horizon
        Controls.readOrigin.target Controls.readOrigin.declaration Controls.readOrigin.signature
        Controls.readOrigin.value Controls.readOrigin.arguments Controls.readOrigin.before after captured ∧
      (reentryRun.2.2.ex.world.accounts Controls.readOrigin.frame.this).storage =
        (after.2.ex.world.accounts Controls.readOrigin.frame.this).storage :=
  SourceExpressionIssuer.storage_of_success Controls.readOrigin.global Controls.readOrigin.frame
    Controls.readOrigin.horizon Controls.readOrigin.declaration Controls.readOrigin.declared
    Controls.readOrigin.signature Controls.readOrigin.target Controls.readOrigin.value
    Controls.readOrigin.arguments Controls.readOrigin.before reentryRun.2 RVal.unit
    (Prod.ext reentry_returns rfl) rfl

def forged : Decl := ⟨.function,"callOut",some "C",false,
  .function (.ident "callOut") pAddr (some .pub) (some .view) .nil false none .nil
    (.some (.block .nil))⟩
theorem forged_is_view : forged.fnMut = some .view := by rfl
theorem forged_not_registered :
    EB.declOf .function ⟨forged.scope,forged.name⟩ ≠ some forged := by
  intro actual
  have registered : EB.declOf .function ⟨forged.scope,forged.name⟩ = some dCallOut := callOut_declared
  have equal : dCallOut = forged := Option.some.inj (registered.symm.trans actual)
  have ordinary : dCallOut.fnMut ≠ some .view := by decide
  exact ordinary ((congrArg Decl.fnMut equal).trans forged_is_view)

def missingCode := { GB answerOnly with hasCode := fun _ _ => false }
theorem missing_code_no_capture (after : Locals EB.layout [.address false] × St EB)
    (captured : Captured EB []) :
    ¬ CapturedAt missingCode FC 6 target dPing dPing_sig (lit 0) .nil before after captured := by
  intro actual
  change ((.error (.revert []) : Except Halt (Captured EB [])),before) =
    (.ok captured,after) at actual
  cases actual
end Solidity.Backend.WorldCalls.SourceIssuerControls
