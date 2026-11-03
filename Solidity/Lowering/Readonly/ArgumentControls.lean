import Solidity.Lowering.Readonly.CapturedArguments
import Solidity.Lowering.Readonly.LoweringControls

/-! Actual source argument effects followed by intrinsic argument evaluation.
This is an argument-phase proof, not a manufactured call/frame/raw-result witness. -/
namespace Solidity.Lowering.Readonly.ArgumentControls
open Solidity.Source Solidity.Source.SemanticsExamples
open PrimitiveValues PrimitiveLocals CapturedArguments
open Solidity.Lowering.Readonly.Controls

def expressions : RConvArgs EB [] [sourceTy .int] :=
  .cons (.convExplicit (.incDec true false (.state dX dX_ty rfl))
    (τ := sourceTy .int) (by decide)) (by decide) .nil

def captured : Vals EB.layout [sourceTy .int] :=
  .cons (toSource EB.layout .int ⟨3, by decide⟩) .nil

def after : St EB := ((evalConvArgs (GB answerOnly) FC 8 expressions).run (L0 EB, sB)).2.2

theorem actual_capture : (evalConvArgs (GB answerOnly) FC 8 expressions).run (L0 EB, sB) =
    (.ok captured, (L0 EB, after)) := by rfl

theorem actual_effect : readX after = some 4 := by rfl

def binders : Binders [.val .int] := .snoc .nil .int (Var.ofName "input")
def values : TEnv Cell [] [.val .int] := fromLocals EB.layout [.int] (captured.onto (L0 EB))
def lowered : Args Cell [] [.val .int] := arguments binders values

theorem after_effect_args : lowered.evalT (State.ofStorage LoweringControls.typedFour) = .ok values :=
  CapturedArguments.eval _ binders values

theorem old_value_retained : (TEnv.get .here values).val = 3 := by rfl

theorem no_reevaluation : (TEnv.get .here values).val ≠ 4 := by decide +kernel

theorem exact_binder_names : lowered.names = binders.names := CapturedArguments.names binders values

end Solidity.Lowering.Readonly.ArgumentControls
