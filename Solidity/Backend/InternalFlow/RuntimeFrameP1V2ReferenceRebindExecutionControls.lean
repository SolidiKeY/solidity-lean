import Solidity.Backend.InternalFlow.RuntimeFrameP1V2ReferenceRebindAgreement

/-! Regression: whole-struct rebinding must retain the old graph through the
actual lifted save/body/restore/export image, and a reached OOB must remain a
bare revert with arbitrary prior metadata. These importing controls reuse the
actual checked seed prefix and selected public call. They do not establish
Source admission or full production session/profile adequacy. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.P1V2ReferenceRebindExecutionControls
open Evm Evm.Memory V3CallProducerRef.StructDefault.RebindControls
noncomputable abbrev input := P1V2ReferenceRebindAgreement.input
abbrev code : List Instr := (V3CallProducerRef.plan selected 16 16).code
abbrev augmented (n : Fin W) (journal : List CallRec) (buffer : List UInt8) : MachineV2 :=
  {base := machine n,calls := journal,returndata := buffer}

theorem failure_run (journal : List CallRec) (buffer : List UInt8) :
    runV2 (lift code) (input (wmod 2) journal buffer).machine = .revert journal [] := by
  with_reducible
    have lifted := run_lift_revert (m := augmented (wmod 2) journal buffer)
      V3CallProducerRef.StructDefault.RebindControls.simulated_revert
    exact lifted

theorem old_alias_target (journal : List CallRec) (buffer : List UInt8) :
    targetObservation (runV2 (lift code) (input (wmod 0) journal buffer).machine).forget =
      some [77,140,128,0,133,133,20,99,1,0,0,0,130,131,0,0,0,135,136,0,0] := by
  with_reducible
    have observed := congrArg targetObservation
      (forget_run_lift code (augmented (wmod 0) journal buffer))
    have result := observed.trans V3CallProducerRef.StructDefault.RebindControls.target_observation
    exact result

end Solidity.Backend.InternalFlow.RuntimeFrame.P1V2ReferenceRebindExecutionControls
