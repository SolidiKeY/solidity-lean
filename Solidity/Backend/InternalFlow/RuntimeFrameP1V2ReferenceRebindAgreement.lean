import Solidity.Backend.InternalFlow.RuntimeFrameP1V2ReferenceAgreement
import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerRefStructRebindControls

/-! Regression: whole-struct return rebinding must return the old graph, not
its newly allocated default. The checked seed constructs the initial graph;
the selected reference plan retains caller restoration and old aliases.
Typed aliases bound conversion in the all-index V2 agreement proof. Source-only
observations remain in RuntimeFrameV3CallProducerRefStructRebindControls;
no duplicate forwarding declarations are needed here. Missing-export refusal
is operational. Separate direct-failure and positive target-snapshot controls
are in RuntimeFrameP1V2ReferenceRebindExecutionControls. No full session
adequacy is claimed. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.P1V2ReferenceRebindAgreement
open Evm Evm.Memory V3CallProducerRef.StructDefault.RebindControls

/-- The base map is fixed by the existing proved allocation prefix, for proof
only; neither source execution nor target instructions evaluate that map. -/
noncomputable abbrev input (n : Fin W) (journal : List CallRec) (buffer : List UInt8) :
    P1LangV2.Input C Γ :=
  ⟨1,64,caller n,bases n,{base := machine n,calls := journal,returndata := buffer},20⟩

abbrev psCheck : Ctx := [.mem S,.mem V3CallProducerRef.ArrayControls.A,.val .uint]
abbrev rsCheck : Ctx := [.mem S]
abbrev finalCheck : Ctx := [.val .uint,.mem S,.mem S,.mem V3CallProducerRef.ArrayControls.A,.val .uint]
abbrev bodyCheck : Prog C (rsCheck ++ psCheck) finalCheck := body
abbrev callCheck : Stmt C Γ (.mem S :: Γ) := .call "structAlias" args ret bodyCheck
abbrev selectedCheck : Composition.Program 1 F (.cons callCheck .nil) := selected
theorem all_indices (n : Fin W) (journal : List CallRec) (buffer : List UInt8) :
    P1LangV2.targetSem (lift (V3CallProducerRef.plan selected 16 16).code)
      (input n journal buffer) = P1LangV2.sourcePrefix (call.run (caller n)) := by
  unfold call
  with_reducible exact (P1V2ReferenceAgreement.agree (C := C) (Γ := Γ) (Δ := .mem S :: Γ)
    (ps := psCheck) (rs := rsCheck) (Γf := finalCheck) (b := 1) (F := F)
    (f := "structAlias") (args := args) (ret := ret) (body := bodyCheck) (scope := scope)
    form selectedCheck 16 16 flags
    ⟨1,64,caller n,bases n,{base := machine n,calls := journal,returndata := buffer},20⟩
    (entered n))

theorem missing_export (journal : List CallRec) (buffer : List UInt8) :
    targetObservation (runV2 (lift missingExport) (input (wmod 0) journal buffer).machine).forget ≠
      some [77,140,128,0,133,133,20,99,1,0,0,0,130,131,0,0,0,135,136,0,0] := by
  with_reducible exact (fun claimed => absurd
    ((congrArg targetObservation (forget_run_lift missingExport
      {base := machine (wmod 0),calls := journal,returndata := buffer})).symm.trans claimed)
    V3CallProducerRef.StructDefault.RebindControls.missing_export_refused)

end Solidity.Backend.InternalFlow.RuntimeFrame.P1V2ReferenceRebindAgreement
