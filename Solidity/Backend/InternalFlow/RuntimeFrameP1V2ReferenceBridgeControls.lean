import Solidity.Backend.InternalFlow.RuntimeFrameP1V2ReferenceBridge
import Solidity.Backend.InternalFlow.RuntimeFrameP1V2ReferenceRebindExecutionControls
import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerRefTupleControls

/-! Regression: native memory and mixed-tuple instantiations must retain real
compiler and both physical-entry witnesses. The test profile is chosen to be
the physical predicate: physical_profile proves only its reflexivity. These
native premise conjunctions are not joint-input evidence for external Approved,
Source origin or the full production P1/G42.04 factory. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.P1V2ReferenceBridgeControls
open Evm Evm.Memory P1LangV2 V3CallProducerRef.StructDefault.RebindControls
open Solidity.Roadmap.G49Final (BridgeGoal)
abbrev program := P1V2ReferenceRebindAgreement.selectedCheck
abbrev bodyCheck := P1V2ReferenceRebindAgreement.bodyCheck
abbrev physical : InterfaceV3.Admission C Γ := V3CallProducerRef.admitted program 16 16

abbrev sourceLanguage (approved : InterfaceV3.Admission C Γ) :=
  P1V2ReferenceBridge.A (ps := P1V2ReferenceRebindAgreement.psCheck)
    (rs := P1V2ReferenceRebindAgreement.rsCheck) (Γf := P1V2ReferenceRebindAgreement.finalCheck)
    (f := "structAlias") (args := args) (ret := ret) (body := bodyCheck) approved
noncomputable abbrev targetLanguage := P1V2ReferenceBridge.B program 16 16
abbrev localConclusion (approved : InterfaceV3.Admission C Γ) := P1V2ReferenceBridge.Local program 16 16 approved
theorem successfulCheck : InterfaceV3.SuccessfulEntry 1 F physical
    (Stmt.call "structAlias" args ret bodyCheck) (V3CallProducerRef.plan program 16 16) := by
  simpa only [call] using V3CallProducerRef.StructDefault.RebindControls.successful

theorem revertingCheck : InterfaceV3.RevertingEntry 1 F physical
    (Stmt.call "structAlias" args ret bodyCheck) (V3CallProducerRef.plan program 16 16) := by
  simpa only [call] using V3CallProducerRef.StructDefault.RebindControls.reverting

noncomputable def certificate (approved : InterfaceV3.Admission C Γ)
    (profile : InterfaceV3.AdmissionAgreement approved physical) :
    BridgeGoal (sourceLanguage approved) (targetLanguage)
      () () id (fun _ _ => ()) (localConclusion approved) := by
  with_reducible exact (P1V2ReferenceBridge.bridge
    (ps := P1V2ReferenceRebindAgreement.psCheck) (rs := P1V2ReferenceRebindAgreement.rsCheck)
    (Γf := P1V2ReferenceRebindAgreement.finalCheck)
    (C := C) (Γ := Γ) (Δ := .mem S :: Γ) (b := 1) (F := F)
    (f := "structAlias") (args := args) (ret := ret) (body := bodyCheck) (scope := scope)
    form program 16 16 approved profile flags
    successfulCheck
    revertingCheck)

theorem full_local (approved : InterfaceV3.Admission C Γ)
    (profile : InterfaceV3.AdmissionAgreement approved physical) :
    localConclusion approved :=
  (certificate approved profile).property.2.2

/-- Every legal index is physically admitted on the actual allocated old graph,
with arbitrary existing V2 journal and returndata, before selecting its outcome. -/
theorem all_inputs (n : Fin W) (journal : List CallRec) (buffer : List UInt8) :
    P1V2ReferenceBridge.targetDomain program 16 16
      (P1V2ReferenceRebindAgreement.input n journal buffer) := by
  with_reducible exact (Eq.mpr
    (P1V2ReferenceBridge.targetDomain_eq program 16 16
      (P1V2ReferenceRebindAgreement.input n journal buffer)) (member n))

theorem approved_all (approved : InterfaceV3.Admission C Γ)
    (profile : InterfaceV3.AdmissionAgreement approved physical)
    (n : Fin W) (journal : List CallRec) (buffer : List UInt8) :
    P1V2ReferenceBridge.sourceDomain approved
      (P1V2ReferenceRebindAgreement.input n journal buffer) := by
  with_reducible exact (P1V2ReferenceBridge.approved_of_member program 16 16 approved profile
    (P1V2ReferenceRebindAgreement.input n journal buffer) (all_inputs n journal buffer))

theorem approved_nonempty (approved : InterfaceV3.Admission C Γ)
    (profile : InterfaceV3.AdmissionAgreement approved physical) :
    ∃ e : Input C Γ, P1V2ReferenceBridge.sourceDomain approved e :=
  ⟨P1V2ReferenceRebindAgreement.input (wmod 0) [] [],approved_all approved profile _ _ _⟩

theorem rejecting_substitute_refused (approved : InterfaceV3.Admission C Γ) :
    ¬ Nonempty (BridgeGoal
      (sourceLanguage approved)
      (targetLang [.base .revert] (P1V2ReferenceBridge.targetDomain program 16 16))
      () () id (fun _ _ => ()) (localConclusion approved)) := by
  with_reducible exact (P1V2ReferenceBridge.always_revert_refused (ps := P1V2ReferenceRebindAgreement.psCheck) (rs := P1V2ReferenceRebindAgreement.rsCheck) (Γf := P1V2ReferenceRebindAgreement.finalCheck) (f := "structAlias") (args := args) (ret := ret) (body := bodyCheck) program 16 16 approved
    successfulCheck)

/-- Reflexivity of the chosen native predicate only; no external Approved
agreement or Source-origin evidence is established. -/
theorem physical_profile : InterfaceV3.AdmissionAgreement physical physical :=
  fun _ _ _ _ _ _ => Iff.rfl

/-- Form, alias flags and real dual-entry witnesses for this native program.
The profile conjunct is reflexive and does not authenticate external approval. -/
theorem joint_premises :
    V3CallProducerRef.Form Γ ret scope ∧
    InterfaceV1.NoAliasPromotion F program.checked.frag scope ∧
    InterfaceV3.AdmissionAgreement physical physical ∧
    InterfaceV3.SuccessfulEntry 1 F physical (Stmt.call "structAlias" args ret bodyCheck)
      (V3CallProducerRef.plan program 16 16) ∧
    InterfaceV3.RevertingEntry 1 F physical (Stmt.call "structAlias" args ret bodyCheck)
      (V3CallProducerRef.plan program 16 16) := by
  with_reducible exact ⟨form,flags,physical_profile,successfulCheck,revertingCheck⟩

/-- A constructed native certificate; this does not authenticate an external
Source approval or claim the physical profile is that Source approval. -/
noncomputable def physical_certificate := certificate physical physical_profile

theorem physical_nonempty :
    ∃ e : Input C Γ, P1V2ReferenceBridge.targetDomain program 16 16 e :=
  ⟨P1V2ReferenceRebindAgreement.input (wmod 0) [] [],all_inputs _ _ _⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.P1V2ReferenceBridgeControls

namespace Solidity.Backend.InternalFlow.RuntimeFrame.P1V2ReferenceBridgeTupleControls
open Evm Evm.Memory P1LangV2 V3CallProducerRef.Tuple.Controls
open Solidity.Roadmap.G49Final (BridgeGoal)
abbrev psCheck : Ctx := [.mem A,.val .uint]
abbrev rsCheck : Ctx := rs
abbrev finalCheck : Ctx := rsCheck ++ psCheck
abbrev bodyCheck : Prog C (rsCheck ++ psCheck) finalCheck := body
abbrev callCheck : Stmt C Γ (rsCheck ++ Γ) :=
  .call "tupleAlias" V3CallProducerRef.ArrayControls.args (.rets binders) bodyCheck
abbrev program : Composition.Program 1 F (.cons callCheck .nil) := selected
abbrev physical : InterfaceV3.Admission C Γ := V3CallProducerRef.admitted program 16 16
abbrev input (n : Fin W) (journal : List CallRec) (buffer : List UInt8) : Input C Γ :=
  ⟨1,64,V3CallProducerRef.ArrayControls.caller n,V3CallProducerRef.ArrayControls.bases,
    {base := V3CallProducerRef.ArrayControls.machine n,calls := journal,returndata := buffer},20⟩
abbrev sourceLanguage (approved : InterfaceV3.Admission C Γ) :=
  P1V2ReferenceBridge.A (C := C) (Γ := Γ) (Δ := rsCheck ++ Γ)
    (ps := psCheck) (rs := rsCheck) (Γf := finalCheck) (f := "tupleAlias")
    (args := V3CallProducerRef.ArrayControls.args) (ret := .rets binders) (body := bodyCheck) approved
noncomputable abbrev targetLanguage := P1V2ReferenceBridge.B program 16 16
abbrev localConclusion (approved : InterfaceV3.Admission C Γ) :=
  P1V2ReferenceBridge.Local program 16 16 approved

theorem successful_entry : InterfaceV3.SuccessfulEntry 1 F physical
    callCheck (V3CallProducerRef.plan program 16 16) := by
  simpa only [call,callCheck] using V3CallProducerRef.Tuple.Controls.successful

theorem reverting_entry : InterfaceV3.RevertingEntry 1 F physical
    callCheck (V3CallProducerRef.plan program 16 16) := by
  simpa only [call,callCheck] using V3CallProducerRef.Tuple.Controls.reverting

/-- This selected tuple is the existing certified emitter over the PUBLIC
compiled expansion; no direct public outer-call selection is asserted. -/
noncomputable def certificate (approved : InterfaceV3.Admission C Γ)
    (profile : InterfaceV3.AdmissionAgreement approved physical) :
    BridgeGoal (sourceLanguage approved) targetLanguage () () id (fun _ _ => ())
      (localConclusion approved) := by
  with_reducible exact (P1V2ReferenceBridge.bridge
    (C := C) (Γ := Γ) (Δ := rsCheck ++ Γ) (ps := psCheck) (rs := rsCheck)
    (Γf := finalCheck) (b := 1) (F := F) (f := "tupleAlias")
    (args := V3CallProducerRef.ArrayControls.args) (ret := .rets binders)
    (body := bodyCheck) (scope := scope)
    form program 16 16 approved profile flags successful_entry reverting_entry)

/-- Native predicate reflexivity only, not external Source approval. -/
theorem physical_profile : InterfaceV3.AdmissionAgreement physical physical :=
  fun _ _ _ _ _ _ => Iff.rfl

/-- Form, alias flags and real dual-entry witnesses for this native program.
The profile conjunct is reflexive and does not authenticate external approval. -/
theorem joint_premises :
    V3CallProducerRef.Form Γ (.rets binders) scope ∧
    InterfaceV1.NoAliasPromotion F program.checked.frag scope ∧
    InterfaceV3.AdmissionAgreement physical physical ∧
    InterfaceV3.SuccessfulEntry 1 F physical callCheck (V3CallProducerRef.plan program 16 16) ∧
    InterfaceV3.RevertingEntry 1 F physical callCheck (V3CallProducerRef.plan program 16 16) := by
  with_reducible exact ⟨form,flags,physical_profile,successful_entry,reverting_entry⟩

noncomputable def physical_certificate := certificate physical physical_profile

theorem all_inputs (n : Fin W) (journal : List CallRec) (buffer : List UInt8) :
    P1V2ReferenceBridge.targetDomain program 16 16 (input n journal buffer) := by
  with_reducible exact (Eq.mpr
    (P1V2ReferenceBridge.targetDomain_eq program 16 16 (input n journal buffer))
    (V3CallProducerRef.Tuple.Controls.member n))

theorem approved_all (approved : InterfaceV3.Admission C Γ)
    (profile : InterfaceV3.AdmissionAgreement approved physical)
    (n : Fin W) (journal : List CallRec) (buffer : List UInt8) :
    P1V2ReferenceBridge.sourceDomain approved (input n journal buffer) := by
  with_reducible exact (P1V2ReferenceBridge.approved_of_member program 16 16 approved profile
    (input n journal buffer) (all_inputs n journal buffer))

theorem physical_nonempty :
    ∃ e : Input C Γ, P1V2ReferenceBridge.targetDomain program 16 16 e :=
  ⟨input (wmod 0) [] [],all_inputs _ _ _⟩

theorem full_local (approved : InterfaceV3.Admission C Γ)
    (profile : InterfaceV3.AdmissionAgreement approved physical) : localConclusion approved :=
  (certificate approved profile).property.2.2

theorem rejecting_substitute_refused (approved : InterfaceV3.Admission C Γ) :
    ¬ Nonempty (BridgeGoal (sourceLanguage approved)
      (targetLang [.base .revert] (P1V2ReferenceBridge.targetDomain program 16 16))
      () () id (fun _ _ => ()) (localConclusion approved)) := by
  with_reducible exact (P1V2ReferenceBridge.always_revert_refused
    (C := C) (Γ := Γ) (Δ := rsCheck ++ Γ) (ps := psCheck) (rs := rsCheck)
    (Γf := finalCheck) (b := 1) (F := F) (f := "tupleAlias")
    (args := V3CallProducerRef.ArrayControls.args) (ret := .rets binders) (body := bodyCheck)
    program 16 16 approved successful_entry)

/-- Primitive7 and the returned/original array identity are source observations,
not an assumed post-state used to select the target domain. -/
theorem mixed_source_observation :
    sourceObservation (wmod 0) = some [7,0,0,2,1] :=
  V3CallProducerRef.Tuple.Controls.source_observation

theorem mixed_target_observation (journal : List CallRec) (buffer : List UInt8) :
    targetObservation
      (runV2 (lift (V3CallProducerRef.plan program 16 16).code) (input (wmod 0) journal buffer).machine).forget =
      some [77,131,128,0,128,7,20,99,1,0,0] := by
  with_reducible
    have observed := congrArg targetObservation (forget_run_lift
      (V3CallProducerRef.plan program 16 16).code (input (wmod 0) journal buffer).machine)
    have result := observed.trans V3CallProducerRef.Tuple.Controls.target_observation
    exact result

theorem tuple_failure_run (journal : List CallRec) (buffer : List UInt8) :
    runV2 (lift (V3CallProducerRef.plan program 16 16).code)
      (input (wmod 2) journal buffer).machine = .revert journal [] := by
  with_reducible
    have lifted := run_lift_revert (m := (input (wmod 2) journal buffer).machine)
      V3CallProducerRef.Tuple.Controls.simulated_revert
    exact lifted

/-- Actual omission of tuple compaction/export loses the primitive and pointer
result words. This refutes that image, not the correctly compiled family. -/
theorem missing_export_refused (journal : List CallRec) (buffer : List UInt8) :
    targetObservation (runV2 (lift missingExport) (input (wmod 0) journal buffer).machine).forget ≠
      some [77,131,128,0,128,7,20,99,1,0,0] := by
  with_reducible exact (fun claimed => absurd
    ((congrArg targetObservation
      (forget_run_lift missingExport (input (wmod 0) journal buffer).machine)).symm.trans claimed)
    V3CallProducerRef.Tuple.Controls.missing_export_refused)

end Solidity.Backend.InternalFlow.RuntimeFrame.P1V2ReferenceBridgeTupleControls
