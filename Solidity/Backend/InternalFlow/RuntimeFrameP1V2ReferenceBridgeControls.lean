import Solidity.Backend.InternalFlow.RuntimeFrameP1V2ReferenceBridge
import Solidity.Backend.InternalFlow.RuntimeFrameP1V2ReferenceRebindExecutionControls

/-! Regression: a generic native bridge must have simultaneous actual compiler,
physical admission and both outcome witnesses, not separate near-vacuous premise
examples. The old-graph rebinding family supplies the original joint witnesses
and constructs the full six-duty native certificate without an assumed producer.
Approved provenance and full production sessions remain open. -/
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

/-- All original make premises hold simultaneously for this one actual selected
program and its physical native profile, not for unrelated premise examples. -/
theorem physical_profile : InterfaceV3.AdmissionAgreement physical physical :=
  fun _ _ _ _ _ _ => Iff.rfl

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
