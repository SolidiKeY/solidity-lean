import Solidity.Backend.InternalFlow.RuntimeFrameP1V2ReadAtBridge

/-! H68 regression: retaining prefix equality must not drop physical coverage,
the reverting-entry witness or one of the outcomes from the approved domain.
The actual selected readAt family supplies both inhabited outcomes and exact
producer-image binding; arbitrary preexisting V2 metadata is retained. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.P1V2ReadAtBridgeControls
open Evm Evm.Memory P1LangV2 V3CallProducer.Controls P1V2ReadAtBridge

/-- Original profile agreement admits the actual successful input, with every
V2 journal/buffer. No success-only domain is defined for the bridge. -/
theorem approved_positive (approved : InterfaceV3.Admission P Γ)
    (profile : InterfaceV3.AdmissionAgreement approved (V3CallProducer.admitted selected 8 8))
    (journal : List CallRec) (buffer : List UInt8) :
    sourceDomain approved (P1V2ValueAgreementControls.positive journal buffer) :=
  (profile 1 16 initial bases machine 10).mpr positive_member

theorem approved_negative (approved : InterfaceV3.Admission P Γ)
    (profile : InterfaceV3.AdmissionAgreement approved (V3CallProducer.admitted selected 8 8))
    (journal : List CallRec) (buffer : List UInt8) :
    sourceDomain approved (P1V2ValueAgreementControls.negative journal buffer) :=
  (profile 1 16 failing bases failedMachine 10).mpr negative_member

/-- This supported bridge cannot be made vacuous by an empty approved domain. -/
theorem approved_nonempty (approved : InterfaceV3.Admission P Γ)
    (profile : InterfaceV3.AdmissionAgreement approved (V3CallProducer.admitted selected 8 8)) :
    ∃ e : Input P Γ, sourceDomain approved e :=
  ⟨P1V2ValueAgreementControls.positive [] [],approved_positive approved profile [] []⟩

theorem positive_observation (journal : List CallRec) (buffer : List UInt8) :
    targetSem image (P1V2ValueAgreementControls.positive journal buffer) =
      ⟨[],some (.success [])⟩ :=
  P1V2ValueAgreementControls.success_prefix journal buffer

theorem negative_observation (journal : List CallRec) (buffer : List UInt8) :
    targetSem image (P1V2ValueAgreementControls.negative journal buffer) =
      ⟨[],some (.revert [])⟩ :=
  P1V2ValueAgreementControls.failure_prefix journal buffer

/-- All six original Local duties are retained by the actual full factory. -/
theorem full_local (approved : InterfaceV3.Admission P Γ)
    (profile : InterfaceV3.AdmissionAgreement approved (V3CallProducer.admitted selected 8 8)) :
    Local approved :=
  (p1_frame_bridge approved profile).property.2.2

/-- In particular the genuine original reverting-entry duty was not erased. -/
theorem reverting_entry_retained (approved : InterfaceV3.Admission P Γ)
    (profile : InterfaceV3.AdmissionAgreement approved (V3CallProducer.admitted selected 8 8)) :
    InterfaceV3.RevertingEntry 0 F (V3CallProducer.admitted selected 8 8) call
      (V3CallProducer.plan selected 8 8) :=
  (full_local approved profile).2.2.2.1

/-- Actual execution of a rejecting substitute in the SAME canonical target
language, not an alternative observation projection. -/
theorem rejecting_target (e : Input P Γ) :
    targetSem [.base .revert] e = ⟨[],some (.revert [])⟩ := by
  change targetPrefix e.machine.base.self e.machine.calls.length
    (.revert e.machine.calls []) = _
  simp only [targetPrefix,eventsAfter_existing]

/-- An always-revert substitute cannot meet the full fixed-map BridgeGoal.
This is an intentional counterexample to that substitute, not an assumed
failure of the source or the implemented compiler. -/
theorem always_revert_refused (approved : InterfaceV3.Admission P Γ) :
    ¬ Nonempty (Solidity.Roadmap.G49Final.BridgeGoal (A approved)
      (targetLang [.base .revert] targetDomain) () () id (fun _ _ => ()) (Local approved)) := by
  rintro ⟨bridge⟩
  let e := P1V2ValueAgreementControls.positive [] []
  have member : targetDomain e := positive_member
  have ready : (Solidity.Roadmap.G49Final.Behaviour.ofLang (A approved) ()).Ready
      (bridge.val.envAbs e) (0 : Nat) := ⟨trivial,trivial,trivial⟩
  have observed := (bridge.val.need_ok e (0 : Nat) member ready).2
  change (sourcePrefix (call.run (bridge.val.envAbs e).caller)).Le
    (targetSem [.base .revert] e) at observed
  rw [bridge.property.1] at observed
  change (sourcePrefix (call.run initial)).Le (targetSem [.base .revert] e) at observed
  rw [source_success,rejecting_target e] at observed
  have same := observed.final_eq rfl
  have final := congrArg Solidity.Roadmap.Prefix.final same
  cases final

end Solidity.Backend.InternalFlow.RuntimeFrame.P1V2ReadAtBridgeControls
