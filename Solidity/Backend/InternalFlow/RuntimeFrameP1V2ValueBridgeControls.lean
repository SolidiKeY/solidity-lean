import Solidity.Backend.InternalFlow.RuntimeFrameP1V2ValueBridge
import Solidity.Backend.InternalFlow.RuntimeFrameP1V2ValueAgreementControls

/-! Regression: bridge packaging must retain the private primitive-result image,
both physical outcomes and refusal of an always-reverting replacement. These
importing checks use the existing genuine readAt witnesses. Approved/profile
remain external; no reflexive physical profile is claimed as Source provenance. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.P1V2ValueBridgeControls
open Evm Evm.Memory P1LangV2 V3CallProducer.Controls
open Solidity.Roadmap.G49Final (BridgeGoal)

noncomputable def certificate (approved : InterfaceV3.Admission P Γ)
    (profile : InterfaceV3.AdmissionAgreement approved (V3CallProducer.admitted selected 8 8)) :
    BridgeGoal (P1V2ValueBridge.A (f := "readAt") (args := args)
      (p := .uint) (r := .user "result") (destination := .here) (body := body) approved)
      (P1V2ValueBridge.B selected 8 8) () () id (fun _ _ => ())
      (P1V2ValueBridge.Local selected 8 8 approved) := by
  with_reducible exact P1V2ValueBridge.bridge selected 8 8 approved profile flags successful reverting

theorem positive_admitted (journal : List CallRec) (buffer : List UInt8) :
    P1V2ValueBridge.targetDomain selected 8 8 (P1V2ValueAgreementControls.positive journal buffer) :=
  positive_member

theorem negative_admitted (journal : List CallRec) (buffer : List UInt8) :
    P1V2ValueBridge.targetDomain selected 8 8 (P1V2ValueAgreementControls.negative journal buffer) :=
  negative_member

theorem complete_local (approved : InterfaceV3.Admission P Γ)
    (profile : InterfaceV3.AdmissionAgreement approved (V3CallProducer.admitted selected 8 8)) :
    P1V2ValueBridge.Local selected 8 8 approved :=
  (certificate approved profile).property.2.2

/-- The actual successful readAt entry rules out replacing this bridge image
with an always-reverting program on the same physical domain. -/
theorem rejecting_compiler_refused (approved : InterfaceV3.Admission P Γ) :
    ¬ Nonempty (BridgeGoal
      (P1V2ValueBridge.A (f := "readAt") (args := args) (p := .uint)
        (r := .user "result") (destination := .here) (body := body) approved)
      (targetLang [.base .revert] (P1V2ValueBridge.targetDomain selected 8 8))
      () () id (fun _ _ => ()) (P1V2ValueBridge.Local selected 8 8 approved)) := by
  with_reducible exact P1V2ValueBridge.always_revert_refused selected 8 8 approved successful

end Solidity.Backend.InternalFlow.RuntimeFrame.P1V2ValueBridgeControls
