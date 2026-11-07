import Solidity.Backend.InternalFlow.RuntimeFrameP1V2ValueAgreementControls

/-! H68 regression: a frame-free or success-only bridge must not replace the
original selected value-call producer. This family is the actual readAt call
selected by Composition.compileCall. Its source family is constant in the
quotation index; quantifying that index adds no coverage of other calls.
Both canonical languages are the existing P1LangV2 languages, with the SAME
emitted private-result plan. The source domain is the caller-supplied original
approved judgment; the target domain is the original typed physical admission.
Their original AdmissionAgreement premise is retained, not authenticated here.
Local retains all six original V3 duties, including both genuine entry witnesses
and the full physical ReturnClaim. No new language, profile filter, no-failure
premise or general P1/library completion is introduced. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.P1V2ReadAtBridge
open Evm Evm.Memory P1LangV2 V3CallProducer.Controls
open Solidity.Roadmap (Event Outcome Prefix Lang Prefixes)
open Solidity.Roadmap.G49Final (BridgeGoal PassCorrect Behaviour)

/-- Exactly the existing ordinary call, not a selected outcome or prefix. -/
def source : Nat → Stmt P Γ Γ := fun _ => call

/-- The actual public-selected capture/private-result/restore/export image. -/
def image : List InstrV2 := lift (V3CallProducer.plan selected 8 8).code

def sourceDomain (approved : InterfaceV3.Admission P Γ) : Admission P Γ := fun e =>
  approved e.L e.frame e.caller e.base e.machine.base e.start

def targetDomain : Admission P Γ := fun e =>
  V3CallProducer.admitted selected 8 8 e.L e.frame e.caller e.base e.machine.base e.start

theorem consistent (e : Input P Γ) : Prefixes.Consistent (sourceSem source e) :=
  fun _ _ _ => Prefix.Le.refl _

def A (approved : InterfaceV3.Admission P Γ) : Lang Event Outcome :=
  sourceLang source (sourceDomain approved) consistent

noncomputable def B : Lang Event Outcome := targetLang image targetDomain

/-- Every original quantifier and antecedent in these six duties is unchanged.
The plan is fixed to the actual image, rather than existentially reselected. -/
def Local (approved : InterfaceV3.Admission P Γ) : Prop :=
  InterfaceV3.AdmissionAgreement approved (V3CallProducer.admitted selected 8 8) ∧
  InterfaceV3.EntryCoverage 0 F (V3CallProducer.admitted selected 8 8)
    (V3CallProducer.plan selected 8 8) ∧
  InterfaceV3.SuccessfulEntry 0 F (V3CallProducer.admitted selected 8 8) call
    (V3CallProducer.plan selected 8 8) ∧
  InterfaceV3.RevertingEntry 0 F (V3CallProducer.admitted selected 8 8) call
    (V3CallProducer.plan selected 8 8) ∧
  InterfaceV1.ReturnClaim 0 F call (V3CallProducer.plan selected 8 8) ∧
  InterfaceV1.BareRevertClaim 0 F call (V3CallProducer.plan selected 8 8)

theorem local_holds (approved : InterfaceV3.Admission P Γ)
    (profile : InterfaceV3.AdmissionAgreement approved (V3CallProducer.admitted selected 8 8)) :
    Local approved :=
  ⟨profile,V3CallProducer.coverage selected 8 8,successful,reverting,
    V3CallProducer.returns selected 8 8 flags,V3CallProducer.bare_revert selected 8 8⟩

/-- Agreement on EVERY original physical target input, arbitrary V2 metadata
included; neither outcome is an admission antecedent. -/
theorem agree (e : Input P Γ) (member : targetDomain e) :
    targetSem image e = sourcePrefix (call.run e.caller) :=
  P1V2ValueAgreement.agree selected 8 8 flags e
    (V3CallProducer.coverage selected 8 8 e.L e.frame e.caller e.base
      e.machine.base e.start member)

/-- Canonical full PassCorrect with identity environment abstraction and the
fixed executable Unit target-resource calculation prescribed by P1LangV2. -/
noncomputable def pass (approved : InterfaceV3.Admission P Γ)
    (profile : InterfaceV3.AdmissionAgreement approved (V3CallProducer.admitted selected 8 8)) :
    PassCorrect (Behaviour.ofLang (A approved) ()) (Behaviour.ofLang B ()) where
  envAbs := id
  envSound e member := (profile e.L e.frame e.caller e.base e.machine.base e.start).mpr member
  envOnto e member :=
    ⟨e,(profile e.L e.frame e.caller e.base e.machine.base e.start).mp member,rfl⟩
  need := fun _ _ => ()
  need_ok e n member _ := by
    refine ⟨⟨trivial,trivial,trivial⟩,?_⟩
    change (sourcePrefix (call.run e.caller)).Le (targetSem image e)
    rw [agree e member]
    exact Prefix.Le.refl _
  back e _ member _ _ := by
    refine ⟨(0 : Nat),trivial,trivial,?_⟩
    change (targetSem image e).Le (sourcePrefix (call.run e.caller))
    rw [agree e member]
    exact Prefix.Le.refl _

/-- The SAME original producer is constructed, with its exact selected plan.
No complete producer or target execution is supplied as a premise. -/
def producer (approved : InterfaceV3.Admission P Γ)
    (profile : InterfaceV3.AdmissionAgreement approved (V3CallProducer.admitted selected 8 8)) :
    { result : InterfaceV3.PendingCallProducer 0 F approved
        (V3CallProducer.admitted selected 8 8) "readAt" args ret body //
      result.plan = V3CallProducer.plan selected 8 8 } :=
  ⟨V3CallProducer.Controls.producer approved profile,rfl⟩

/-- The canonical target image is exactly this producer's image. -/
theorem producer_image (approved : InterfaceV3.Admission P Γ)
    (profile : InterfaceV3.AdmissionAgreement approved (V3CallProducer.admitted selected 8 8)) :
    image = lift (producer approved profile).val.plan.code := rfl

/-- Full H68 factory for this supported ordinary-call family, conditional only
on its unchanged external profile agreement. It is not a factory for arbitrary
bodies, recursive sessions or unproved approved-profile provenance. -/
noncomputable def p1_frame_bridge (approved : InterfaceV3.Admission P Γ)
    (profile : InterfaceV3.AdmissionAgreement approved (V3CallProducer.admitted selected 8 8)) :
    BridgeGoal (A approved) B () () id (fun _ _ => ()) (Local approved) :=
  ⟨pass approved profile,rfl,rfl,local_holds approved profile⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.P1V2ReadAtBridge
