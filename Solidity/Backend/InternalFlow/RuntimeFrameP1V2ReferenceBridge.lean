import Solidity.Backend.InternalFlow.RuntimeFrameP1V2ReferenceAgreement

/-! Regression: a native reference-return bridge must bind the actual selected
capture/body/restore image and retain all six original V3 duties, including
both genuine entry witnesses. This general transport covers the existing typed
reference/tuple Form, not merely one closed example. It uses canonical P1LangV2
languages and preserves the original Approved agreement and physical domain.
The supplied success/revert witnesses and profile are exactly the old make
premises, not a complete producer or target run. No actual-Source/profile
provenance, recursive session, payload producer or full P1/G42.04 factory is
claimed. Source quotation indices all select the same native call. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.P1V2ReferenceBridge
open Evm Evm.Memory P1LangV2
open Solidity.Roadmap (Event Outcome Prefix Lang Prefixes)
open Solidity.Roadmap.G49Final (BridgeGoal PassCorrect Behaviour)

variable {C : Contract} {Γ Δ ps rs Γf : Ctx} {b : Nat} {F : Frag Γ}
  {f : Name} {args : Args C Γ ps} {ret : CallRet Γ rs Δ}
  {body : Prog C (rs ++ ps) Γf} {scope : Ext Γ Δ}

local notation "nativeCall" => (Stmt.call f args ret body : Stmt C Γ Δ)

def source : Nat → Stmt C Γ Δ := fun _ => nativeCall
local notation "nativeSource" => source (f := f) (args := args) (ret := ret) (body := body)

def sourceDomain (approved : InterfaceV3.Admission C Γ) : Admission C Γ := fun e =>
  approved e.L e.frame e.caller e.base e.machine.base e.start

def image (selected : Composition.Program b F (.cons nativeCall .nil))
    (lo pointer : Nat) : List InstrV2 := lift (V3CallProducerRef.plan selected lo pointer).code

def targetDomain (selected : Composition.Program b F (.cons nativeCall .nil))
    (lo pointer : Nat) : Admission C Γ := fun e =>
  V3CallProducerRef.admitted selected lo pointer e.L e.frame e.caller e.base e.machine.base e.start

/-- Exact original physical admission, exposed without reducing its concrete
heap/machine arguments during an importing proof. -/
theorem targetDomain_eq (selected : Composition.Program b F (.cons nativeCall .nil))
    (lo pointer : Nat) (e : Input C Γ) :
    targetDomain selected lo pointer e =
      V3CallProducerRef.admitted selected lo pointer e.L e.frame e.caller e.base e.machine.base e.start := rfl

theorem sourceDomain_eq (approved : InterfaceV3.Admission C Γ) (e : Input C Γ) :
    sourceDomain approved e = approved e.L e.frame e.caller e.base e.machine.base e.start := rfl

/-- The unchanged original agreement transports physical membership to Approved,
without unfolding a concrete caller's heap in an importing proof. -/
theorem approved_of_member
    (selected : Composition.Program b F (.cons nativeCall .nil)) (lo pointer : Nat)
    (approved : InterfaceV3.Admission C Γ)
    (profile : InterfaceV3.AdmissionAgreement approved (V3CallProducerRef.admitted selected lo pointer))
    (e : Input C Γ) (member : targetDomain selected lo pointer e) : sourceDomain approved e :=
  (profile e.L e.frame e.caller e.base e.machine.base e.start).mpr member

theorem consistent (e : Input C Γ) : Prefixes.Consistent (sourceSem nativeSource e) :=
  fun _ _ _ => Prefix.Le.refl _

def A (approved : InterfaceV3.Admission C Γ) : Lang Event Outcome :=
  sourceLang nativeSource (sourceDomain approved) consistent

noncomputable def B (selected : Composition.Program b F (.cons nativeCall .nil))
    (lo pointer : Nat) : Lang Event Outcome :=
  targetLang (image selected lo pointer) (targetDomain selected lo pointer)

/-- Entire old V3 conclusion, with the exact selected plan; no antecedent is
moved into a new global admission filter. -/
def Local (selected : Composition.Program b F (.cons nativeCall .nil))
    (lo pointer : Nat) (approved : InterfaceV3.Admission C Γ) : Prop :=
  InterfaceV3.AdmissionAgreement approved (V3CallProducerRef.admitted selected lo pointer) ∧
  InterfaceV3.EntryCoverage b F (V3CallProducerRef.admitted selected lo pointer)
    (V3CallProducerRef.plan selected lo pointer) ∧
  InterfaceV3.SuccessfulEntry b F (V3CallProducerRef.admitted selected lo pointer) nativeCall
    (V3CallProducerRef.plan selected lo pointer) ∧
  InterfaceV3.RevertingEntry b F (V3CallProducerRef.admitted selected lo pointer) nativeCall
    (V3CallProducerRef.plan selected lo pointer) ∧
  InterfaceV1.ReturnClaim b F nativeCall (V3CallProducerRef.plan selected lo pointer) ∧
  InterfaceV1.BareRevertClaim b F nativeCall (V3CallProducerRef.plan selected lo pointer)

theorem local_holds (form : V3CallProducerRef.Form Γ ret scope)
    (selected : Composition.Program b F (.cons nativeCall .nil)) (lo pointer : Nat)
    (approved : InterfaceV3.Admission C Γ)
    (profile : InterfaceV3.AdmissionAgreement approved (V3CallProducerRef.admitted selected lo pointer))
    (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag scope)
    (successful : InterfaceV3.SuccessfulEntry b F (V3CallProducerRef.admitted selected lo pointer)
      nativeCall (V3CallProducerRef.plan selected lo pointer))
    (reverting : InterfaceV3.RevertingEntry b F (V3CallProducerRef.admitted selected lo pointer)
      nativeCall (V3CallProducerRef.plan selected lo pointer)) : Local selected lo pointer approved :=
  ⟨profile,V3CallProducerRef.coverage selected lo pointer,successful,reverting,
    V3CallProducerRef.returns form selected lo pointer flags,
    V3CallProducerRef.bare_revert selected lo pointer⟩

theorem agree (form : V3CallProducerRef.Form Γ ret scope)
    (selected : Composition.Program b F (.cons nativeCall .nil)) (lo pointer : Nat)
    (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag scope)
    (e : Input C Γ) (member : targetDomain selected lo pointer e) :
    targetSem (image selected lo pointer) e = sourcePrefix ((nativeCall).run e.caller) :=
  P1V2ReferenceAgreement.agree form selected lo pointer flags e
    (V3CallProducerRef.coverage selected lo pointer e.L e.frame e.caller e.base
      e.machine.base e.start member)

/-- Fixed canonical identity environment map and executable Unit target need.
Agreement is proved for every physical input, not given as a premise. -/
noncomputable def pass (form : V3CallProducerRef.Form Γ ret scope)
    (selected : Composition.Program b F (.cons nativeCall .nil)) (lo pointer : Nat)
    (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag scope)
    (approved : InterfaceV3.Admission C Γ)
    (profile : InterfaceV3.AdmissionAgreement approved (V3CallProducerRef.admitted selected lo pointer)) :
    PassCorrect (Behaviour.ofLang (A (f := f) (args := args) (ret := ret) (body := body) approved) ())
      (Behaviour.ofLang (B selected lo pointer) ()) where
  envAbs := id
  envSound e member := (profile e.L e.frame e.caller e.base e.machine.base e.start).mpr member
  envOnto e member :=
    ⟨e,(profile e.L e.frame e.caller e.base e.machine.base e.start).mp member,rfl⟩
  need := fun _ _ => ()
  need_ok e n member _ := by
    refine ⟨⟨trivial,trivial,trivial⟩,?_⟩
    change (sourcePrefix ((nativeCall).run e.caller)).Le (targetSem (image selected lo pointer) e)
    rw [agree form selected lo pointer flags e member]
    exact Prefix.Le.refl _
  back e _ member _ _ := by
    refine ⟨(0 : Nat),trivial,trivial,?_⟩
    change (targetSem (image selected lo pointer) e).Le (sourcePrefix ((nativeCall).run e.caller))
    rw [agree form selected lo pointer flags e member]
    exact Prefix.Le.refl _

/-- Actual old producer with exact-plan provenance, built from its unchanged
premises; no full producer is assumed. -/
def producer (form : V3CallProducerRef.Form Γ ret scope)
    (selected : Composition.Program b F (.cons nativeCall .nil)) (lo pointer : Nat)
    (approved : InterfaceV3.Admission C Γ)
    (profile : InterfaceV3.AdmissionAgreement approved (V3CallProducerRef.admitted selected lo pointer))
    (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag scope)
    (successful : InterfaceV3.SuccessfulEntry b F (V3CallProducerRef.admitted selected lo pointer)
      nativeCall (V3CallProducerRef.plan selected lo pointer))
    (reverting : InterfaceV3.RevertingEntry b F (V3CallProducerRef.admitted selected lo pointer)
      nativeCall (V3CallProducerRef.plan selected lo pointer)) :
    V3CallProducerRef.ProducerGoal selected lo pointer approved :=
  ⟨V3CallProducerRef.make form selected lo pointer approved profile flags successful reverting,rfl⟩

theorem producer_image (form : V3CallProducerRef.Form Γ ret scope)
    (selected : Composition.Program b F (.cons nativeCall .nil)) (lo pointer : Nat)
    (approved : InterfaceV3.Admission C Γ)
    (profile : InterfaceV3.AdmissionAgreement approved (V3CallProducerRef.admitted selected lo pointer))
    (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag scope)
    (successful : InterfaceV3.SuccessfulEntry b F (V3CallProducerRef.admitted selected lo pointer)
      nativeCall (V3CallProducerRef.plan selected lo pointer))
    (reverting : InterfaceV3.RevertingEntry b F (V3CallProducerRef.admitted selected lo pointer)
      nativeCall (V3CallProducerRef.plan selected lo pointer)) :
    image selected lo pointer =
      lift (producer form selected lo pointer approved profile flags successful reverting).val.plan.code := rfl

/-- Native reference-family full certificate and complete old Local. External
Approved provenance and general source sessions remain explicit open work. -/
noncomputable def bridge (form : V3CallProducerRef.Form Γ ret scope)
    (selected : Composition.Program b F (.cons nativeCall .nil)) (lo pointer : Nat)
    (approved : InterfaceV3.Admission C Γ)
    (profile : InterfaceV3.AdmissionAgreement approved (V3CallProducerRef.admitted selected lo pointer))
    (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag scope)
    (successful : InterfaceV3.SuccessfulEntry b F (V3CallProducerRef.admitted selected lo pointer)
      nativeCall (V3CallProducerRef.plan selected lo pointer))
    (reverting : InterfaceV3.RevertingEntry b F (V3CallProducerRef.admitted selected lo pointer)
      nativeCall (V3CallProducerRef.plan selected lo pointer)) :
    BridgeGoal (A (f := f) (args := args) (ret := ret) (body := body) approved)
      (B selected lo pointer) () () id (fun _ _ => ()) (Local selected lo pointer approved) :=
  ⟨pass form selected lo pointer flags approved profile,rfl,rfl,
    local_holds form selected lo pointer approved profile flags successful reverting⟩

/-- Actual rejecting execution in the same canonical target language. -/
theorem rejecting_target (e : Input C Γ) :
    targetSem [.base .revert] e = ⟨[],some (.revert [])⟩ := by
  change targetPrefix e.machine.base.self e.machine.calls.length
    (.revert e.machine.calls []) = _
  simp only [targetPrefix,eventsAfter_existing]

/-- An original successful physical entry refutes an always-revert replacement
of the complete native bridge, even without assuming an Approved agreement. -/
theorem always_revert_refused
    (selected : Composition.Program b F (.cons nativeCall .nil)) (lo pointer : Nat)
    (approved : InterfaceV3.Admission C Γ)
    (successful : InterfaceV3.SuccessfulEntry b F (V3CallProducerRef.admitted selected lo pointer)
      nativeCall (V3CallProducerRef.plan selected lo pointer)) :
    ¬ Nonempty (BridgeGoal
      (A (f := f) (args := args) (ret := ret) (body := body) approved)
      (targetLang [.base .revert] (targetDomain selected lo pointer))
      () () id (fun _ _ => ()) (Local selected lo pointer approved)) := by
  rintro ⟨certificate⟩
  obtain ⟨L,frame,caller,base,machine,start,out,member,entry,executed⟩ := successful
  let e : Input C Γ := ⟨L,frame,caller,base,MachineV2.ofBase machine,start⟩
  have entered : targetDomain selected lo pointer e := member
  have ready : (Behaviour.ofLang
      (A (f := f) (args := args) (ret := ret) (body := body) approved) ()).Ready
      (certificate.val.envAbs e) (0 : Nat) := ⟨trivial,trivial,trivial⟩
  have observed := (certificate.val.need_ok e (0 : Nat) entered ready).2
  change (sourcePrefix ((nativeCall).run (certificate.val.envAbs e).caller)).Le
    (targetSem [.base .revert] e) at observed
  rw [certificate.property.1] at observed
  change (sourcePrefix ((nativeCall).run caller)).Le (targetSem [.base .revert] e) at observed
  rw [executed,rejecting_target e] at observed
  have same := observed.final_eq rfl
  have final := congrArg Prefix.final same
  cases final

end Solidity.Backend.InternalFlow.RuntimeFrame.P1V2ReferenceBridge
