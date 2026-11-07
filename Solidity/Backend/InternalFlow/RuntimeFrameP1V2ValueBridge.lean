import Solidity.Backend.InternalFlow.RuntimeFrameP1V2ValueAgreement

/-! Regression: a native primitive-result bridge must execute the exact private
result/capture/restore/export plan, rather than a void plan that loses its result.
Reuse canonical P1LangV2 and the proved all-outcome value agreement. The six
original V3 duties, Approved agreement and physical admission remain unchanged;
success/revert witnesses are original premises, not external Source/profile
provenance. This conditional native bridge is not the full production factory. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.P1V2ValueBridge
open Evm Evm.Memory P1LangV2
open Solidity.Roadmap (Event Outcome Prefix Lang Prefixes)
open Solidity.Roadmap.G49Final (BridgeGoal PassCorrect Behaviour)

variable {C : Contract} {Γ ps Γf : Ctx} {b : Nat} {F : Frag Γ}
  {f : Name} {args : Args C Γ ps} {p : PrimTy} {r : Var}
  {destination : Idx Γ (.val p)} {body : Prog C (.val p :: ps) Γf}

local notation "nativeCall" => (Stmt.call f args (CallRet.val p r (some destination)) body : Stmt C Γ Γ)

def source : Nat → Stmt C Γ Γ := fun _ => nativeCall
local notation "nativeSource" => source (f := f) (args := args) (p := p) (r := r) (destination := destination) (body := body)

def sourceDomain (approved : InterfaceV3.Admission C Γ) : Admission C Γ := fun e =>
  approved e.L e.frame e.caller e.base e.machine.base e.start

def image (selected : Composition.Program b F (.cons nativeCall .nil))
    (lo pointer : Nat) : List InstrV2 := lift (V3CallProducer.plan selected lo pointer).code

def targetDomain (selected : Composition.Program b F (.cons nativeCall .nil))
    (lo pointer : Nat) : Admission C Γ := fun e =>
  V3CallProducer.admitted selected lo pointer e.L e.frame e.caller e.base e.machine.base e.start

/-- Exact original physical admission, exposed without reducing its concrete
heap/machine arguments during an importing proof. -/
theorem targetDomain_eq (selected : Composition.Program b F (.cons nativeCall .nil))
    (lo pointer : Nat) (e : Input C Γ) :
    targetDomain selected lo pointer e =
      V3CallProducer.admitted selected lo pointer e.L e.frame e.caller e.base e.machine.base e.start := rfl

theorem sourceDomain_eq (approved : InterfaceV3.Admission C Γ) (e : Input C Γ) :
    sourceDomain approved e = approved e.L e.frame e.caller e.base e.machine.base e.start := rfl

/-- The unchanged original agreement transports physical membership to Approved,
without unfolding a concrete caller's heap in an importing proof. -/
theorem approved_of_member
    (selected : Composition.Program b F (.cons nativeCall .nil)) (lo pointer : Nat)
    (approved : InterfaceV3.Admission C Γ)
    (profile : InterfaceV3.AdmissionAgreement approved (V3CallProducer.admitted selected lo pointer))
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
  InterfaceV3.AdmissionAgreement approved (V3CallProducer.admitted selected lo pointer) ∧
  InterfaceV3.EntryCoverage b F (V3CallProducer.admitted selected lo pointer)
    (V3CallProducer.plan selected lo pointer) ∧
  InterfaceV3.SuccessfulEntry b F (V3CallProducer.admitted selected lo pointer) nativeCall
    (V3CallProducer.plan selected lo pointer) ∧
  InterfaceV3.RevertingEntry b F (V3CallProducer.admitted selected lo pointer) nativeCall
    (V3CallProducer.plan selected lo pointer) ∧
  InterfaceV1.ReturnClaim b F nativeCall (V3CallProducer.plan selected lo pointer) ∧
  InterfaceV1.BareRevertClaim b F nativeCall (V3CallProducer.plan selected lo pointer)

theorem local_holds (selected : Composition.Program b F (.cons nativeCall .nil)) (lo pointer : Nat)
    (approved : InterfaceV3.Admission C Γ)
    (profile : InterfaceV3.AdmissionAgreement approved (V3CallProducer.admitted selected lo pointer))
    (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag .refl)
    (successful : InterfaceV3.SuccessfulEntry b F (V3CallProducer.admitted selected lo pointer)
      nativeCall (V3CallProducer.plan selected lo pointer))
    (reverting : InterfaceV3.RevertingEntry b F (V3CallProducer.admitted selected lo pointer)
      nativeCall (V3CallProducer.plan selected lo pointer)) : Local selected lo pointer approved :=
  ⟨profile,V3CallProducer.coverage selected lo pointer,successful,reverting,
    V3CallProducer.returns selected lo pointer flags,
    V3CallProducer.bare_revert selected lo pointer⟩

theorem agree (selected : Composition.Program b F (.cons nativeCall .nil)) (lo pointer : Nat)
    (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag .refl)
    (e : Input C Γ) (member : targetDomain selected lo pointer e) :
    targetSem (image selected lo pointer) e = sourcePrefix ((nativeCall).run e.caller) :=
  P1V2ValueAgreement.agree selected lo pointer flags e
    (V3CallProducer.coverage selected lo pointer e.L e.frame e.caller e.base
      e.machine.base e.start member)

/-- Fixed canonical identity environment map and executable Unit target need.
Agreement is proved for every physical input, not given as a premise. -/
noncomputable def pass (selected : Composition.Program b F (.cons nativeCall .nil)) (lo pointer : Nat)
    (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag .refl)
    (approved : InterfaceV3.Admission C Γ)
    (profile : InterfaceV3.AdmissionAgreement approved (V3CallProducer.admitted selected lo pointer)) :
    PassCorrect (Behaviour.ofLang (A (f := f) (args := args) (p := p) (r := r) (destination := destination) (body := body) approved) ())
      (Behaviour.ofLang (B selected lo pointer) ()) where
  envAbs := id
  envSound e member := (profile e.L e.frame e.caller e.base e.machine.base e.start).mpr member
  envOnto e member :=
    ⟨e,(profile e.L e.frame e.caller e.base e.machine.base e.start).mp member,rfl⟩
  need := fun _ _ => ()
  need_ok e n member _ := by
    refine ⟨⟨trivial,trivial,trivial⟩,?_⟩
    change (sourcePrefix ((nativeCall).run e.caller)).Le (targetSem (image selected lo pointer) e)
    rw [agree selected lo pointer flags e member]
    exact Prefix.Le.refl _
  back e _ member _ _ := by
    refine ⟨(0 : Nat),trivial,trivial,?_⟩
    change (targetSem (image selected lo pointer) e).Le (sourcePrefix ((nativeCall).run e.caller))
    rw [agree selected lo pointer flags e member]
    exact Prefix.Le.refl _

/-- Actual old producer with exact-plan provenance, built from its unchanged
premises; no full producer is assumed. -/
def producer (selected : Composition.Program b F (.cons nativeCall .nil)) (lo pointer : Nat)
    (approved : InterfaceV3.Admission C Γ)
    (profile : InterfaceV3.AdmissionAgreement approved (V3CallProducer.admitted selected lo pointer))
    (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag .refl)
    (successful : InterfaceV3.SuccessfulEntry b F (V3CallProducer.admitted selected lo pointer)
      nativeCall (V3CallProducer.plan selected lo pointer))
    (reverting : InterfaceV3.RevertingEntry b F (V3CallProducer.admitted selected lo pointer)
      nativeCall (V3CallProducer.plan selected lo pointer)) :
    { result : InterfaceV3.PendingCallProducer b F approved (V3CallProducer.admitted selected lo pointer)
      f args (.val p r (some destination)) body // result.plan = V3CallProducer.plan selected lo pointer } :=
  ⟨V3CallProducer.make selected lo pointer approved profile flags successful reverting,rfl⟩

theorem producer_image (selected : Composition.Program b F (.cons nativeCall .nil)) (lo pointer : Nat)
    (approved : InterfaceV3.Admission C Γ)
    (profile : InterfaceV3.AdmissionAgreement approved (V3CallProducer.admitted selected lo pointer))
    (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag .refl)
    (successful : InterfaceV3.SuccessfulEntry b F (V3CallProducer.admitted selected lo pointer)
      nativeCall (V3CallProducer.plan selected lo pointer))
    (reverting : InterfaceV3.RevertingEntry b F (V3CallProducer.admitted selected lo pointer)
      nativeCall (V3CallProducer.plan selected lo pointer)) :
    image selected lo pointer =
      lift (producer selected lo pointer approved profile flags successful reverting).val.plan.code := rfl

/-- Native primitive-value-family full certificate and complete old Local. External
Approved provenance and general source sessions remain explicit open work. -/
noncomputable def bridge (selected : Composition.Program b F (.cons nativeCall .nil)) (lo pointer : Nat)
    (approved : InterfaceV3.Admission C Γ)
    (profile : InterfaceV3.AdmissionAgreement approved (V3CallProducer.admitted selected lo pointer))
    (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag .refl)
    (successful : InterfaceV3.SuccessfulEntry b F (V3CallProducer.admitted selected lo pointer)
      nativeCall (V3CallProducer.plan selected lo pointer))
    (reverting : InterfaceV3.RevertingEntry b F (V3CallProducer.admitted selected lo pointer)
      nativeCall (V3CallProducer.plan selected lo pointer)) :
    BridgeGoal (A (f := f) (args := args) (p := p) (r := r) (destination := destination) (body := body) approved)
      (B selected lo pointer) () () id (fun _ _ => ()) (Local selected lo pointer approved) :=
  ⟨pass selected lo pointer flags approved profile,rfl,rfl,
    local_holds selected lo pointer approved profile flags successful reverting⟩

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
    (successful : InterfaceV3.SuccessfulEntry b F (V3CallProducer.admitted selected lo pointer)
      nativeCall (V3CallProducer.plan selected lo pointer)) :
    ¬ Nonempty (BridgeGoal
      (A (f := f) (args := args) (p := p) (r := r) (destination := destination) (body := body) approved)
      (targetLang [.base .revert] (targetDomain selected lo pointer))
      () () id (fun _ _ => ()) (Local selected lo pointer approved)) := by
  rintro ⟨certificate⟩
  obtain ⟨L,frame,caller,base,machine,start,out,member,entry,executed⟩ := successful
  let e : Input C Γ := ⟨L,frame,caller,base,MachineV2.ofBase machine,start⟩
  have entered : targetDomain selected lo pointer e := member
  have ready : (Behaviour.ofLang
      (A (f := f) (args := args) (p := p) (r := r) (destination := destination) (body := body) approved) ()).Ready
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

end Solidity.Backend.InternalFlow.RuntimeFrame.P1V2ValueBridge
