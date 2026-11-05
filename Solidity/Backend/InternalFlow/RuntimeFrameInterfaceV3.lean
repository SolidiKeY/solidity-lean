import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV2

/-! Frozen P1 runtime-frame interface, version 3. Admission is an explicit
external typed input domain, not a field selected by an emitter. Coverage is
universal over the SAME admitted inputs; both source outcomes need real
witnesses. These are pending obligations, not producer instances. The
provenance of the approved source/resource domain must be established
separately; an arbitrary whitelist is not approved-profile coverage. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV3
open Evm Evm.Memory

/-- An initial-input judgment over EXISTING typed states and machines.
There is no default domain and no source/target evaluator here. The approved
judgment must be independently pinned to the actual source/resource profile,
not defined from the candidate emission's Entry predicate or target execution. -/
abbrev Admission (C : Contract) (Γ : Ctx) :=
 (L frame : Nat) → (caller : State C Γ) → (base : Nat → Fin W) →
 (machine : Machine) → (start : Nat) → Prop

/-- Explicit outstanding domain-agreement duty. This does not authenticate
the provenance of `approved`; the source/resource producer must do that. -/
def AdmissionAgreement {C : Contract} {Γ : Ctx}
 (approved admitted : Admission C Γ) : Prop :=
 ∀ L frame caller base machine start,
 approved L frame caller base machine start ↔ admitted L frame caller base machine start

/-- Every admitted input has Entry for EXACTLY that caller, map, machine,
frame and cursor. A producer cannot replace it with a convenient witness. -/
def EntryCoverage {C : Contract} {Γ Δ : Ctx} (b : Nat) (F : Frag Γ)
 (admitted : Admission C Γ) (plan : InterfaceV1.Emission C Γ Δ) : Prop :=
 ∀ L frame caller base machine start,
 admitted L frame caller base machine start →
 InterfaceV1.Entry plan L b frame F caller base machine start

def SuccessfulEntry {C : Contract} {Γ Δ : Ctx} (b : Nat) (F : Frag Γ)
 (admitted : Admission C Γ) (statement : Stmt C Γ Δ)
 (plan : InterfaceV1.Emission C Γ Δ) : Prop :=
 ∃ (L frame : Nat) (caller : State C Γ) (base : Nat → Fin W)
   (machine : Machine) (start : Nat) (out : Solidity.Out C caller.H Δ),
 admitted L frame caller base machine start ∧
 InterfaceV1.Entry plan L b frame F caller base machine start ∧ statement.run caller=.ok out

def RevertingEntry {C : Contract} {Γ Δ : Ctx} (b : Nat) (F : Frag Γ)
 (admitted : Admission C Γ) (statement : Stmt C Γ Δ)
 (plan : InterfaceV1.Emission C Γ Δ) : Prop :=
 ∃ (L frame : Nat) (caller : State C Γ) (base : Nat → Fin W)
   (machine : Machine) (start : Nat),
 admitted L frame caller base machine start ∧
 InterfaceV1.Entry plan L b frame F caller base machine start ∧ statement.run caller=.error .revert

/-- Both outcome witnesses are independently quantified. A success-only
source cannot inhabit this dual-outcome evidence class; that is not a new
source refusal. Its success-only transport remains a separate obligation. -/
structure PendingCallProducer {C : Contract} {Γ Δ ps rs Γf : Ctx}
 (b : Nat) (F : Frag Γ) (approved admitted : Admission C Γ)
 (f : Name) (args : Args C Γ ps) (ret : CallRet Γ rs Δ) (body : Prog C (rs ++ ps) Γf) where
 plan : InterfaceV1.Emission C Γ Δ
 required_profile : AdmissionAgreement approved admitted
 required_coverage : EntryCoverage b F admitted plan
 required_successful_entry : SuccessfulEntry b F admitted (.call f args ret body) plan
 required_reverting_entry : RevertingEntry b F admitted (.call f args ret body) plan
 required_return : InterfaceV1.ReturnClaim b F (.call f args ret body) plan
 required_bare_revert : InterfaceV1.BareRevertClaim b F (.call f args ret body) plan

/-- The domain is independent of the quotation index of the SAME fixed
thunk; coverage applies to every admitted input at every such index. -/
structure PendingFixedCallRecProducer {C : Contract} {Γ Δ ps rs : Ctx}
 (b : Nat) (F : Frag Γ) (approved admitted : Admission C Γ)
 (f : Name) (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
 (body : Unit → Prog C (rs ++ ps) (rs ++ ps)) where
 plan : InterfaceV1.Emission C Γ Δ
 required_profile : AdmissionAgreement approved admitted
 required_coverage : EntryCoverage b F admitted plan
 required_successful_entry : ∀ d, SuccessfulEntry b F admitted (.callRec f d args ret body) plan
 required_reverting_entry : ∀ d, RevertingEntry b F admitted (.callRec f d args ret body) plan
 required_return : ∀ d, InterfaceV1.ReturnClaim b F (.callRec f d args ret body) plan
 required_bare_revert : ∀ d, InterfaceV1.BareRevertClaim b F (.callRec f d args ret body) plan

def FamilyAdmissionAgreement {C : Contract} {Γ : Ctx}
 (approved admitted : Nat → Admission C Γ) : Prop :=
 ∀ n, AdmissionAgreement (approved n) (admitted n)

def FamilyEntryCoverage {C : Contract} {Γ Δ : Ctx} (b : Nat) (F : Frag Γ)
 (admitted : Nat → Admission C Γ) (plan : InterfaceV1.RecursiveEmission C Γ Δ) : Prop :=
 ∀ n, EntryCoverage b F (admitted n) (plan.at n)

/-- Universal coverage at each admitted index, with ONE code image. The
external domain must state genuine physical feasibility; no claim says all
natural indices fit finite word memory, and no emitter depth cutoff is added. -/
structure PendingRecursiveReturns {C : Contract} {Γ Δ ps rs : Ctx}
 (b : Nat) (F : Frag Γ) (approved admitted : Nat → Admission C Γ)
 (f : Name) (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
 (step : Nat → (Unit → Prog C (rs ++ ps) (rs ++ ps)) → Prog C (rs ++ ps) (rs ++ ps)) where
 plan : InterfaceV1.RecursiveEmission C Γ Δ
 required_profile : FamilyAdmissionAgreement approved admitted
 required_coverage : FamilyEntryCoverage b F admitted plan
 required_successful_entry : ∃ n, SuccessfulEntry b F (admitted n)
   (InterfaceV1.recursiveSource f args ret step n) (plan.at n)
 required_reverting_entry : ∃ n, RevertingEntry b F (admitted n)
   (InterfaceV1.recursiveSource f args ret step n) (plan.at n)
 required_source_coherence : InterfaceV1.RecursiveReturnCoherence f args ret step
 required_return : ∀ n, InterfaceV1.ReturnClaim b F (InterfaceV1.recursiveSource f args ret step n) (plan.at n)
 required_bare_revert : ∀ n, InterfaceV1.BareRevertClaim b F (InterfaceV1.recursiveSource f args ret step n) (plan.at n)

/-- The failure-specialized class makes no successful-return assertion. -/
structure PendingBareRevertProducer {C : Contract} {Γ Δ : Ctx}
 (b : Nat) (F : Frag Γ) (approved admitted : Admission C Γ) (statement : Stmt C Γ Δ) where
 plan : InterfaceV1.Emission C Γ Δ
 required_profile : AdmissionAgreement approved admitted
 required_coverage : EntryCoverage b F admitted plan
 required_reverting_entry : RevertingEntry b F admitted statement plan
 required_bare_revert : InterfaceV1.BareRevertClaim b F statement plan

end Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV3
