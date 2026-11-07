import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV3

/-! Frozen P1 runtime-frame interface, version 4: the success-only companion
of version 3 (an H57 pair; V3 is unchanged and stays frozen).

V3 asks every producer for an admitted bare-reverting entry, so a source that
never bare-reverts cannot inhabit it (`V3GeneralBoundary.no_recursive_producer`).
V4 keeps every V3 field except `required_reverting_entry`: the same external
admission domain and agreement duty, universal Entry coverage, an admitted
successful entry, the universal `ReturnClaim`, the universal (conditional)
`BareRevertClaim` and, for recursive families, source coherence. Dropping the
reverting witness only removes a non-vacuity witness; no claim is weakened,
but a V4 producer's `BareRevertClaim` may then hold only vacuously.

These are signatures and pending duties only, with no instance. Provenance of
the approved domain stays external, exactly as in V3; panic, payload,
exhaustion, running prefixes and divergence are not covered. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV4
open Evm Evm.Memory
open InterfaceV3 (Admission AdmissionAgreement EntryCoverage SuccessfulEntry
  FamilyAdmissionAgreement FamilyEntryCoverage)

/-- Success-only ordinary call producer. -/
structure PendingCallProducer {C : Contract} {Γ Δ ps rs Γf : Ctx}
    (b : Nat) (F : Frag Γ) (approved admitted : Admission C Γ)
    (f : Name) (args : Args C Γ ps) (ret : CallRet Γ rs Δ) (body : Prog C (rs ++ ps) Γf) where
  plan : InterfaceV1.Emission C Γ Δ
  required_profile : AdmissionAgreement approved admitted
  required_coverage : EntryCoverage b F admitted plan
  required_successful_entry : SuccessfulEntry b F admitted (.call f args ret body) plan
  required_return : InterfaceV1.ReturnClaim b F (.call f args ret body) plan
  required_bare_revert : InterfaceV1.BareRevertClaim b F (.call f args ret body) plan

/-- Success-only fixed-thunk producer, at every quotation index. -/
structure PendingFixedCallRecProducer {C : Contract} {Γ Δ ps rs : Ctx}
    (b : Nat) (F : Frag Γ) (approved admitted : Admission C Γ)
    (f : Name) (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
    (body : Unit → Prog C (rs ++ ps) (rs ++ ps)) where
  plan : InterfaceV1.Emission C Γ Δ
  required_profile : AdmissionAgreement approved admitted
  required_coverage : EntryCoverage b F admitted plan
  required_successful_entry : ∀ d, SuccessfulEntry b F admitted (.callRec f d args ret body) plan
  required_return : ∀ d, InterfaceV1.ReturnClaim b F (.callRec f d args ret body) plan
  required_bare_revert : ∀ d, InterfaceV1.BareRevertClaim b F (.callRec f d args ret body) plan

/-- Success-only recursive family with ONE code image. Coherence stays: two
successful indices from one caller must agree, as one image requires. -/
structure PendingRecursiveReturns {C : Contract} {Γ Δ ps rs : Ctx}
    (b : Nat) (F : Frag Γ) (approved admitted : Nat → Admission C Γ)
    (f : Name) (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
    (step : Nat → (Unit → Prog C (rs ++ ps) (rs ++ ps)) → Prog C (rs ++ ps) (rs ++ ps)) where
  plan : InterfaceV1.RecursiveEmission C Γ Δ
  required_profile : FamilyAdmissionAgreement approved admitted
  required_coverage : FamilyEntryCoverage b F admitted plan
  required_successful_entry : ∃ n, SuccessfulEntry b F (admitted n)
    (InterfaceV1.recursiveSource f args ret step n) (plan.at n)
  required_source_coherence : InterfaceV1.RecursiveReturnCoherence f args ret step
  required_return : ∀ n, InterfaceV1.ReturnClaim b F
    (InterfaceV1.recursiveSource f args ret step n) (plan.at n)
  required_bare_revert : ∀ n, InterfaceV1.BareRevertClaim b F
    (InterfaceV1.recursiveSource f args ret step n) (plan.at n)

end Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV4
