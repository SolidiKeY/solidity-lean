import Solidity.Lowering.P8.ResourceContractLaw1
import Solidity.Lowering.P8.ProducerAssembly

/-! V2 failure boundary. V1 remains frozen. SourceSpec.failures_with
retracts resources onto abstract failures; it does NOT imply a retraction from
abstract failures onto all EVM plans. FullPlanCoverage is that second,
independent obligation. Splitting it out does not make it optional: every
complete projection and Producer below still requires it. This is a lossless
clarification, not a Nat semantics repair or a resource-extension approval. -/
namespace Solidity.Lowering.P8.FailureContractV2
open Solidity.Roadmap P8a

structure Projection (S : Spec) where
  points : S.Failures → Evm.FailurePoints
  noFail_requests : ∀ f, S.NoFail f → ∀ i, ∃ balance,
    (points f).tx i = .runs balance none
  noFail_frames : ∀ f, S.NoFail f → ∀ k, (points f).frame k = none

/-- Independent full-plan coverage: every request/frame schedule, not only
realizable samples or failure-free/finite prefixes. -/
structure FullPlanCoverage {S : Spec} (projection : Projection S) where
  ofPoints : Evm.FailurePoints → S.Failures
  points_ofPoints : ∀ p, projection.points (ofPoints p) = p

structure CompleteProjection (S : Spec) where
  projection : Projection S
  coverage : FullPlanCoverage projection

def CompleteProjection.toV1 {S : Spec} (f : CompleteProjection S) :
    P8a.FailureProjection S where
  points := f.projection.points
  ofPoints := f.coverage.ofPoints
  points_ofPoints := f.coverage.points_ofPoints
  noFail_requests := f.projection.noFail_requests
  noFail_frames := f.projection.noFail_frames

def CompleteProjection.ofV1 {S : Spec} (f : P8a.FailureProjection S) :
    CompleteProjection S where
  projection := ⟨f.points, f.noFail_requests, f.noFail_frames⟩
  coverage := ⟨f.ofPoints, f.points_ofPoints⟩

theorem CompleteProjection.toV1_ofV1 {S : Spec} (f : P8a.FailureProjection S) :
    (ofV1 f).toV1 = f := by rfl

theorem CompleteProjection.ofV1_toV1 {S : Spec} (f : CompleteProjection S) :
    ofV1 f.toV1 = f := by rfl

/-- All original admission and operational obligations remain mandatory. -/
structure Producer (S : Spec) (reference : OperationalReference)
    (origins : SourceOrigins S) (roots : RootModel S) where
  failures : CompleteProjection S
  realization : SourceRealization reference origins failures.toV1
  admission : ProducerAssembly.AdmissionHalf S roots

def Producer.toV1 {S : Spec} {reference : OperationalReference}
    {origins : SourceOrigins S} {roots : RootModel S}
    (p : Producer S reference origins roots) : P8a.Producer S reference origins roots where
  failures := p.failures.toV1
  realization := p.realization
  extraction := p.admission.extraction
  checkedFrontend := p.admission.checkedFrontend
  admission := p.admission.admission
  frontend_agrees := p.admission.frontend_agrees
  unambiguous := p.admission.unambiguous
  approved := p.admission.approved
  allPipelines := p.admission.allPipelines
  nonVacuous := p.admission.nonVacuous

def Producer.ofV1 {S : Spec} {reference : OperationalReference}
    {origins : SourceOrigins S} {roots : RootModel S}
    (p : P8a.Producer S reference origins roots) : Producer S reference origins roots where
  failures := CompleteProjection.ofV1 p.failures
  realization := p.realization
  admission := ⟨p.extraction, p.checkedFrontend, p.admission, p.frontend_agrees,
    p.unambiguous, p.approved, p.allPipelines, p.nonVacuous⟩

theorem Producer.toV1_ofV1 {S : Spec} {reference : OperationalReference}
    {origins : SourceOrigins S} {roots : RootModel S}
    (p : P8a.Producer S reference origins roots) : (ofV1 p).toV1 = p := by rfl

theorem Producer.ofV1_toV1 {S : Spec} {reference : OperationalReference}
    {origins : SourceOrigins S} {roots : RootModel S}
    (p : Producer S reference origins roots) : ofV1 p.toV1 = p := by rfl

/-- V2 retains the obstruction, rather than hiding it behind optional coverage. -/
theorem nat_encodable_resource_impossible (S : Spec) (f : CompleteProjection S)
    (encode : S.lang.Res → Nat) (decode : Nat → S.lang.Res)
    (roundtrip : ∀ r, decode (encode r) = r) : False :=
  ResourceContractLaw1.nat_encodable_resource_impossible S f.toV1 encode decode roundtrip

#print axioms CompleteProjection.toV1_ofV1
#print axioms Producer.toV1_ofV1
#print axioms nat_encodable_resource_impossible
end Solidity.Lowering.P8.FailureContractV2
