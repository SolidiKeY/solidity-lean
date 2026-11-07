import Solidity.Lowering.P8.ConditionalAssembly
import Solidity.Lowering.P8.DeclarationGraphAdmissionV2

/-! H57/H128 conditional checked-receipt/program/graph binding.
Regression purpose: keep the same Source program, artifact, graph environment
and v2 local refusal at a genuine produced checker receipt. All model, failure,
realization and graph facts remain explicit; no actual library producer or v1
retirement is provided. Existing generic assembly/origin laws are reused. -/
namespace Solidity.Lowering.P8.ConditionalAssemblyV2
open Solidity.Roadmap P8a

variable {S : Spec} {reference : OperationalReference}
  {origins : SourceOrigins S} {roots : RootModel S}

/-- H57 pair of the conditional v1 constructor, retaining its exact base assembly. -/
def withGraphs (checked : CheckedFrontend S) (extraction : Extractor roots)
    (facts : ConditionalAssembly.ModelFacts S) (failures : FailureProjection S)
    (realization : SourceRealization reference origins failures)
    (graphs : DeclarationGraphAdmissionV2.Admission
      (ConditionalAssembly.producer checked extraction facts failures realization)) :
    DeclarationGraphAdmissionV2.Producer S reference origins roots :=
  ⟨ConditionalAssembly.producer checked extraction facts failures realization, graphs⟩

/-- Reuse v1 graph fields only; this converts no actual v1 typing derivation. -/
def from_v1_graphs (old : DeclarationGraphAdmission.Producer S reference origins roots) :
    DeclarationGraphAdmissionV2.Producer S reference origins roots where
  base := old.base
  declarationGraphs := {
    graphs := old.declarationGraphs.graphs
    source_refuses := fun _ _ _ _ => DeclarationGraphAdmissionV2.source_refuses _ }

/-- A produced receipt binds full program identity, graph and refusal jointly.
The supplied producer still owes actual reference/model/Source adequacy. -/
theorem checked_contract (producer : DeclarationGraphAdmissionV2.Producer S reference origins roots)
    (i : S.Input) (r : S.Resolved) (cert : producer.base.checkedFrontend.Cert)
    (produced : producer.base.checkedFrontend.produce i = some (r, cert))
    (art : Artifact) (loc : Source.DataLoc) :
    let admitted := V07.P8Bindings.checked_frontend_agrees producer.base i r cert produced
    let profile := V07.P8Bindings.accepted_profile producer.base i r admitted
    let accepted := V07.P8Bindings.acceptedSource producer.base i r admitted art
    let realized := producer.base.realization.program (S.meaning r profile.1 profile.2 art)
    realized = accepted ∧ ∃ n, ∃ G : TypeGraph.Schema n,
      Nonempty (V07.LocationGraphInterface.LocationDeclarationGraph realized.1 loc G) ∧
      DeclarationGraphAdmissionV2.SourceRefusesNonAdmissible realized.1 := by
  dsimp only
  have identity := V07.P8Bindings.program_origin producer.base i r
    (V07.P8Bindings.checked_frontend_agrees producer.base i r cert produced) art
  constructor
  · exact identity
  · rw [identity]
    obtain ⟨n, G, certificate⟩ := producer.declarationGraphs.graphs i r
      (V07.P8Bindings.checked_frontend_agrees producer.base i r cert produced) art loc
    exact ⟨n, G, certificate, producer.declarationGraphs.source_refuses i r
      (V07.P8Bindings.checked_frontend_agrees producer.base i r cert produced) art⟩

/-- A refused checker receipt cannot be produced. A different valid certificate
is not excluded by this fixed-receipt statement. -/
theorem rejected_receipt (producer : DeclarationGraphAdmissionV2.Producer S reference origins roots)
    (i : S.Input) (r : S.Resolved) (cert : producer.base.checkedFrontend.Cert)
    (refused : producer.base.checkedFrontend.check i r cert = false) :
    producer.base.checkedFrontend.produce i ≠ some (r, cert) :=
  CheckedFrontendAdmission.check_false_refuses producer.base.checkedFrontend i r cert refused

/-- info: 'Solidity.Lowering.P8.ConditionalAssemblyV2.withGraphs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms withGraphs
/-- info: 'Solidity.Lowering.P8.ConditionalAssemblyV2.from_v1_graphs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms from_v1_graphs
/-- info: 'Solidity.Lowering.P8.ConditionalAssemblyV2.checked_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checked_contract
/-- info: 'Solidity.Lowering.P8.ConditionalAssemblyV2.rejected_receipt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rejected_receipt
end Solidity.Lowering.P8.ConditionalAssemblyV2
