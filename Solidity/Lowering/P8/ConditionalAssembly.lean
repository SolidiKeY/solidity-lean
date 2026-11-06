import Solidity.Lowering.P8.CheckedFrontendAdmission
import Solidity.Lowering.P8.ProducerAssembly
import Solidity.Lowering.P8.DeclarationGraphAdmission

/-! H12 conditional consumer assembly. Missing semantic facts are explicit
structure fields/arguments, not opaque constants or fabricated instances.
Frozen constructors, H15 graph/refusal coverage and every premise are unchanged.
No concrete SourceSpec, resource implementation or actual-source adequacy is
supplied. In particular this does not inhabit the frozen producer over Nat. -/
namespace Solidity.Lowering.P8.ConditionalAssembly
open Solidity.Roadmap P8a

/-- Semantic facts still owed by the approved Source model. None is inferred
from finite controls, metadata closure or uniqueness of admitted resolutions. -/
structure ModelFacts (S : Spec) where
  unambiguous : S.Unambiguous
  approved : S.Approved
  allPipelines : S.AllPipelines
  nonVacuous : S.NonVacuous

variable {S : Spec} {reference : OperationalReference}
  {origins : SourceOrigins S} {roots : RootModel S}

/-- Derive the existing admission half from its real missing facts. Admission
and agreement are implemented, not added as separate pending hypotheses. -/
def admissionHalf (checked : CheckedFrontend S) (extraction : Extractor roots)
    (facts : ModelFacts S) : ProducerAssembly.AdmissionHalf S roots where
  extraction := extraction
  checkedFrontend := checked
  admission := CheckedFrontendAdmission.admission checked
  frontend_agrees := CheckedFrontendAdmission.frontend_agrees checked
  unambiguous := facts.unambiguous
  approved := facts.approved
  allPipelines := facts.allPipelines
  nonVacuous := facts.nonVacuous

def producer (checked : CheckedFrontend S) (extraction : Extractor roots)
    (facts : ModelFacts S) (failures : FailureProjection S)
    (realization : SourceRealization reference origins failures) :
    P8a.Producer S reference origins roots :=
  ProducerAssembly.assemble S reference origins roots failures realization
    (admissionHalf checked extraction facts)

theorem accepted_iff (checked : CheckedFrontend S) (extraction : Extractor roots)
    (facts : ModelFacts S) (failures : FailureProjection S)
    (realization : SourceRealization reference origins failures) (i : S.Input) (r : S.Resolved) :
    (producer checked extraction facts failures realization).admission.frontend i = some r ↔
      S.Admitted i r := CheckedFrontendAdmission.frontend_iff checked i r

theorem accepts_checked (checked : CheckedFrontend S) (extraction : Extractor roots)
    (facts : ModelFacts S) (failures : FailureProjection S)
    (realization : SourceRealization reference origins failures) (i : S.Input)
    (r : S.Resolved) (cert : checked.Cert) (produced : checked.produce i = some (r,cert)) :
    (producer checked extraction facts failures realization).admission.frontend i = some r := by
  change (checked.produce i).map Prod.fst = some r
  rw [produced]
  rfl

/-- The graph/refusal field is the EXACT owner-reviewed H15 Admission, indexed
by this assembled producer. This value remains an explicit V07 obligation. -/
def withGraphs (checked : CheckedFrontend S) (extraction : Extractor roots)
    (facts : ModelFacts S) (failures : FailureProjection S)
    (realization : SourceRealization reference origins failures)
    (graphs : V07.LocationGraphInterface.Admission
      (producer checked extraction facts failures realization)) :
    DeclarationGraphAdmission.Producer S reference origins roots :=
  ⟨producer checked extraction facts failures realization, graphs⟩

/-- Bridge a concrete checked receipt to the exact accepted Source origin,
artifact and admissible-location graph contract. No success oracle or graph
instance is constructed here: the published total Admission field is required. -/
theorem checked_graphs (checked : CheckedFrontend S) (extraction : Extractor roots)
    (facts : ModelFacts S) (failures : FailureProjection S)
    (realization : SourceRealization reference origins failures)
    (graphs : V07.LocationGraphInterface.Admission
      (producer checked extraction facts failures realization))
    (i : S.Input) (r : S.Resolved) (cert : checked.Cert)
    (produced : checked.produce i = some (r,cert)) (art : Artifact) (loc : Source.DataLoc) :
    ∃ n, ∃ G : TypeGraph.Schema n, Nonempty
      (V07.LocationGraphInterface.LocationDeclarationGraph
        (V07.P8Bindings.acceptedSource (producer checked extraction facts failures realization)
          i r (accepts_checked checked extraction facts failures realization i r cert produced) art).1 loc G) :=
  graphs.graphs i r (accepts_checked checked extraction facts failures realization i r cert produced) art loc

/-- Actual Source local-declaration refusal is retained verbatim, rather than
replaced by an all-locations mapping graph or a weakened profile exclusion. -/
theorem checked_source_refuses (checked : CheckedFrontend S) (extraction : Extractor roots)
    (facts : ModelFacts S) (failures : FailureProjection S)
    (realization : SourceRealization reference origins failures)
    (graphs : V07.LocationGraphInterface.Admission
      (producer checked extraction facts failures realization))
    (i : S.Input) (r : S.Resolved) (cert : checked.Cert)
    (produced : checked.produce i = some (r,cert)) (art : Artifact) :
    V07.LocationGraphInterface.SourceRefusesNonAdmissible
      (V07.P8Bindings.acceptedSource (producer checked extraction facts failures realization)
        i r (accepts_checked checked extraction facts failures realization i r cert produced) art).1 :=
  graphs.source_refuses i r (accepts_checked checked extraction facts failures realization i r cert produced) art

/-- info: 'Solidity.Lowering.P8.ConditionalAssembly.admissionHalf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms admissionHalf
/-- info: 'Solidity.Lowering.P8.ConditionalAssembly.producer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms producer
/-- info: 'Solidity.Lowering.P8.ConditionalAssembly.accepted_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_iff
/-- info: 'Solidity.Lowering.P8.ConditionalAssembly.accepts_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepts_checked
/-- info: 'Solidity.Lowering.P8.ConditionalAssembly.checked_graphs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checked_graphs
/-- info: 'Solidity.Lowering.P8.ConditionalAssembly.checked_source_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checked_source_refuses
end Solidity.Lowering.P8.ConditionalAssembly
