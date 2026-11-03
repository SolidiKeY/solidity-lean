import Solidity.Lowering.P8.FrozenInterface
import Solidity.Lowering.P8.SourceAllSettings

/-! Frozen H14D admission/assembly boundary and checked conditional glue.
No actual AdmissionHalf or concrete Source Producer witness is supplied. The
reference/origins/failure/realization fields remain external typed inputs. Original FrozenInterface is unchanged. -/
namespace Solidity.Lowering.P8.ProducerAssembly
open Solidity.Roadmap P8a

/-- The admission fields, whose actual-source proofs are still owed. Merely
accepting them as parameters does not implement admission. -/
structure AdmissionHalf (S : Spec) (roots : RootModel S) where
  extraction : Extractor roots
  checkedFrontend : CheckedFrontend S
  admission : Admission S
  frontend_agrees : ∀ i, admission.frontend i = (checkedFrontend.produce i).map Prod.fst
  unambiguous : S.Unambiguous
  approved : S.Approved
  allPipelines : S.AllPipelines
  nonVacuous : S.NonVacuous

abbrev AssemblyType (S : Spec) (reference : OperationalReference)
    (origins : SourceOrigins S) (roots : RootModel S) :=
  (failures : FailureProjection S) → SourceRealization reference origins failures →
    AdmissionHalf S roots → Producer S reference origins roots

/-- Routine specialization of the proved component settings closure, not the
full SourceSpec.AllPipelines field of AdmissionHalf. -/
abbrev ComponentPipelineClosure : Prop :=
  ∀ (i : Frontend.Input) (p : CheckedSyntax.Parsed) (r : SourceResolutions.Packet)
    (c : CheckedSyntax.Cert) (q : Solidity.Frontend.Source.Pipeline),
    SourceMetadata.checkInput i p r c = true →
    SourceMetadata.checkInput {i with settings := Frontend.Settings.ofPipeline q}
      {p with settings := Frontend.Settings.ofPipeline q}
      (SourceResolutions.produce {p with settings := Frontend.Settings.ofPipeline q}) c = true

/-- Conditional glue, implemented below. A conditional assembler is not a
concrete actual-source Producer. -/
structure PendingGlue (S : Spec) (reference : OperationalReference)
    (origins : SourceOrigins S) (roots : RootModel S) where
  componentPipelines : ComponentPipelineClosure
  assemble : AssemblyType S reference origins roots

theorem component_pipeline_closure : ComponentPipelineClosure := by
  intro i p r c q h
  exact Solidity.Lowering.P8.SourceAllSettings.input_settings i p r c
    (Solidity.Roadmap.Frontend.Settings.ofPipeline q) h
    (Solidity.Roadmap.Frontend.Settings.ok_ofPipeline q)

/-- info: 'Solidity.Lowering.P8.ProducerAssembly.component_pipeline_closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms component_pipeline_closure

def assemble : ∀ (S : Solidity.Lowering.P8.P8a.Spec) (reference : Solidity.Lowering.P8.P8a.OperationalReference) (origins : Solidity.Lowering.P8.P8a.SourceOrigins S) (roots : Solidity.Lowering.P8.P8a.RootModel S), Solidity.Lowering.P8.ProducerAssembly.AssemblyType S reference origins roots := by
  intro S reference origins roots f real half
  exact ⟨f, real, half.extraction, half.checkedFrontend, half.admission,
    half.frontend_agrees, half.unambiguous, half.approved, half.allPipelines, half.nonVacuous⟩

/-- info: 'Solidity.Lowering.P8.ProducerAssembly.assemble' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms assemble

def checked_glue (S : Spec) (reference : OperationalReference)
    (origins : SourceOrigins S) (roots : RootModel S) : PendingGlue S reference origins roots :=
  ⟨component_pipeline_closure, assemble S reference origins roots⟩

/-- info: 'Solidity.Lowering.P8.ProducerAssembly.checked_glue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checked_glue
end Solidity.Lowering.P8.ProducerAssembly
