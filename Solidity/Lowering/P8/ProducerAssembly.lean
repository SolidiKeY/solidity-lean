import Solidity.Lowering.P8.FrozenInterface
import Solidity.Lowering.P8.SourceAllSettings

/-! GENERATED frozen H14D admission/assembly boundary. Signatures and explicit
unimplemented obligations only; no AdmissionHalf, PendingGlue or Producer
witness is supplied. VY5's actual reference/origins/failure/realization fields
remain external typed inputs. Original FrozenInterface is unchanged. -/
namespace Solidity.Lowering.P8.ProducerAssembly
open Solidity.Roadmap P8a

/-- This lane owns these fields and their actual-source proofs. Merely
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

/-- Terra fills routine glue only. No instance is supplied or assumed. A
conditional assembler is not a concrete actual-source Producer. -/
structure PendingGlue (S : Spec) (reference : OperationalReference)
    (origins : SourceOrigins S) (roots : RootModel S) where
  componentPipelines : ComponentPipelineClosure
  assemble : AssemblyType S reference origins roots

end Solidity.Lowering.P8.ProducerAssembly
