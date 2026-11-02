import Solidity.Lowering.P8.FrozenInterface
import Solidity.Lowering.P8b.Frozen

/-! H12 FROZEN additive P8b/P8a interface v1.
This consumes P8a's exact declarations without changing either frozen module.
All structures below are explicit obligation/witness types; no Producer,
SourceSpec, operational reference, emitter or semantic Cert is implemented.
Public signature changes require coordinator notice before editing.
-/
namespace Solidity.Lowering.P8b.P8aInterface
open Roadmap

/-- The exact upstream producer type, not a parallel premise record. -/
abbrev SourceProducer (S : Solidity.Lowering.P8.P8a.Spec) (reference : Solidity.Lowering.P8.P8a.OperationalReference)
    (origins : Solidity.Lowering.P8.P8a.SourceOrigins S) (roots : Solidity.Lowering.P8.P8a.RootModel S) : Type 1 :=
  Solidity.Lowering.P8.P8a.Producer S reference origins roots

/-- Existing frozen P8b output instantiated with the SAME upstream S.
SourceInput's signatures are unchanged; SourceSpec and P8a.Spec are defeq. -/
abbrev ProducerOutput (S : Solidity.Lowering.P8.P8a.Spec) (I : IntrinsicSpec) : Type :=
  Frozen.Producer (Frozen.SourceInput.mk S) I

/-- A real upstream checked-frontend result, indexed by its actual Producer.
The equation is an explicit witness obligation, not a fabricated result. -/
structure CertifiedInput {S : Solidity.Lowering.P8.P8a.Spec} {reference : Solidity.Lowering.P8.P8a.OperationalReference}
    {origins : Solidity.Lowering.P8.P8a.SourceOrigins S} {roots : Solidity.Lowering.P8.P8a.RootModel S}
    (producer : SourceProducer S reference origins roots) (input : S.Input) where
  resolved : S.Resolved
  certificate : producer.checkedFrontend.Cert
  produced : producer.checkedFrontend.produce input=some (resolved,certificate)

end Solidity.Lowering.P8b.P8aInterface
