import Solidity.Lowering.P8.SourceMetadata
import Solidity.Frontend.Static.InheritanceExamples

/-! GENERATED pending routine control interface (H14). Proposition aliases
and explicit proof obligations only. No witness, axiom or completed control
is exported. M02 is a proposed, unvalidated fixture statement. This does
not change the frozen P8a producer interface. -/
namespace Solidity.Lowering.P8.SourceMetadataObligations

abbrev NontrivialPositive : Prop := SourceMetadata.unitCheck (Solidity.Frontend.Static.InheritanceExamples.res Solidity.Frontend.Static.InheritanceExamples.overrideOk) = true
abbrev StrictBeforeRefusal : Prop :=
  Solidity.Frontend.Static.strictMetadataChecker.check (Solidity.Frontend.Static.InheritanceExamples.res Solidity.Frontend.Static.InheritanceExamples.missingVirtual) () () = true
abbrev OverrideRefusal : Prop := SourceMetadata.unitCheck (Solidity.Frontend.Static.InheritanceExamples.res Solidity.Frontend.Static.InheritanceExamples.missingVirtual) = false

/-- Open proof fields; no inhabitant is supplied. -/
structure PendingControls where
  positive : NontrivialPositive
  strictBeforeRefusal : StrictBeforeRefusal
  refused : OverrideRefusal

end Solidity.Lowering.P8.SourceMetadataObligations
