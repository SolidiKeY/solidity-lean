import Solidity.Lowering.P8.SourceMetadata
import Solidity.Frontend.Static.InheritanceExamples

/-! Checked metadata/inheritance controls for the existing fixtures.
These preserve component judgments, not full SourceSpec/profile adequacy,
and do not change the frozen P8a producer interface. -/
namespace Solidity.Lowering.P8.SourceMetadataObligations

abbrev NontrivialPositive : Prop := SourceMetadata.unitCheck (Solidity.Frontend.Static.InheritanceExamples.res Solidity.Frontend.Static.InheritanceExamples.overrideOk) = true
abbrev StrictBeforeRefusal : Prop :=
  Solidity.Frontend.Static.strictMetadataChecker.check (Solidity.Frontend.Static.InheritanceExamples.res Solidity.Frontend.Static.InheritanceExamples.missingVirtual) () () = true
abbrev OverrideRefusal : Prop := SourceMetadata.unitCheck (Solidity.Frontend.Static.InheritanceExamples.res Solidity.Frontend.Static.InheritanceExamples.missingVirtual) = false

/-- Existing metadata fixture conjunction, implemented below. -/
structure PendingControls where
  positive : NontrivialPositive
  strictBeforeRefusal : StrictBeforeRefusal
  refused : OverrideRefusal

theorem nontrivial_positive : NontrivialPositive := rfl
theorem strict_before_refusal : StrictBeforeRefusal := rfl
theorem override_refused : OverrideRefusal := rfl

def checked_controls : PendingControls :=
  ⟨nontrivial_positive, strict_before_refusal, override_refused⟩

/-- info: 'Solidity.Lowering.P8.SourceMetadataObligations.nontrivial_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nontrivial_positive
/-- info: 'Solidity.Lowering.P8.SourceMetadataObligations.strict_before_refusal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms strict_before_refusal
/-- info: 'Solidity.Lowering.P8.SourceMetadataObligations.override_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms override_refused
/-- info: 'Solidity.Lowering.P8.SourceMetadataObligations.checked_controls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checked_controls
end Solidity.Lowering.P8.SourceMetadataObligations
