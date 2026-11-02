import Solidity.Lowering.P8.SourceMetadata
import Solidity.Lowering.P8.SourceResolutionControls
import Solidity.Frontend.Static.InferExamples

/-! Actual source/component controls. No SourceSpec, global imported-name
typing, approved profile completeness or source/EVM execution is inferred. -/
namespace Solidity.Lowering.P8.SourceMetadataControls
open Solidity.Source
open Solidity.Roadmap.Frontend
open Solidity.Frontend.Static
open CheckedSyntax SourceResolutions SourceMetadata

abbrev parsed := CheckedSyntax.Controls.parsedInput
abbrev input := CheckedSyntax.Controls.input

theorem legacy_metadata : metadata (produce (parsed .legacy)) = true := by decide +kernel

theorem viaIR_metadata : metadata (produce (parsed .viaIR)) = true := by decide +kernel

theorem legacy_stages :
    SourceMetadata.checkInput (input .legacy) (parsed .legacy) (produce (parsed .legacy)) CheckedSyntax.Controls.layout = true := by
  rw [SourceMetadata.checkInput, SourceResolutionControls.legacy_input_checked, legacy_metadata]
  rfl

theorem viaIR_stages :
    SourceMetadata.checkInput (input .viaIR) (parsed .viaIR) (produce (parsed .viaIR)) CheckedSyntax.Controls.layout = true := by
  rw [SourceMetadata.checkInput, SourceResolutionControls.viaIR_input_checked, viaIR_metadata]
  rfl

theorem two_unit_metadata : metadata (produce SourceResolutionControls.twoUnits) = true := by decide +kernel

theorem two_unit_stages : SourceMetadata.checkInput SourceResolutionControls.twoInput
    SourceResolutionControls.twoUnits (produce SourceResolutionControls.twoUnits)
    SourceResolutionControls.twoCertificates = true := by
  rw [SourceMetadata.checkInput, SourceResolutionControls.two_input_checked, two_unit_metadata]
  rfl

/-- Existing S01 accepts this initializer, but the stronger existing static
judgment refuses it. Reuse the owning frontend's proofs unchanged. -/
theorem impure_constant_is_wellFormed :
    WellFormed (resolveUnit InferExamples.legacy InferExamples.timestampUnit) :=
  InferExamples.timestamp_wellFormed

theorem impure_constant_refused :
    unitCheck (resolveUnit InferExamples.legacy InferExamples.timestampUnit) = false := by
  cases hb : unitCheck (resolveUnit InferExamples.legacy InferExamples.timestampUnit) with
  | false => rfl
  | true => exact False.elim (InferExamples.timestamp_refused ((unitCheck_iff _).mp hb).1.2.1)

def missingParsed : Parsed := {
  parsed .legacy with units := [("C.sol", .unit (.cons (.importPath "Missing.sol" none) .nil))] }

theorem missing_import_refused : metadata (produce missingParsed) = false := by decide +kernel

theorem wrong_main_refused :
    metadata {produce (parsed .legacy) with main := "Absent.sol"} = false := by decide +kernel

def duplicatePacket : Packet := {
  produce (parsed .legacy) with units := (produce (parsed .legacy)).units ++ (produce (parsed .legacy)).units }

theorem duplicate_names_refused : metadata duplicatePacket = false := by decide +kernel

/-- A global metadata claim cannot be manufactured from raw resolution alone. -/
theorem missing_import_resolution_checked :
    SourceResolutions.check missingParsed (produce missingParsed) = true := produce_checked _

#print axioms legacy_stages
#print axioms viaIR_stages
#print axioms two_unit_stages
#print axioms impure_constant_refused
#print axioms missing_import_refused
#print axioms duplicate_names_refused
end Solidity.Lowering.P8.SourceMetadataControls
