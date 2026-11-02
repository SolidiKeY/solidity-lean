import Solidity.Lowering.P8.SourceResolutions

/-! Inhabited raw/parse/source-resolution controls, not a SourceSpec or a
claim that raw/per-unit resolution entails global typing or execution. -/
namespace Solidity.Lowering.P8.SourceResolutionControls
open Solidity.Roadmap.Frontend
open CheckedSyntax SourceResolutions

abbrev parsed := CheckedSyntax.Controls.parsedInput
abbrev input := CheckedSyntax.Controls.input

theorem legacy_resolved : check (parsed .legacy) (produce (parsed .legacy)) = true :=
  produce_checked _
theorem viaIR_resolved : check (parsed .viaIR) (produce (parsed .viaIR)) = true :=
  produce_checked _

theorem legacy_input_checked :
    checkInput (input .legacy) (parsed .legacy) (produce (parsed .legacy)) CheckedSyntax.Controls.layout = true := by
  rw [checkInput, produce_checked, CheckedSyntax.Controls.legacy_certificate_checked]
  rfl

theorem viaIR_input_checked :
    checkInput (input .viaIR) (parsed .viaIR) (produce (parsed .viaIR)) CheckedSyntax.Controls.layout = true := by
  rw [checkInput, produce_checked, CheckedSyntax.Controls.viaIR_certificate_checked]
  rfl

theorem wrong_settings_refused :
    check (parsed .legacy) (produce (parsed .viaIR)) = false := by decide +kernel

theorem wrong_main_refused :
    check (parsed .legacy) {produce (parsed .legacy) with main := "Other.sol"} = false := by decide +kernel

theorem missing_unit_refused :
    check (parsed .legacy) {produce (parsed .legacy) with units := []} = false := by decide +kernel

def twoUnits : Parsed := {
  parsed .legacy with main := "A.sol", units := [("A.sol", CheckedSyntax.Controls.tree), ("B.sol", CheckedSyntax.Controls.tree)] }

theorem both_units_preserved :
    (produce twoUnits).units.map Prod.fst = ["A.sol", "B.sol"] := rfl

theorem both_units_checked : check twoUnits (produce twoUnits) = true := produce_checked _

theorem reversed_units_refused :
    check twoUnits {produce twoUnits with units := (produce twoUnits).units.reverse} = false := by decide +kernel

theorem duplicate_resolution_refused :
    check twoUnits {produce twoUnits with units := (produce (parsed .legacy)).units ++ (produce (parsed .legacy)).units} = false := by decide +kernel

/-- Wrong source-unit identity is rejected even for identical source trees. -/
theorem same_tree_wrong_name_refused :
    check (parsed .legacy) {produce (parsed .legacy) with units := [("Wrong.sol", Source.resolveUnit (sourceSettings (parsed .legacy).settings) CheckedSyntax.Controls.tree)]} = false := by decide +kernel

theorem missing_parse_certificate_refused :
    checkInput (input .legacy) (parsed .legacy) (produce (parsed .legacy)) [] = false := by decide +kernel

def wrongPipeline : Packet := {produce (parsed .legacy) with units := [
  ("C.sol", {Source.resolveUnit (sourceSettings (parsed .legacy).settings) CheckedSyntax.Controls.tree
    with pipeline := .viaIR})] }

/-- Packet tags, names, unit count and syntax are correct; the source
resolution's own pipeline is deliberately corrupted. -/
theorem source_pipeline_corruption_refused : check (parsed .legacy) wrongPipeline = false := by
  cases hb : check (parsed .legacy) wrongPipeline with
  | false => rfl
  | true =>
    have h := (check_iff _ _).mp hb
    have he := congrArg Source.Resolution.pipeline h.2.2.1.2.2
    change Roadmap.Pipeline.viaIR = Roadmap.Pipeline.legacy at he
    cases he

def wrongCoder : Packet := {produce (parsed .legacy) with units := [
  ("C.sol", {Source.resolveUnit (sourceSettings (parsed .legacy).settings) CheckedSyntax.Controls.tree
    with coder := .v1})] }

theorem source_coder_corruption_refused : check (parsed .legacy) wrongCoder = false := by
  cases hb : check (parsed .legacy) wrongCoder with
  | false => rfl
  | true =>
    have h := (check_iff _ _).mp hb
    have he := congrArg Source.Resolution.coder h.2.2.1.2.2
    change Roadmap.AbiCoder.v1 = Roadmap.AbiCoder.v2 at he
    cases he

def linkedInput : Input := {input .legacy with settings := {
  (input .legacy).settings with links := [⟨"C.sol", "L", 291⟩]} }

def linkedParsed : Parsed := {parsed .legacy with settings := linkedInput.settings}

theorem linked_parse_checked :
    CheckedSyntax.check linkedInput linkedParsed CheckedSyntax.Controls.layout = true := by decide +kernel

theorem linked_resolution_checked : check linkedParsed (produce linkedParsed) = true := produce_checked _

/-- Tags and both later stages match. The ORIGINAL raw-input link restriction
is responsible for refusal; tag mismatch cannot mask a missing guard. -/
theorem nonempty_links_refused :
    checkInput linkedInput linkedParsed (produce linkedParsed) CheckedSyntax.Controls.layout = false := by decide +kernel

def twoInput : Input := {
  units := [⟨"A.sol", [99,111,110,116,114,97,99,116,32,67,32,123,125]⟩,
    ⟨"B.sol", [99,111,110,116,114,97,99,116,32,67,32,123,125]⟩]
  main := "A.sol", settings := Settings.ofPipeline .legacy }

def twoCertificates : CheckedSyntax.Cert := [
  ⟨CheckedSyntax.Controls.pieces, []⟩, ⟨CheckedSyntax.Controls.pieces, []⟩]

/-- A nonempty TWO-unit raw/byte-parse/per-unit-resolution chain. It still
claims no global import typing, profile verdict or source execution. -/
theorem two_input_checked : checkInput twoInput twoUnits (produce twoUnits) twoCertificates = true := by
  rw [checkInput, produce_checked]
  decide +kernel

def pragmaV1 : Source.Syn .unit := .unit (.cons (.pragma ["abicoder", "v1"]) .nil)

theorem legacy_pragma_v1 :
    (Source.resolveUnit (sourceSettings (Settings.ofPipeline .legacy)) pragmaV1).coder = .v1 := rfl

theorem viaIR_forces_v2 :
    (Source.resolveUnit (sourceSettings (Settings.ofPipeline .viaIR)) pragmaV1).coder = .v2 := rfl

#print axioms two_input_checked
#print axioms legacy_pragma_v1
#print axioms viaIR_forces_v2
#print axioms source_pipeline_corruption_refused
#print axioms source_coder_corruption_refused
#print axioms nonempty_links_refused
#print axioms legacy_input_checked
#print axioms viaIR_input_checked
#print axioms wrong_settings_refused
#print axioms missing_unit_refused
#print axioms reversed_units_refused
#print axioms same_tree_wrong_name_refused
end Solidity.Lowering.P8.SourceResolutionControls
