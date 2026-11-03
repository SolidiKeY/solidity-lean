import Solidity.Lowering.P8.SourcePrograms
import Solidity.Lowering.P8.SourceMetadataControls

/-! Original-byte certificates to actual Source program controls, not
approved-profile completeness or source/bytecode correspondence. -/
namespace Solidity.Lowering.P8.SourceProgramControls
open Solidity.Source Solidity.Roadmap.Frontend
open SourcePrograms SourceMetadataControls

def admitted (q : Solidity.Frontend.Source.Pipeline) : Option Programs :=
  admit (input q) (parsed q) (SourceResolutions.produce (parsed q)) CheckedSyntax.Controls.layout

def admittedTwo : Option Programs :=
  admit SourceResolutionControls.twoInput SourceResolutionControls.twoUnits
    (SourceResolutions.produce SourceResolutionControls.twoUnits)
    SourceResolutionControls.twoCertificates

def corruptInput : Input := { input .legacy with
  units := [⟨"C.sol", [99,111,110,116,114,97,99,116,32,68,32,123,125]⟩] }
def corrupted : Option Programs :=
  admit corruptInput (parsed .legacy) (SourceResolutions.produce (parsed .legacy))
    CheckedSyntax.Controls.layout

def badTree : Syn .unit := .unit (.cons (.topPart
  (.function (.ident "bad") .nil none none .nil false none .nil
    (.some (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "notDeclared")))) .nil))))) .nil)
def badResolution : Resolution := resolveUnit
  (SourceResolutions.sourceSettings (Settings.ofPipeline .legacy)) badTree

def laterFailure : Option Programs := elaborateUnits
  [("C.sol", resolveUnit (SourceResolutions.sourceSettings (Settings.ofPipeline .legacy))
      CheckedSyntax.Controls.tree), ("Bad.sol", badResolution)]

def emptyInput : Input := { input .legacy with units := [⟨"Empty.sol", []⟩], main := "Empty.sol" }
def emptyParsed : CheckedSyntax.Parsed :=
  ⟨emptyInput.settings, "Empty.sol", [("Empty.sol", .unit .nil)]⟩
def emptyCert : CheckedSyntax.Cert := [⟨[], []⟩]
def emptyAdmitted : Option Programs := admit emptyInput emptyParsed
  (SourceResolutions.produce emptyParsed) emptyCert

/-- Independent minimal kernel witness, separate from the nonempty contract
component controls; no SourceSpec.NonVacuous claim. -/
theorem empty_unit_admitted : emptyAdmitted.map (fun es => es.map Prod.fst) =
    some ["Empty.sol"] := by decide +kernel

theorem bad_unit_refused : (elaborate badResolution).isSome = false := rfl

theorem later_unit_failure_retained : laterFailure.isSome = false := by
  have hb : elaborate badResolution = none := rfl
  have ht : elaborateUnits [("Bad.sol", badResolution)] = none := by
    simp only [elaborateUnits, hb, bind, pure, Option.bind]
  exact congrArg Option.isSome (elaborateUnits_tail_failure _ _ ht)

/-- Original ordered-name expectations, retained unchanged. Kernel proofs
of this full conjunction are exported by SourceProgramAcceptanceControls;
no proof is supplied in this defining module. -/
abbrev ContractControls : Prop :=
  (admitted .legacy).map (fun es => es.map Prod.fst) = some ["C.sol"] ∧
  (admitted .viaIR).map (fun es => es.map Prod.fst) = some ["C.sol"] ∧
  admittedTwo.map (fun es => es.map Prod.fst) = some ["A.sol", "B.sol"] ∧
  corrupted.isSome = false

/-- info: 'Solidity.Lowering.P8.SourceProgramControls.empty_unit_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_unit_admitted
/-- info: 'Solidity.Lowering.P8.SourceProgramControls.bad_unit_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bad_unit_refused
/-- info: 'Solidity.Lowering.P8.SourceProgramControls.later_unit_failure_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms later_unit_failure_retained
end Solidity.Lowering.P8.SourceProgramControls
