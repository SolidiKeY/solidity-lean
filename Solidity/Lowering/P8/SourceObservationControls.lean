import Solidity.Lowering.P8.SourceObservationAdmission
import Solidity.Lowering.P8.SourceProgramControls
import Solidity.Frontend.Admission.ProgramObservationControls

/-! Original-byte minimal end-to-end component controls, plus a populated
supplied-Program scan. Neither is full SourceSpec or Source/EVM adequacy. -/
namespace Solidity.Lowering.P8.SourceObservationControls
open Source Roadmap.Frontend Frontend.Admission
open SourceObservationAdmission

def accepted := accept SourceProgramControls.emptyInput SourceProgramControls.emptyParsed
  (SourceResolutions.produce SourceProgramControls.emptyParsed) SourceProgramControls.emptyCert

def changed : Input := {SourceProgramControls.emptyInput with
  units := [⟨"Empty.sol", [255]⟩]}
def refused := accept changed SourceProgramControls.emptyParsed
  (SourceResolutions.produce SourceProgramControls.emptyParsed) SourceProgramControls.emptyCert

abbrev Controls : Prop :=
  accepted.map (fun es => es.map Prod.fst) = some ["Empty.sol"] ∧
  refused.isSome = false ∧
  checkProgram ProgramControls.program = true ∧
  (programObservations ProgramControls.program).length = 7
theorem controls : Controls := by decide

/-- info: 'Solidity.Lowering.P8.SourceObservationControls.controls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms controls
end Solidity.Lowering.P8.SourceObservationControls
