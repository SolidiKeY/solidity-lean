import Lean
import Solidity.Frontend.QualifiedUnits.Checked
import Solidity.Frontend.QualifiedUnits.CheckedControls
import Solidity.Frontend.QualifiedUnits.ConstructorFixtures
import Solidity.Frontend.QualifiedUnits.Controls
import Solidity.Frontend.QualifiedUnits.DifferentialControls
import Solidity.Frontend.QualifiedUnits.Inheritance
import Solidity.Frontend.QualifiedUnits.Layout
import Solidity.Frontend.QualifiedUnits.Linearization
import Solidity.Frontend.QualifiedUnits.Lookup
import Solidity.Frontend.QualifiedUnits.MergeSpecification
import Solidity.Frontend.QualifiedUnits.NormalizationAdequacy
import Solidity.Frontend.QualifiedUnits.NormalizationControls
import Solidity.Frontend.QualifiedUnits.ReferenceControls
import Solidity.Frontend.QualifiedUnits.ReferenceCoverage
import Solidity.Frontend.QualifiedUnits.References
import Solidity.Frontend.QualifiedUnits.Relation
import Solidity.Frontend.QualifiedUnits.SignatureGap
import Solidity.Frontend.QualifiedUnits.SignatureHiding
import Solidity.Frontend.QualifiedUnits.SignatureMemberControls
import Solidity.Frontend.QualifiedUnits.SignatureMembers
import Solidity.Frontend.QualifiedUnits.SignatureNormalization
import Solidity.Frontend.QualifiedUnits.SignatureResolution
import Solidity.Frontend.QualifiedUnits.SignatureResolutionControls
import Solidity.Frontend.QualifiedUnits.Specification
import Solidity.Frontend.QualifiedUnits.Target
import Solidity.Frontend.QualifiedUnits.TargetControls
import Solidity.Frontend.QualifiedUnits.TypePaths
import Solidity.Frontend.QualifiedUnits.UnitPaths

open Lean in
run_cmd do
  let env ← getEnv
  let lanePrefix := `Solidity.Frontend.QualifiedUnits
  let modules := env.header.moduleNames.filter (fun n => lanePrefix.isPrefixOf n)
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[index]!
      if lanePrefix.isPrefixOf moduleName then
        let axioms ← collectAxioms name
        let kind := match info with
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "definition"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quotient"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
        rows := rows.push (Json.mkObj [
          ("name", toJson name.toString),
          ("module", toJson moduleName.toString),
          ("kind", toJson kind),
          ("unsafe", toJson info.isUnsafe),
          ("partial", toJson info.isPartial),
          ("axiom", toJson info.isAxiom),
          ("axioms", toJson (axioms.map (fun n => n.toString)))])
  let report := s!"DECLARATION_INVENTORY {(Json.mkObj [("modules", toJson (modules.map (fun n => n.toString))), ("declarations", Json.arr rows)]).compress}"
  IO.FS.writeFile "tests/sol-qualified-units/claude-evidence/probe-declarations.out" (report ++ "\n")
  logInfo report
