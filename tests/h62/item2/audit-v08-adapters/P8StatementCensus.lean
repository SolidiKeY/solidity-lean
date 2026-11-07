import Lean
import Solidity.Lowering.P8.FrozenInterface
import Solidity.Lowering.V08.EnvironmentProjection
import Solidity.Lowering.V08.ConstructorScalarTransport
import Solidity.Lowering.V08.LibraryFrameTransport
import Solidity.Lowering.V08.CreationPremises
import Solidity.Lowering.V08.LibraryPremises

/-! Kernel-environment census, including exact elaborated types and imported
defining-module provenance. Guards omission of proof projections, predicate
definitions and generated declarations from lexical-only audits. The separate
world-agreement marker extends inventory without changing P8 consumer input.
Set H62_WORLD_CENSUS=1 to opt into this additional diagnostic work.
Metaprogramming remains under tests; the core is unchanged. -/
open Lean Elab Command Meta

run_cmd do
  let environment ← getEnv
  let includeWorld ← liftIO <| IO.getEnv "H62_WORLD_CENSUS"
  let targets : Array (Name × String) := if includeWorld == some "1" then #[
    (`Solidity.Lowering.P8.FrozenInterface, "H62_CENSUS_JSON "),
    (`Solidity.Lowering.V08.EnvironmentProjection, "H62_WORLD_CENSUS_JSON "),
    (`Solidity.Lowering.V08.ConstructorScalarTransport, "H62_WORLD_CENSUS_JSON "),
    (`Solidity.Lowering.V08.LibraryFrameTransport, "H62_WORLD_CENSUS_JSON "),
    (`Solidity.Lowering.V08.CreationPremises, "H62_WORLD_CENSUS_JSON "),
    (`Solidity.Lowering.V08.LibraryPremises, "H62_WORLD_CENSUS_JSON ")
  ] else #[(`Solidity.Lowering.P8.FrozenInterface, "H62_CENSUS_JSON ")]
  let constants := environment.constants.toList.mergeSort (fun a b => a.1.toString ≤ b.1.toString)
  for (name, info) in constants do
    let some index := environment.getModuleIdxFor? name | continue
    let target := environment.header.moduleNames[index]!
    let some marker := targets.findSome? (fun entry =>
      if entry.1 == target then some entry.2 else none) | continue
    let theoremDecl := getOriginalConstKind? environment name == some ConstantKind.thm
    let isProof ← liftTermElabM <| isProp info.type
    let returnsProp ← liftTermElabM do
      forallTelescope info.type fun _ result => pure (result == mkSort Level.zero)
    let projection := environment.getProjectionFnInfo? name
    let kind := if theoremDecl then "theorem"
      else if projection.isSome then (if isProof then "proof_projection" else "data_projection")
      else if (getStructureInfo? environment name).isSome then "structure_carrier"
      else if returnsProp then "predicate_definition"
      else if isProof then "proof_definition"
      else "other_declaration"
    let value := match info with
      | .defnInfo v => some (reprStr v.value)
      | _ => none
    let binders ← liftTermElabM do
      forallTelescope info.type fun values _ => values.mapM fun value => do
        let declaration ← value.fvarId!.getDecl
        let proposition ← isProp declaration.type
        pure <| Json.mkObj [("name", toJson declaration.userName.toString),
          ("is_proposition", toJson proposition)]
    let axioms ← collectAxioms name
    let pretty ← liftTermElabM <| ppExpr info.type
    let fields : Array Json := match getStructureInfo? environment name with
      | none => #[]
      | some structureInfo => structureInfo.fieldInfo.map fun (field : StructureFieldInfo) =>
          Json.mkObj [("field", toJson field.fieldName.toString), ("projection", toJson field.projFn.toString)]
    let row := Json.mkObj [("name", toJson name.toString),
      ("kind", toJson kind), ("is_proof", toJson isProof),
      ("is_theorem", toJson theoremDecl), ("has_projection_info", toJson projection.isSome),
      ("structure_fields", toJson fields),
      ("level_parameters", toJson (info.levelParams.map Name.toString)),
      ("value_expr", toJson value),
      ("module", toJson target.toString), ("type_expr", toJson (reprStr info.type)),
      ("type_pretty", toJson pretty.pretty), ("binders", toJson binders),
      ("axioms", toJson (axioms.map Name.toString))]
    liftIO <| IO.println (marker ++ row.compress)
