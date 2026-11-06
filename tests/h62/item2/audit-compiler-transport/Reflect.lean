import Lean

/-! External elaborated census writer. It records every theorem constant and proof-valued definition owned
by the selected imported modules, including proof-field projections and compiler-generated auxiliary names.
A separate join to the frozen source census accounts for auxiliaries explicitly.
Binder classification is syntactic (Prop versus data), not an inhabitation proof.
-/
namespace H62.CompilerTransport
open Lean Meta Elab Command

-- The disposable driver imports its complete frozen module set before any
-- census command. Each direct Lean process gets its own index; no cross-run
-- environment or proof result is reused.
initialize theoremIndex : IO.Ref (Option (Std.HashMap String (Array (Name × ConstantInfo)))) ←
  IO.mkRef none

private def importedTheorems (environment : Environment) : IO (Std.HashMap String (Array (Name × ConstantInfo))) := do
  if let some index ← theoremIndex.get then return index
  let mut index : Std.HashMap String (Array (Name × ConstantInfo)) := {}
  for (name, info) in environment.constants.toList do
    match info with
    | .thmInfo _ | .defnInfo _ | .opaqueInfo _ => pure ()
    | _ => continue
    let some position := environment.getModuleIdxFor? name | continue
    let key := environment.header.moduleNames[position.toNat]!.toString
    index := index.insert key ((index.getD key #[]).push (name, info))
  theoremIndex.set (some index)
  return index

elab "#audit_census " output:str " modules " selected:str : command => do
  let modules := selected.getString.splitOn "\n"
  let environment ← getEnv
  let index ← liftIO (importedTheorems environment)
  let candidates := modules.foldl (fun out key => out ++ index.getD key #[]) #[]
  let mut rows : Array Json := #[]
  for (name, info) in candidates do
    let some index := environment.getModuleIdxFor? name | continue
    let ownerModule := environment.header.moduleNames[index.toNat]!
    unless modules.contains ownerModule.toString do continue
    let proofTyped ← liftTermElabM (isProp info.type)
    unless proofTyped do continue
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "proof-valued-definition"
      | .opaqueInfo _ => "proof-valued-opaque"
      | _ => "unexpected"
    let row ← liftTermElabM do
      let binders ← forallTelescope info.type fun xs result => do
        let mut records : Array Json := #[]
        for x in xs do
          let declaration ← getFVarLocalDecl x
          let head := declaration.type.getAppFn.constName?.getD .anonymous
          let fields := ((getStructureInfo? environment head).map (·.fieldNames) |>.getD #[]).map Name.toString
          records := records.push (Json.mkObj [
            ("name", toJson declaration.userName.toString),
            ("domain_head", toJson head.toString),
            ("domain_structure_fields", toJson fields),
            ("type", toJson (← ppExpr declaration.type).pretty),
            ("domain_is_prop", toJson (← isProp declaration.type)),
            ("binder_info", toJson (reprStr declaration.binderInfo))])
        pure (records, (← ppExpr result).pretty)
      pure (Json.mkObj [
        ("kernel_name", toJson name.toString),
        ("declaration_kind", toJson kind),
        ("proof_field_projection", toJson (environment.getProjectionFnInfo? name).isSome),
        ("declared_type_is_prop", toJson proofTyped),
        ("source_name", toJson (privateToUserName? name |>.getD name).toString),
        ("module", toJson ownerModule.toString),
        ("type", toJson (← ppExpr info.type).pretty),
        ("raw_type", toJson (reprStr info.type)),
        ("level_parameters", toJson (info.levelParams.map Name.toString)),
        ("binders", toJson binders.1),
        ("telescope_result", toJson binders.2),
        ("joint_witness", Json.null)])
    rows := rows.push row
  liftIO <| IO.FS.writeFile output.getString (Json.pretty (toJson rows) ++ "\n")
  logInfo m!"Elaborated {rows.size} theorem constants; simultaneous witnesses remain separate."
end H62.CompilerTransport
