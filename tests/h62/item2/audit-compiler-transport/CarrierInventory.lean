import Lean

/-! Separate inventory of definitions returning a directly proof-bearing record.
Such values are not proofs merely because their records contain proof fields.
No global inhabitation or per-input feasibility is inferred from this census.
-/
namespace H62.CompilerTransport.CarrierInventory
open Lean Meta Elab Command

initialize valuesIndex : IO.Ref (Option (Std.HashMap String (Array (Name × ConstantInfo)))) ← IO.mkRef none

private def importedValues (environment : Environment) : IO (Std.HashMap String (Array (Name × ConstantInfo))) := do
  if let some index ← valuesIndex.get then return index
  let mut index : Std.HashMap String (Array (Name × ConstantInfo)) := {}
  for (name,info) in environment.constants.toList do
    match info with
    | .defnInfo _ | .opaqueInfo _ => pure ()
    | _ => continue
    let some position := environment.getModuleIdxFor? name | continue
    let key := environment.header.moduleNames[position.toNat]!.toString
    index := index.insert key ((index.getD key #[]).push (name,info))
  valuesIndex.set (some index)
  return index

elab "#audit_carriers " output:str " module " selected:str : command => do
  let environment ← getEnv
  let index ← liftIO (importedValues environment)
  let mut rows : Array Json := #[]
  for (name,info) in index.getD selected.getString #[] do
    let row ← liftTermElabM do
      if ← isProp info.type then return none
      forallTelescope info.type fun parameters body => do
        let resultType ← whnf body
        let head := resultType.getAppFn.constName?.getD .anonymous
        let some structureInfo := getStructureInfo? environment head | return none
        let proofFields ← withLocalDeclD `record resultType fun recordValue => do
          let mut fields : Array String := #[]
          for field in structureInfo.fieldInfo do
            let some projection := environment.getProjectionFnInfo? field.projFn |
              throwError "structure field has no projection metadata: {field.projFn}"
            let arguments := (resultType.getAppArgs.extract 0 projection.numParams).push recordValue
            let value := mkAppN (← mkConstWithFreshMVarLevels field.projFn) arguments
            if ← isProp (← inferType value) then fields := fields.push field.projFn.toString
          return fields
        if proofFields.isEmpty then return none
        let mut binders : Array Json := #[]
        for parameter in parameters do
          let declaration ← getFVarLocalDecl parameter
          binders := binders.push (Json.mkObj [
            ("name",toJson declaration.userName.toString),
            ("type",toJson (← ppExpr declaration.type).pretty),
            ("domain_is_prop",toJson (← isProp declaration.type))])
        return some (Json.mkObj [
          ("kernel_name",toJson name.toString),
          ("source_name",toJson (privateToUserName? name |>.getD name).toString),
          ("module",toJson selected.getString),
          ("type",toJson (← ppExpr info.type).pretty),
          ("raw_type",toJson (reprStr info.type)),
          ("result_structure",toJson head.toString),
          ("direct_proof_fields",toJson proofFields),
          ("binders",toJson binders),
          ("audit_status",toJson "pending coupled global-record and input-domain witness")])
    if let some record := row then rows := rows.push record
  liftIO <| IO.FS.writeFile output.getString (Json.pretty (toJson rows) ++ "\n")
  logInfo m!"Inventoried {rows.size} proof-bearing record producers; none certified inhabited by scanning."
end H62.CompilerTransport.CarrierInventory
