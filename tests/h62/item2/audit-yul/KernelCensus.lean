import Lean
/-! Read-only typed census of already checked, unchanged interface modules.
This utility does not create declarations, prove witnesses or change options.
Each declaration gets the normal default Meta budget independently. -/
open Lean Meta

private def describe (n : Name) (ci : ConstantInfo) (moduleName : Name) : MetaM Json := do
  let mut fields : Array Json := #[]
  if let some info := getStructureInfo? (← getEnv) n then
    for i in [:info.fieldNames.size] do
      if let some proj := info.getProjFn? i then
        let f ← getConstInfo proj
        fields := fields.push <| Json.mkObj [
          ("name", toJson proj.toString), ("type_repr", toJson (reprStr f.type)),
          ("pretty_type", toJson (← ppExpr f.type).pretty)]
  let axioms ← collectAxioms n
  forallTelescopeReducing ci.type fun xs result => do
    let mut binders : Array Json := #[]
    for x in xs do
      let binderDecl ← x.fvarId!.getDecl
      binders := binders.push <| Json.mkObj [
        ("name", toJson binderDecl.userName.toString),
        ("binder_info", toJson (reprStr binderDecl.binderInfo)),
        ("pretty_type", toJson (← ppExpr binderDecl.type).pretty),
        ("is_proof", toJson (← isProp binderDecl.type))]
    let range ← findDeclarationRanges? n
    return Json.mkObj [
      ("status", toJson "typed"), ("kernel_name", toJson n.toString),
      ("source_name", toJson ((privateToUserName? n).getD n).toString),
      ("module", toJson moduleName.toString),
      ("kind", toJson (if wasOriginallyTheorem (← getEnv) n then "theorem" else "structure")),
      ("level_parameters", toJson (ci.levelParams.map Name.toString)),
      ("type_repr", toJson (reprStr ci.type)),
      ("pretty_type", toJson (← ppExpr ci.type).pretty),
      ("binders", toJson binders),
      ("result_repr", toJson (reprStr result)),
      ("result_pretty", toJson (← ppExpr result).pretty),
      ("source_range", toJson (range.map fun r => Json.mkObj [
        ("line", toJson r.selectionRange.pos.line),
        ("column", toJson r.selectionRange.pos.column),
        ("end_line", toJson r.range.endPos.line)])),
      ("result_is_false", toJson ((← whnf result).isConstOf ``False)),
      ("fields", toJson fields),
      ("axioms", toJson (axioms.toList.map Name.toString))]

unsafe def main (args : List String) : IO Unit := do
  let ["--modules", listFile, "--output", outputFile] := args
    | throw (IO.userError "expected --modules FILE --output FILE")
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let text ← IO.FS.readFile listFile
  let names := ((text.splitOn "\n").filter (· != "")).toArray.map String.toName
  let imports := #[{ module := `Lean : Import }] ++ names.map fun n => { module := n }
  let env ← importModules imports {} 0 (loadExts := true)
  let targets := env.constants.fold (init := #[]) fun acc n ci =>
    match env.getModuleIdxFor? n with
    | some idx =>
      let moduleName := env.header.moduleNames[idx.toNat]!
      if names.contains moduleName && (wasOriginallyTheorem env n || (getStructureInfo? env n).isSome)
        then acc.push (n, ci, moduleName) else acc
    | none => acc
  let targets := targets.qsort (fun a b => Name.quickLt a.1 b.1)
  let output ← IO.FS.Handle.mk outputFile .write
  for (n, ci, moduleName) in targets do
    try
      let context : Core.Context := {
        fileName := listFile, fileMap := FileMap.ofString "",
        initHeartbeats := (← IO.getNumHeartbeats) }
      let (row, _, _) ← (describe n ci moduleName).toIO context { env := env }
      output.putStrLn row.compress
    catch ex =>
      output.putStrLn <| (Json.mkObj [("status", toJson "error"),
        ("kernel_name", toJson n.toString), ("module", toJson moduleName.toString),
        ("error", toJson ex.toString)]).compress
  output.flush
  IO.println s!"KERNEL_CENSUS_READ: {names.size} modules; {targets.size} declarations (inspect error rows)"
