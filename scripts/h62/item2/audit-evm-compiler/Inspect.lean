import Lean

/-! Read-only environment census. Output is bulk evidence, not a proof witness. -/
open Lean Meta

def inspectDeclaration (target name : Name) (ci : ConstantInfo) : MetaM Json := do
  let binders ← forallTelescope ci.type fun xs _ => xs.mapM fun x => do
    let decl ← x.fvarId!.getDecl
    let prop ← isProp decl.type
    return Json.mkObj [("name", toJson decl.userName.toString),
      ("type", toJson (← ppExpr decl.type).pretty), ("is_prop_binder", toJson prop)]
  let axioms ← collectAxioms name
  let ranges ← findDeclarationRanges? name
  return Json.mkObj [("name", toJson name.toString),
    ("level_params", toJson (ci.levelParams.map Name.toString)),
    ("source_user_name", toJson (privateToUserName name).toString),
    ("source_line", toJson (ranges.map (·.selectionRange.pos.line))),
    ("premise_classification", toJson "pending-global-versus-per-input"),
    ("module", toJson target.toString), ("type", toJson (← ppExpr ci.type).pretty),
    ("type_expr", toJson (reprStr ci.type)), ("binders", toJson binders),
    ("axioms", toJson (axioms.map Name.toString)),
    ("inspection_budget", toJson "default-per-declaration"),
    ("witness_status", toJson "pending")]

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let namesPath :: modules := args | throw (IO.userError "expected names-file and modules")
  unless modules.length == 1 do throw (IO.userError "inspect one module per process")
  let requested := ((← IO.FS.readFile namesPath).splitOn "\n").toArray
  for arg in modules do
    let target := arg.toName
    let env ← importModules #[{module := target}] {} 0
    let options := Options.empty.setBool `pp.all true
    for (name, ci) in env.constants.toList.mergeSort (fun a b => a.1.toString ≤ b.1.toString) do
      if let .thmInfo _ := ci then
        if let some idx := env.getModuleIdxFor? name then
          if env.header.moduleNames[idx.toNat]! == target &&
              requested.contains ((privateToUserName name).toString.replace "«" "" |>.replace "»" "") then
            -- Fresh default metadata budget per declaration; proof budgets and
            -- the caller's per-process wall/memory bounds remain unchanged.
            let (row, _, _) ← (inspectDeclaration target name ci).toIO
              {fileName := "<audit-census>", fileMap := FileMap.ofString "", options := options}
              {env := env}
            IO.println row.compress
