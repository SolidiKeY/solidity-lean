import tests.h62.item2.«audit-calculus».KernelCensus

/-! Optional bounded exporter for modules exceeding one command budget.
The existing fast exporter and its checked receipts remain unchanged.
Each chunk keeps Lean’s default heartbeat limit; no proof budget is raised. -/
namespace H62.AuditCalculus.ChunkCensus
open Lean Meta Elab Command

private def theoremRecord (name : Name) (info : ConstantInfo) : MetaM Json := do
  let typeText := (← ppExpr info.type).pretty
  let binders ← forallTelescope info.type fun xs _ => do
    xs.mapM fun x => do
      let decl ← x.fvarId!.getDecl
      let type ← inferType x
      return Json.mkObj [
        ("name", toJson decl.userName.toString),
        ("type", toJson (← ppExpr type).pretty),
        ("is_prop", toJson (← isProp type)),
        ("binder_info", toJson (reprStr decl.binderInfo))]
  return Json.mkObj [
    ("name", toJson name.toString),
    ("user_name", toJson ((privateToUserName? name).getD name).toString),
    ("is_private", toJson (isPrivateName name)),
    ("is_internal_detail", toJson name.isInternalDetail),
    ("level_params", toJson (info.levelParams.map Name.toString)),
    ("type_pretty", toJson typeText),
    ("type_expression", toJson (reprStr info.type)),
    ("binders", Json.arr binders),
    ("joint_witness", toJson "pending"),
    ("premise_role", toJson "requires semantic review: global vs per-input")]

/-- Export one bounded portion of a module under the unchanged command budget.
The caller validates that all contiguous portions were emitted exactly once. -/
elab "#audit_module_chunk " module:str " from " offset:num " count " limit:num : command => do
  let moduleName := module.getString.toName
  let first := offset.getNat
  let count := limit.getNat
  unless count > 0 do
    throwError "chunk count must be positive"
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, info) in env.constants.toList do
    if let .thmInfo _ := info then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]! == moduleName then
          names := names.push name
  names := names.qsort (fun a b => a.toString < b.toString)
  let total := names.size
  unless first < total || (first == 0 && total == 0) do
    throwError "chunk offset outside module census"
  let selected := (names.toList.drop first).take count
  let records ← liftTermElabM do
    selected.toArray.mapM fun name => do theoremRecord name (← getConstInfo name)
  logInfo m!"H62_KERNEL_CENSUS_CHUNK {Json.mkObj [
    ("module", toJson module.getString), ("offset", toJson first),
    ("limit", toJson count), ("total", toJson total),
    ("theorems", Json.arr records)] |>.compress}"

end H62.AuditCalculus.ChunkCensus
