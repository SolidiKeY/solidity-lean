import Lean

/-!
Read-only elaborated declaration exporter. The source scanner is not the
statement-fidelity authority: this command records actual theorem constants,
including generated/private names, full expression trees and dependent binders.
A Prop binder is not automatically feasible; all witnesses remain pending.
This metaprogram is audit tooling, separate from the dependency-free core.
-/
namespace H62.AuditCalculus
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

/-- Export the actual theorem constants belonging to an imported module.
Output is JSON in the diagnostic stream; the caller stores it outside git. -/
elab "#audit_module " module:str : command => do
  let moduleName := module.getString.toName
  let env ← getEnv
  let records ← liftTermElabM do
    let mut records : Array Json := #[]
    for (name, info) in env.constants.toList do
      if let .thmInfo _ := info then
        if let some idx := env.getModuleIdxFor? name then
          if env.header.moduleNames[idx.toNat]! == moduleName then
            records := records.push (← theoremRecord name info)
    return records
  let records := records.qsort (fun a b => a.compress < b.compress)
  logInfo m!"H62_KERNEL_CENSUS {Json.mkObj [("module", toJson module.getString), ("theorems", Json.arr records)] |>.compress}"

private def jointPremises (info : ConstantInfo) : MetaM Expr := do
  let type := info.type.instantiateLevelParams info.levelParams
    (info.levelParams.map (fun _ => Level.zero))
  forallTelescope type fun xs _ => do
    let mut result := mkConst ``True
    for x in xs.reverse do
      let predicate ← mkLambdaFVars #[x] result
      result ← mkAppM ``Exists #[predicate]
    return result

/-- Generate one existential telescope containing every parameter and proof
premise of the actual theorem constant. Universes are instantiated at zero for
one closed instance. This does not prove the goal, alter the original theorem,
or substitute independently inhabited assumptions for a joint witness. -/
elab "#joint_premises " original:ident " as " target:ident : command => do
  let info ← getConstInfo original.getId
  unless info matches .thmInfo _ do
    throwError "expected an existing theorem constant"
  let proposition ← liftTermElabM <| jointPremises info
  let name := (← getCurrNamespace) ++ target.getId
  liftCoreM <| addAndCompile (.defnDecl {
    name := name, levelParams := [], type := mkSort .zero,
    value := proposition, hints := .abbrev, safety := .safe })

/-- Reconstruct the joint goal independently from the current frozen theorem,
check the proof type, and reject any axiom outside the core trust baseline. -/
elab "#verify_joint " original:ident " with " witness:ident : command => do
  let originalInfo ← getConstInfo original.getId
  let witnessName ← resolveGlobalConstNoOverload witness
  let witnessInfo ← getConstInfo witnessName
  unless originalInfo matches .thmInfo _ do
    throwError "original must be a theorem"
  unless witnessInfo matches .thmInfo _ do
    throwError "witness must be a checked theorem"
  liftTermElabM do
    let expected ← jointPremises originalInfo
    unless ← isDefEq expected witnessInfo.type do
      throwError "witness type does not match the exact joint telescope"
  let env ← getEnv
  let originalModule := (env.getModuleIdxFor? original.getId).map (fun idx => env.header.moduleNames[idx.toNat]!.toString)
  let axioms ← collectAxioms witnessName
  for axiomName in axioms do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "unapproved axiom {axiomName}"
  logInfo m!"H62_JOINT_VERIFIED {Json.mkObj [
    ("original", toJson original.getId.toString),
    ("original_module", toJson originalModule),
    ("witness", toJson witnessName.toString),
    ("original_type_expression", toJson (reprStr originalInfo.type)),
    ("axioms", toJson (axioms.toList.map Name.toString))] |>.compress}"

end H62.AuditCalculus
