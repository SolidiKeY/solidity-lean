import Solidity.Automation.H28.Context
import Lean

open Lean Elab Term Command Meta
set_option Elab.async false

elab "h28_type% " id:ident : term => do
  return (← getConstInfo id.getId).type

elab "#h28_mark " label:str : command => do
  let ticks ← IO.monoNanosNow
  let beats ← IO.getNumHeartbeats
  let budget := maxHeartbeats.get (← getOptions)
  logInfo m!"H28_MARK {label.getString} {ticks} {beats} {budget}"

elab "#h28_assert_exact " original:ident tested:ident : command => do
  let sourceInfo ← getConstInfo original.getId
  let testedInfo ← getConstInfo tested.getId
  unless testedInfo.type == sourceInfo.type do
    throwError "single-goal control changed the original theorem type"
  logInfo m!"H28_TYPE_OK {tested.getId}"

elab "#h28_assert_combine " left:ident right:ident tested:ident : command => do
  let leftInfo ← getConstInfo left.getId
  let rightInfo ← getConstInfo right.getId
  let testedInfo ← getConstInfo tested.getId
  unless testedInfo.type == mkApp2 (mkConst ``And) leftInfo.type rightInfo.type do
    throwError "benchmark changed the exact conjunction of the original theorem types"
  logInfo m!"H28_TYPE_OK {tested.getId}"


elab "h28_pointwise_pair% " id:ident : term => do
  let info ← getConstInfo id.getId
  return ← forallTelescope info.type fun args body =>
    mkForallFVars args (mkApp2 (mkConst (Name.str .anonymous "And")) body body)

elab "#h28_assert_pointwise " original:ident tested:ident : command => do
  let sourceInfo ← getConstInfo original.getId
  let testedInfo ← getConstInfo tested.getId
  let expected ← liftTermElabM do
    return ← forallTelescope sourceInfo.type fun args body =>
      mkForallFVars args (mkApp2 (mkConst (Name.str .anonymous "And")) body body)
  unless testedInfo.type == expected do
    throwError "pointwise control changed original binders or statement"
  logInfo m!"H28_TYPE_OK {tested.getId}"

elab "#h28_audit " id:ident : command => do
  let info ← getConstInfo id.getId
  let axioms ← collectAxioms id.getId
  let entries ← axioms.mapM fun axiomName => do
    let axiomInfo ← getConstInfo axiomName
    return Json.mkObj [("name", toJson axiomName.toString),
      ("signature", toJson (reprStr axiomInfo.type))]
  let payload := Json.mkObj [("name", toJson id.getId.toString),
    ("signature", toJson (reprStr info.type)),
    ("proof_nodes", toJson info.value!.sizeWithoutSharing),
    ("axioms", Json.arr entries)]
  logInfo m!"H28_AUDIT {payload.compress}"
  let ticks ← IO.monoNanosNow
  let beats ← IO.getNumHeartbeats
  liftTermElabM do
    addDecl <| Declaration.thmDecl {
      name := Name.str info.name "kernelReplay"
      levelParams := info.levelParams
      type := info.type
      value := info.value!
    }
  let ticksAfter ← IO.monoNanosNow
  let beatsAfter ← IO.getNumHeartbeats
  logInfo m!"H28_REPLAY {id.getId} {ticksAfter - ticks} {beatsAfter - beats}"

open Solidity.Automation.H28

def callerContext : Lean.Core.Context := {
  fileName := "H28 actual caller witness"
  fileMap := Lean.FileMap.ofString ""
  options := (({} : Lean.Options).setBool `compiler.extract_closed true).setBool `h28.callerFlag true
  maxRecDepth := 17
  maxHeartbeats := 23
  initHeartbeats := 42
  diag := true
}

theorem ambientContextReflexive (context : Lean.Core.Context) : context = context := rfl

theorem contextInhabited : Nonempty Lean.Core.Context := ⟨callerContext⟩

theorem actualCallerFields :
    (codegenContext callerContext).maxRecDepth = 17 ∧
    (codegenContext callerContext).maxHeartbeats = 23 ∧
    (codegenContext callerContext).initHeartbeats = 42 ∧
    (codegenContext callerContext).diag = true ∧
    (codegenContext callerContext).options.getBool `compiler.extract_closed true = false ∧
    (codegenContext callerContext).options.getBool `h28.callerFlag false = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem extractionActuallyChanges : codegenContext callerContext ≠ callerContext := by
  intro equal
  have flag :
      (codegenContext callerContext).options.getBool `compiler.extract_closed true =
        callerContext.options.getBool `compiler.extract_closed true := congrArg (fun context : Lean.Core.Context =>
    context.options.getBool `compiler.extract_closed true) equal
  change false = true at flag
  cases flag

#h28_audit Solidity.Automation.H28.codegenContext_restore_options
#h28_audit Solidity.Automation.H28.codegenContext_limits
#h28_audit ambientContextReflexive
#h28_audit contextInhabited
#h28_audit actualCallerFields
#h28_audit extractionActuallyChanges

#print axioms Solidity.Automation.H28.codegenContext_restore_options
#print axioms Solidity.Automation.H28.codegenContext_limits
#print axioms ambientContextReflexive
#print axioms contextInhabited
#print axioms actualCallerFields
#print axioms extractionActuallyChanges
