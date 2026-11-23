import Solidity.Examples.ExecutableGoalBinding

/-! Test-only kernel replay: the same retained proof must check at its exact
formula and fail with a declaration-type mismatch at the true formula.
The ordinary proof examples are built first; CI runs this module serially.
-/
open Lean Elab Command Meta Solidity Solidity.Tools
namespace ExecutableBindingControls

run_cmd do
  let some (.thmInfo certificate) := (← getEnv).find? ``exactTarget
    | throwError "missing exact-target control"
  let options ← getOptions
  if options.getBool `debug.skipKernelTC false then
    throwError "kernel checking must be enabled"
  let target ← liftTermElabM <| mkAppM ``Fml.Valid #[mkApp (mkConst ``GoalPair.executableFormula)
    (mkConst ``truePair)]
  let declaration := Declaration.thmDecl {
    name := `ExecutableBindingControls.wrongTargetCertificate
    levelParams := [], type := mkNot target, value := certificate.value }
  let limit := maxHeartbeats.get options
  let options := maxHeartbeats.set options (if limit == 0 then 100000 else min limit 100000)
  let environment := (← getEnv)
  let positiveName := `ExecutableBindingControls.correctTargetCertificate
  unless !(environment.contains positiveName) &&
      !(environment.contains `ExecutableBindingControls.wrongTargetCertificate) do
    throwError "kernel-control declaration name already present"
  let positive := Declaration.thmDecl {
    name := positiveName, levelParams := [],
    type := certificate.type, value := certificate.value }
  match Kernel.Environment.addDecl environment.toKernelEnv options positive with
  | .error _ => throwError "correct-target replay failed under identical kernel ceiling"
  | .ok checked =>
    match Kernel.Environment.addDecl checked options declaration with
    | .ok _ => throwError "wrong-target certificate accepted"
    | .error (.declTypeMismatch ..) =>
      logInfo "EXECUTABLE_BINDING correct-target replay and wrong-target declaration-type mismatch confirmed"
    | .error _ => throwError "wrong-target refusal was not a declaration-type mismatch"


end ExecutableBindingControls
