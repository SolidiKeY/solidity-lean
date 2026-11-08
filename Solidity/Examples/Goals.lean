import Solidity.Goals

/--
info: proved Solidity.Goals.tacletsPartitioned ← Solidity.RuleShapes.taclets_partitioned
proved Solidity.Goals.compilerCorrectNoPaymentRevert ← Solidity.Main.compiler_correct_v2
mismatch Solidity.Goals.headlineIsNoPaymentRevert ← Solidity.Main.compiler_correct plan va2-honest-theorems
unstated Solidity.Goals.lowerLoopsCorrect ← Solidity.Correctness.Lowering.lowerLoops_correct plan e1-lowering
unstated Solidity.Goals.compilerCorrectCollisionFree ← Solidity.Hash.compiler_correct_collisionFree plan e4-hash-bridge
unstated Solidity.Goals.runCarriesPanicCodes ← Solidity.Semantics.run_panic_codes plan w3-panic-codes
-/
#guard_msgs in
#roadmap

-- Classifier fixtures live only in a temporary environment: none is exported.
open Lean Elab Command Meta in
#guard_msgs in
run_cmd liftTermElabM do
  let assumption := `Solidity.Goals.Regression.assumption
  let goalName := `Solidity.Goals.Regression.goal
  let transitive := `Solidity.Goals.Regression.transitive
  let native := `Solidity.Goals.Regression.native
  let trueGoal := `Solidity.Goals.Regression.trueGoal
  let logical := `Solidity.Goals.Regression.logical
  let logicalGoal := `Solidity.Goals.Regression.logicalGoal
  withoutModifyingEnv do
    addDecl (.axiomDecl {
      name := assumption, levelParams := [], type := mkConst ``False, isUnsafe := false })
    addDecl (.defnDecl {
      name := goalName, levelParams := [], type := mkSort .zero,
      value := mkConst ``False, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl {
      name := transitive, levelParams := [], type := mkConst ``False,
      value := mkConst assumption })
    addDecl (.defnDecl {
      name := trueGoal, levelParams := [], type := mkSort .zero,
      value := mkConst ``True, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl {
      name := native, levelParams := [], type := mkConst ``True,
      value := mkConst ``Lean.trustCompiler })
    let logicalType := (← getConstInfo ``propext).type
    addDecl (.defnDecl {
      name := logicalGoal, levelParams := [], type := mkSort .zero,
      value := logicalType, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl {
      name := logical, levelParams := [], type := logicalType, value := mkConst ``propext })
    let direct : Solidity.Goal.Entry := { decl := goalName, proof := assumption, deps := #[], plan := none }
    let directStatus ← Solidity.Goal.status direct
    unless directStatus == .assumed do throwError "direct assumption reported as completed"
    unless (← Solidity.Goal.status { direct with proof := transitive }) == .assumed do
      throwError "transitive assumption reported as completed"
    unless (← Solidity.Goal.status { direct with decl := trueGoal, proof := native }) == .assumed do
      throwError "native evaluation trust reported as completed"
    unless (← Solidity.Goal.status { direct with decl := trueGoal, proof := ``True.intro }) == .proved do
      throwError "closed proof rejected"
    unless (← Solidity.Goal.status { direct with decl := logicalGoal, proof := logical }) == .proved do
      throwError "standard logical foundation rejected"
    unless (← Solidity.Goal.status { direct with decl := logicalGoal, proof := ``propext }) == .assumed do
      throwError "direct logical assumption reported as completed"
    let dependent : Solidity.Goal.Entry := {
      decl := `Solidity.Goals.Regression.dependent, proof := `Solidity.Goals.Regression.missing,
      deps := #[goalName], plan := none }
    let expected := s!"assumed {goalName} ← {assumption}\nopen {dependent.decl} ← {dependent.proof} blocked by [{goalName}]"
    unless Solidity.Goal.report #[(direct, directStatus), (dependent, .open)] == expected do
      throwError "assumed dependency did not remain blocked"
  for name in [assumption, goalName, transitive, native, trueGoal, logical, logicalGoal] do
    if (← getEnv).contains name then throwError "classifier fixture escaped its temporary environment"
