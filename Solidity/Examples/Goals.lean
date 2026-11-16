import Solidity.Goals

/-! The whole roadmap, unpinned: each goal module pins its own lines in
`Solidity/Examples/Goals/<Name>.lean`, one `#guard_msgs` block per goal, so a lane
flipping its goal edits only its own block. -/

#roadmap

-- `@[goal … ← deps]` registers its dependencies: an unproved one prints `blocked by`.
-- The fixtures live only in a temporary environment: none is exported.
open Lean Elab Command in
/--
info: unstated Solidity.Goals.DepsRegression.base ← Solidity.Goals.DepsRegression.base_proof
open Solidity.Goals.DepsRegression.top ← Solidity.Goals.DepsRegression.top_proof blocked by [Solidity.Goals.DepsRegression.base, Solidity.Goals.DepsRegression.other] plan dep-test
-/
#guard_msgs in
run_cmd withoutModifyingEnv do
  for src in [
      "@[goal Solidity.Goals.DepsRegression.base_proof] def Solidity.Goals.DepsRegression.base : Prop := Solidity.Goal.Unstated",
      "@[goal Solidity.Goals.DepsRegression.other_proof] def Solidity.Goals.DepsRegression.other : Prop := True",
      "@[goal Solidity.Goals.DepsRegression.top_proof \"dep-test\" ← Solidity.Goals.DepsRegression.base Solidity.Goals.DepsRegression.other] def Solidity.Goals.DepsRegression.top : Prop := True"] do
    elabCommand (← ofExcept <| Parser.runParserCategory (← getEnv) `command src)
  let es := Solidity.Goal.goalExt.getState (← getEnv)
  let some top := es.find? (·.decl == `Solidity.Goals.DepsRegression.top)
    | throwError "dependent fixture not registered"
  unless top.deps == #[`Solidity.Goals.DepsRegression.base, `Solidity.Goals.DepsRegression.other] do
    throwError "dependencies lost: {top.deps}"
  elabCommand (← ofExcept <| Parser.runParserCategory (← getEnv) `command
    "#roadmap_goal Solidity.Goals.DepsRegression.base Solidity.Goals.DepsRegression.top")

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
