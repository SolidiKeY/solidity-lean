import Solidity.Goals

/--
info: proved Solidity.Goals.tacletsPartitioned ← Solidity.RuleShapes.taclets_partitioned
proved Solidity.Goals.compilerCorrectNoPaymentRevert ← Solidity.Main.compiler_correct_v2
mismatch Solidity.Goals.headlineIsNoPaymentRevert ← Solidity.Main.compiler_correct plan va2-honest-theorems
unstated Solidity.Goals.lowerLoopsCorrect ← Solidity.Correctness.Lowering.lowerLoops_correct plan e1-lowering
unstated Solidity.Goals.compilerCorrectCollisionFree ← Solidity.Hash.compiler_correct_collisionFree plan e4-hash-bridge
unstated Solidity.Goals.runCarriesPanicCodes ← Solidity.Semantics.run_panic_codes plan w3-panic-codes
open Solidity.Goals.loweringStudyTarget ← Solidity.Correctness.Lowering.lowerLoops_correct plan pa-lowering
unstated Solidity.Goals.trustedSurfaceClosed ← Solidity.Main.trusted_surface_closed plan va1-trust-surface
unstated Solidity.Goals.differentialAgreement ← Solidity.Validation.differential_agreement plan va3-semantic-validation
unstated Solidity.Goals.benchmarkBudgetsMet ← Solidity.Bench.budgets_met plan vu1-benchmarks
unstated Solidity.Goals.fastModeAgrees ← Solidity.Automation.fast_mode_agrees plan vu2-fast-mode
unstated Solidity.Goals.certificateCheckSound ← Solidity.Automation.Certificate.check_sound plan vu3-certificates
unstated Solidity.Goals.callSummarySound ← Solidity.Automation.Summary.call_summary_sound plan vu4-modular
unstated Solidity.Goals.genericYulViewsPreserve ← Solidity.Yul.Views.generic_views_preserve plan t1-yul-views-generic
unstated Solidity.Goals.controlsOffCriticalPath ← Solidity.Controls.off_critical_path plan t2-controls-off-path
unstated Solidity.Goals.dedupStatementsPreserved ← Solidity.Dedup.statements_preserved plan t3-dedup-rollout
unstated Solidity.Goals.docLintClean ← Solidity.Docs.lint_clean plan g2-doc-lint
unstated Solidity.Goals.docHistoryPurged ← Solidity.Docs.history_purged plan g3-history-purge-docs
unstated Solidity.Goals.commentsAsCode ← Solidity.Docs.comments_as_code plan g4-comments-to-code
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
