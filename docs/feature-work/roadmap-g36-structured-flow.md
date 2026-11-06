# G36.01 structured-flow target selectors

Target-side branch and exit selectors over the existing EVM instruction
semantics (`Backend/StructuredFlow/`), from the v17-validation-release lane.
No new AST or source evaluator.

- `BranchSelector.lean`: `emit` and its runs: `false_run`, `true_run`,
  `true_success`, `true_revert`, `true_fault`, `true_pending_skip` (a pending
  skip is not a return), `condition_revert`, `condition_fault`. The
  post-condition machine is explicit, since a condition prefix may have effects.
- `ExitSelector.lean`: relative-exit composition (`run_skip`, `skips`,
  `branch_left`); the caller supplies the exact skipped code.
- `CoreScopes.lean`, `CoreSequence.lean`: thin adapters over the core compiler's
  `ite_sim`/`block_sim`/`stmt_sim`/`prog_sim` for intrinsic `Prog`/`Stmt`
  inputs (`branch_code` reduces to `compileStmt (.ite …)`; `block_code` is
  `rfl`).
- `BranchControls.lean`, `ExitControls.lean`, `CoreScopeControls.lean`,
  `CoreSequenceControls.lean`: concrete machines (hand-built, no `StateRepr` in
  the branch controls), an off-by-one exit refusal, a branch-updated local read
  by its continuation.

Open: source outcome, label and frame correspondence; the G24 compilation and
representation facts at the post-condition machine; mixed memory/backend
composition. The lane's `Source/Lowering/` control-lowering modules (G19) are
not merged: they form a second lowering layer beside `Lowering/V07/`.
