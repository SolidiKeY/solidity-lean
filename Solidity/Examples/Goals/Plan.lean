import Solidity.Goals.Plan

namespace Solidity.Goals

/--
info: unstated Solidity.Goals.trustedSurfaceClosed ← Solidity.Main.trusted_surface_closed plan va1-trust-surface
-/
#guard_msgs in
#roadmap_goal trustedSurfaceClosed

/--
info: unstated Solidity.Goals.differentialAgreement ← Solidity.Validation.differential_agreement plan va3-semantic-validation
-/
#guard_msgs in
#roadmap_goal differentialAgreement

/--
info: unstated Solidity.Goals.benchmarkBudgetsMet ← Solidity.Bench.budgets_met plan vu1-benchmarks
-/
#guard_msgs in
#roadmap_goal benchmarkBudgetsMet

/--
info: unstated Solidity.Goals.fastModeAgrees ← Solidity.Automation.fast_mode_agrees plan vu2-fast-mode
-/
#guard_msgs in
#roadmap_goal fastModeAgrees

/--
info: unstated Solidity.Goals.certificateCheckSound ← Solidity.Automation.Certificate.check_sound plan vu3-certificates
-/
#guard_msgs in
#roadmap_goal certificateCheckSound

/--
info: unstated Solidity.Goals.callSummarySound ← Solidity.Automation.Summary.call_summary_sound plan vu4-modular
-/
#guard_msgs in
#roadmap_goal callSummarySound

/--
info: unstated Solidity.Goals.genericYulViewsPreserve ← Solidity.Yul.Views.generic_views_preserve plan t1-yul-views-generic
-/
#guard_msgs in
#roadmap_goal genericYulViewsPreserve

/--
info: unstated Solidity.Goals.controlsOffCriticalPath ← Solidity.Controls.off_critical_path plan t2-controls-off-path
-/
#guard_msgs in
#roadmap_goal controlsOffCriticalPath

/--
info: unstated Solidity.Goals.dedupStatementsPreserved ← Solidity.Dedup.statements_preserved plan t3-dedup-rollout
-/
#guard_msgs in
#roadmap_goal dedupStatementsPreserved

/--
info: unstated Solidity.Goals.docLintClean ← Solidity.Docs.lint_clean plan g2-doc-lint
-/
#guard_msgs in
#roadmap_goal docLintClean

/--
info: unstated Solidity.Goals.docHistoryPurged ← Solidity.Docs.history_purged plan g3-history-purge-docs
-/
#guard_msgs in
#roadmap_goal docHistoryPurged

/--
info: unstated Solidity.Goals.commentsAsCode ← Solidity.Docs.comments_as_code plan g4-comments-to-code
-/
#guard_msgs in
#roadmap_goal commentsAsCode

/--
info: open Solidity.Goals.opcodeEvalUniversal ← Solidity.Yul.opcode_eval_universal plan v1-yul-checks-universal
-/
#guard_msgs in
#roadmap_goal opcodeEvalUniversal

end Solidity.Goals
