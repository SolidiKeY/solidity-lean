import Solidity.Goals.Plan

namespace Solidity.Goals

/--
info: unstated Solidity.Goals.trustedSurfaceClosed ← Solidity.Main.trusted_surface_closed plan va1-trust-surface
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
#roadmap_goal trustedSurfaceClosed differentialAgreement benchmarkBudgetsMet fastModeAgrees certificateCheckSound callSummarySound genericYulViewsPreserve controlsOffCriticalPath dedupStatementsPreserved docLintClean docHistoryPurged commentsAsCode

end Solidity.Goals
