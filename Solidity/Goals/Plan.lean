import Solidity.Tools.Goal

/-! Plan steps outside the finish line: each goal names the theorem expected to close
it; all await vocabulary. -/

namespace Solidity.Goals

open Solidity.Goal

@[goal Solidity.Main.trusted_surface_closed "va1-trust-surface"]
def trustedSurfaceClosed : Prop := Unstated

@[goal Solidity.Validation.differential_agreement "va3-semantic-validation"]
def differentialAgreement : Prop := Unstated

@[goal Solidity.Bench.budgets_met "vu1-benchmarks"]
def benchmarkBudgetsMet : Prop := Unstated

@[goal Solidity.Automation.fast_mode_agrees "vu2-fast-mode"]
def fastModeAgrees : Prop := Unstated

@[goal Solidity.Automation.Certificate.check_sound "vu3-certificates"]
def certificateCheckSound : Prop := Unstated

@[goal Solidity.Automation.Summary.call_summary_sound "vu4-modular"]
def callSummarySound : Prop := Unstated

@[goal Solidity.Yul.Views.generic_views_preserve "t1-yul-views-generic"]
def genericYulViewsPreserve : Prop := Unstated

@[goal Solidity.Controls.off_critical_path "t2-controls-off-path"]
def controlsOffCriticalPath : Prop := Unstated

@[goal Solidity.Dedup.statements_preserved "t3-dedup-rollout"]
def dedupStatementsPreserved : Prop := Unstated

@[goal Solidity.Docs.lint_clean "g2-doc-lint"]
def docLintClean : Prop := Unstated

@[goal Solidity.Docs.history_purged "g3-history-purge-docs"]
def docHistoryPurged : Prop := Unstated

@[goal Solidity.Docs.comments_as_code "g4-comments-to-code"]
def commentsAsCode : Prop := Unstated

end Solidity.Goals
