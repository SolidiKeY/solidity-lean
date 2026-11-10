import Solidity.Tools.Goal
import Solidity.Backend.Payments.Headlines
import Solidity.Calculus.RuleShapes

namespace Solidity.Goals

open Semantics Solidity.Goal

open RuleShapes in
@[goal Solidity.RuleShapes.taclets_partitioned]
def tacletsPartitioned : Prop :=
  KeyTaclet.all.all (fun t =>
    (if claims t then (1 : Nat) else 0) +
    (if unclaimedTaclets.contains t then 1 else 0) +
    (if migrationPendingTaclets.contains t then 1 else 0) == 1) = true

open Main Evm Evm in
@[goal Solidity.Main.compiler_correct_v2]
def compilerCorrectNoPaymentRevert : Prop :=
  ∀ {C Γ Γ'} {P : Prog C Γ Γ'} {F : Frag Γ} {F' : Frag Γ'} {σ : State C Γ} {mc : Machine} {L b : Nat},
    F ⊩ P ⊣ F' → σ ≈[C, L, b, F] mc → L + Prog.pushes P ≤ Lmax →
    (∃ o mc', (P, σ) ⇓ o ∧ (⟦P⟧b, mc) ⇓ₘ mc' ∧ o.st ≈[C, L + Prog.pushes P, b, F'] mc') ∨
      ((Prog.run σ P = .error .revert ∨
          (Prog.asserts P = true ∧ Prog.run σ P = .error .panic)) ∧ (⟦P⟧b, mc) ↯ₘ) ∨
      (Prog.run σ P = .error .diverge ∧ run (⟦P⟧b) mc = .fault)

@[goal Solidity.Main.compiler_correct "va2-honest-theorems" ← compilerCorrectNoPaymentRevert]
def headlineIsNoPaymentRevert : Prop := compilerCorrectNoPaymentRevert

@[goal Solidity.Correctness.Lowering.lowerLoops_correct "e1-lowering"]
def lowerLoopsCorrect : Prop := Unstated

@[goal Solidity.Hash.compiler_correct_collisionFree "e4-hash-bridge"]
def compilerCorrectCollisionFree : Prop := Unstated

@[goal Solidity.Semantics.run_panic_codes "w3-panic-codes"]
def runCarriesPanicCodes : Prop := Unstated

-- Remaining plan steps: each goal names the theorem expected to close it; pa-lowering
-- reuses the e1 statement, the others await vocabulary.

@[goal Solidity.Correctness.Lowering.lowerLoops_correct "pa-lowering" ← lowerLoopsCorrect]
def loweringStudyTarget : Prop := lowerLoopsCorrect

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
