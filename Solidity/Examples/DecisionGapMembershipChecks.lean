import Solidity.Examples.Decision
import Solidity.Examples.DecisionGapBinderChecks

/-! Checks ledger verdicts and coverage, and re-exports the fragment-membership regressions. -/

namespace Solidity.Examples.Decision

open Solidity.Decide

set_option Elab.async false

/-! A ledger read past a payment (M7, feature 25): the former counterexample
`gapLedgerWrite` refuted, its true variant proved, the balance a payment
leaves read; the coverage kernel-checked. -/

/-- info: ["refuted", "proved", "proved", "refuted"] -/
#guard_msgs in
#eval [gapLedgerWrite, ledgerWriteOk, payBalanceOk, payBalanceBad].map verdict

theorem gapLedgerWrite_covered : gapLedgerWrite.Covered = true := by decide +kernel
theorem ledgerWriteOk_covered : ledgerWriteOk.Covered = true := by decide +kernel
theorem payBalanceOk_covered : payBalanceOk.Covered = true := by decide +kernel

/-- `decideGoal_complete`, applied: no hash, so no premise. -/
theorem gapLedgerWrite_answers : decideGoal gapLedgerWrite ≠ .unknown :=
  decideGoal_complete gapLedgerWrite_covered rfl

/-- `decideLeaf_proved_iff`, applied: the verdict on the true variant is exact. -/
theorem ledgerWriteOk_iff : decideLeaf ledgerWriteOk = .proved ↔ Fml.Valid ledgerWriteOk :=
  decideLeaf_proved_iff ledgerWriteOk_covered

end Solidity.Examples.Decision
