import Solidity.Examples.Decision
import Solidity.Examples.DecisionGapBinderChecks

/-! Checks ledger verdicts and coverage, and re-exports the fragment-membership regressions. -/

namespace Solidity.Examples.Decision

open Solidity.Decide

set_option Elab.async false

/-! A ledger read past a payment (M7, feature 25): the former counterexample
`gapLedgerWrite` refuted, its true variant proved, the balance a payment
leaves read; the coverage kernel-checked. -/

/-- info: ["proved", "refuted"] -/
#guard_msgs in #eval [payBalanceOk, payBalanceBad].map verdict

-- The refuting state: the payee `0`, its entry `0`, the contract at `1`.
/-- info: "[(0, 0), (0, 0), (0, 0), (0, 0)] self 1" -/
#guard_msgs in
#eval match decideGoal gapLedgerWrite with
  | .refuted σ => toString (σ.net.map fun (e : PrimTy.uint.Denote × Int) => (e.1.1, e.2)) ++
      " self " ++ toString σ.tx.selfAddress.1
  | _ => "-"

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
