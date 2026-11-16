import Solidity.Examples.Decision
import Solidity.Examples.DecisionGapBinderChecks

/-! Checks the positive ledger verdict and re-exports the preserved membership/coverage facts. -/

namespace Solidity.Examples.Decision

open Solidity.Decide

set_option Elab.async false

/-! A ledger read past a payment (M7, feature 25): the former counterexample
`gapLedgerWrite` refuted, its true variant proved, the balance a payment
leaves read; the coverage kernel-checked. -/

/-- info: "proved" -/
#guard_msgs in #eval verdict ledgerWriteOk

end Solidity.Examples.Decision
