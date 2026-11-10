import Solidity.Examples.Decision

/-! Checks integer-binder verdicts, refuting states, coverage, and exact-answer regressions. -/

namespace Solidity.Examples.Decision

open Solidity.Decide

set_option Elab.async false

/-! Binders of KeY's `int` (M7, feature 26): the former counterexample
`gapKIntBinder` proved, its false variant refuted (the binder's entry `0`),
two binders proved; the coverage kernel-checked. -/

/-- info: ["proved", "refuted", "proved"] -/
#guard_msgs in
#eval [gapKIntBinder, kintBinderBad, kintBinderTwo].map verdict

-- The refuting state: the binder's address `0`, its entry `0`.
/-- info: "[(0, 0)]" -/
#guard_msgs in
#eval match decideGoal kintBinderBad with
  | .refuted σ => toString (σ.net.map fun (e : PrimTy.uint.Denote × Int) => (e.1.1, e.2))
  | _ => "-"

theorem gapKIntBinder_covered : gapKIntBinder.Covered = true := by decide +kernel
theorem kintBinderBad_covered : kintBinderBad.Covered = true := by decide +kernel

/-- `decideGoal_complete`, applied: no hash, so no premise. -/
theorem gapKIntBinder_answers : decideGoal gapKIntBinder ≠ .unknown :=
  decideGoal_complete gapKIntBinder_covered rfl

/-- `decideLeaf_proved_iff`, applied: the verdict is exact. -/
theorem gapKIntBinder_iff : decideLeaf gapKIntBinder = .proved ↔ Fml.Valid gapKIntBinder :=
  decideLeaf_proved_iff gapKIntBinder_covered

-- The refuting state: the payee `0`, its entry `0`, the contract at `1`.
/-- info: "[(0, 0), (0, 0), (0, 0), (0, 0)] self 1" -/
#guard_msgs in
#eval match decideGoal gapLedgerWrite with
  | .refuted σ => toString (σ.net.map fun (e : PrimTy.uint.Denote × Int) => (e.1.1, e.2)) ++
      " self " ++ toString σ.tx.selfAddress.1
  | _ => "-"

end Solidity.Examples.Decision
