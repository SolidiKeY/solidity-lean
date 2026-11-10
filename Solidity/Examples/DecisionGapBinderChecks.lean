import Solidity.Examples.Decision

/-! Checks fragment membership, integer binders, and their preserved refuting-state regressions. -/

namespace Solidity.Examples.Decision

open Solidity.Decide

set_option Elab.async false

theorem gapColumn_inTarget : gapColumn.inTarget {} = true := by decide +kernel
theorem gapTwoPaths_inTarget : gapTwoPaths.inTarget {} = true := by decide +kernel
theorem gapIntKeyed_inTarget : gapIntKeyed.inTarget {} = true := by decide +kernel
theorem gapBoolKeyed_inTarget : gapBoolKeyed.inTarget {} = true := by decide +kernel
theorem gapStructValue_inTarget : gapStructValue.inTarget {} = true := by decide +kernel
theorem gapArrayBlock_inTarget : gapArrayBlock.inTarget {} = true := by decide +kernel
theorem gapLedgerBlock_inTarget : gapLedgerBlock.inTarget {} = true := by decide +kernel
theorem gapPartialGuard_inTarget : gapPartialGuard.inTarget {} = true := by decide +kernel
theorem gapPositiveForall_inTarget : gapPositiveForall.inTarget {} = true := by decide +kernel
theorem gapMemory_inTarget : gapMemory.inTarget {} = true := by decide +kernel
theorem gapKIntBinder_inTarget : gapKIntBinder.inTarget {} = true := by decide +kernel
theorem gapKIntNeg_inTarget : gapKIntNeg.inTarget {} = true := by decide +kernel
theorem gapLedgerWrite_inTarget : gapLedgerWrite.inTarget {} = true := by decide +kernel
theorem gapManyReads_inTarget : gapManyReads.inTarget {} = true := by decide +kernel
theorem gapIntDiv_inTarget : gapIntDiv.inTarget {} = true := by decide +kernel
theorem gapIntMod_inTarget : gapIntMod.inTarget {} = true := by decide +kernel
theorem gapOr_inTarget : gapOr.inTarget {} = true := by decide +kernel
theorem gapXor_inTarget : gapXor.inTarget {} = true := by decide +kernel
theorem gapAnd_inTarget : gapAnd.inTarget {} = true := by decide +kernel
theorem gapPow_inTarget : gapPow.inTarget {} = true := by decide +kernel
theorem gapMulW_inTarget : gapMulW.inTarget {} = true := by decide +kernel
theorem gapIntAnd_inTarget : gapIntAnd.inTarget {} = true := by decide +kernel
theorem gapAddmod_inTarget : gapAddmod.inTarget {} = true := by decide +kernel
theorem gapThreeKinds_inTarget : gapThreeKinds.inTarget {} = true := by decide +kernel
theorem gapMixedKinds_inTarget : gapMixedKinds.inTarget {} = true := by decide +kernel
theorem gapMixedPairs_inTarget : gapMixedPairs.inTarget {} = true := by decide +kernel
theorem gapWrittenMemory_inTarget : gapWrittenMemory.inTarget {} = true := by decide +kernel
/-- Outside the fragment (e3″): the negative `∀ x` compares hashes its scope does not read. -/
theorem gapHashNegForall_outside : gapHashNegForall.inTarget {} = false := by decide +kernel

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

/-- info: ["refuted", "proved"] -/
#guard_msgs in #eval [gapLedgerWrite, ledgerWriteOk].map verdict

end Solidity.Examples.Decision
