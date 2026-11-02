import Solidity.Examples.Decision

/-!
# The closer's decision (M7): the former counterexamples over `Gaps`

Fragment membership of the `DecisionTheorem` counterexamples, KeY `int`
binders, a ledger read past a payment, array property blocks past their
last key, `int` and ledger blocks, the astronomically large refutations
and fifty reads. Split from `Examples/Decision.lean`, which defines the formulas, so
that each piece builds well under 300 s.
-/

namespace Solidity.Examples.Decision

open Solidity.Decide

-- The verdicts run one after another: run in parallel, their evaluations
-- together overflow a command-line `lean`'s stack (exit 135).
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

/-! A ledger read past a payment (M7, feature 25): the former counterexample
`gapLedgerWrite` refuted, its true variant proved, the balance a payment
leaves read; the coverage kernel-checked. -/

/-- info: ["refuted", "proved", "proved", "refuted"] -/
#guard_msgs in
#eval [gapLedgerWrite, ledgerWriteOk, payBalanceOk, payBalanceBad].map verdict

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

/-! Array property blocks past their last key and at two depths, over a
`bool` key, past a member, with a guard that may halt, and a positive `∀`
past the prefix (M7, features 16 to 19, 2026-10-26): each former
counterexample proved, a false variant refuted, the coverage
kernel-checked. -/

/-- info: ["proved", "proved", "proved", "proved", "proved", "proved"] -/
#guard_msgs in
#eval [gapColumn, gapTwoPaths, gapBoolKeyed, gapStructValue, gapPartialGuard, gapPositiveForall].map verdict

/-- info: ["refuted", "refuted", "refuted", "refuted", "refuted", "refuted"] -/
#guard_msgs in
#eval [columnBad, twoPathsBad, boolKeyedBad, structValueBad, partialGuardBad, positiveForallBad].map verdict

theorem gapColumn_covered : gapColumn.Covered = true := by decide +kernel
theorem gapTwoPaths_covered : gapTwoPaths.Covered = true := by decide +kernel
theorem gapBoolKeyed_covered : gapBoolKeyed.Covered = true := by decide +kernel
theorem gapStructValue_covered : gapStructValue.Covered = true := by decide +kernel
theorem gapPartialGuard_covered : gapPartialGuard.Covered = true := by decide +kernel
theorem gapPositiveForall_covered : gapPositiveForall.Covered = true := by decide +kernel
theorem columnBad_covered : columnBad.Covered = true := by decide +kernel

theorem gapColumn_answers : decideGoal gapColumn ≠ .unknown := decideGoal_complete gapColumn_covered rfl

/-! Blocks over `int` keys and over the ledger (M7, features 20 and 21,
2026-10-26): each former counterexample proved, a false variant refuted,
the coverage kernel-checked.  An `int` block's index set has the type's
least value `-2^255` as its base and its largest value too; the ledger's
blocks are instantiated by the ledger pipeline's preparation stage
(`ledgerBlockReduction?`).  A refutation rebuilds `ibal` (the ledger) region
by region (`regionList`), a region holding the default (`0`) left out:
`intKeyedBad`'s `ibal` lists one entry; `ledgerBlockBad`'s ledger, the
largest address in the index set too, lists the addresses up to `5` whose
floors' entries are not `0`, the addresses past `5` reading the free entry
at the largest one. -/

/-- info: ["proved", "proved"] -/
#guard_msgs in #eval [gapIntKeyed, gapLedgerBlock].map verdict

/-- info: ["refuted", "refuted"] -/
#guard_msgs in #eval [intKeyedBad, ledgerBlockBad].map verdict

/-- The entries of `ibal` in a state. -/
def ibalEntries (σ : State Gaps []) : List (Int × Int) :=
  match σ.storage.get (f := "ibal") (T := .ref (.mapping .int (.prim .uint))) rfl with
  | .map m _ => m.toList.map fun e => (e.1.1, match e.2 with | .prim v => v.1)

/-- info: some [(0, 1)] -/
#guard_msgs in #eval match decideGoal intKeyedBad with | .refuted σ => some (ibalEntries σ) | _ => none

/-- info: some [(0, 127), (4, 127), (1, 127), (2, 127), (3, 127), (5, -21)] -/
#guard_msgs in
#eval match decideGoal ledgerBlockBad with
  | .refuted σ => some (σ.net.map fun (e : PrimTy.uint.Denote × Int) => (e.1.1, e.2)) | _ => none

theorem gapIntKeyed_covered : gapIntKeyed.Covered = true := by decide +kernel
theorem gapLedgerBlock_covered : gapLedgerBlock.Covered = true := by decide +kernel
theorem intKeyedBad_covered : intKeyedBad.Covered = true := by decide +kernel
theorem ledgerBlockBad_covered : ledgerBlockBad.Covered = true := by decide +kernel

theorem gapIntKeyed_answers : decideGoal gapIntKeyed ≠ .unknown := decideGoal_complete gapIntKeyed_covered rfl
theorem gapLedgerBlock_iff : decideLeaf gapLedgerBlock = .proved ↔ Fml.Valid gapLedgerBlock :=
  decideLeaf_proved_iff gapLedgerBlock_covered

/-! The astronomically large refutations: both leaves are in the fragment
and covered by the kernel, so they answer (`decideGoal_complete`).  The
instance the decision refutes is refuted by its arithmetic (computed for
`intTwoSides` below, the instance's state small), and the leaf's refuting
state is that state's mappings or ledger
rebuilt at the floors (`ApfFml.apfInst_refute`): a term whose reads are
proved region by region, the negative region of `2^255` keys for
`intTwoSides` (the positive one holds the default, the largest key's `2`),
one of `2^256 - 6` addresses for `ledgerFar`, which no evaluation builds. -/

theorem intTwoSides_inTarget : intTwoSides.inTarget {} = true := by decide +kernel
theorem ledgerFar_inTarget : ledgerFar.inTarget {} = true := by decide +kernel
theorem intTwoSides_covered : intTwoSides.Covered = true := by decide +kernel
theorem ledgerFar_covered : ledgerFar.Covered = true := by decide +kernel

theorem intTwoSides_answers : decideGoal intTwoSides ≠ .unknown := decideGoal_complete intTwoSides_covered rfl
theorem ledgerFar_answers : decideGoal ledgerFar ≠ .unknown := decideGoal_complete ledgerFar_covered rfl

/-- info: "refuted" -/
#guard_msgs in
#eval match quantReduction? intTwoSides with
  | some q => if q.Qs.isEmpty then (match q.main.verify with | .inl _ => "valid" | .inr _ => "refuted")
    else "quantified"
  | none => "none"
theorem gapPartialGuard_iff : decideLeaf gapPartialGuard = .proved ↔ Fml.Valid gapPartialGuard :=
  decideLeaf_proved_iff gapPartialGuard_covered

/-! Fifty reads (M7, 2026-10-25): the flattener's budget is the leaf's own
(`readBudget`), no longer a fixed 45 reads. -/

theorem gapManyReads_covered : gapManyReads.Covered = true := by decide +kernel

/-- It answers (`decideGoal_complete`); the answer is not computed here: the
walk of `AFml.fastVerify` over 51 variables of 256 bits recurses past the
interpreter's stack (docs/automation.md, M7, "Running time"). -/
theorem gapManyReads_answers : decideGoal gapManyReads ≠ .unknown :=
  decideGoal_complete gapManyReads_covered rfl

end Solidity.Examples.Decision
