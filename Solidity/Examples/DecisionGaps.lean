import Solidity.Examples.DecisionGapMembershipChecks
import Solidity.Examples.DecisionGapBinderChecks
import Solidity.Examples.DecisionGapBlockChecks

/-!
# The closer's decision (M7): the former counterexamples over `Gaps`

Fragment membership of the `DecisionTheorem` counterexamples, KeY `int`
binders, a ledger read past a payment, array property blocks past their
last key, `int` and ledger blocks, the astronomically large refutations
and fifty reads. The formulas live in `Examples/Decision.lean`. This proposed split aims to
keep every module within the unchanged 300-second replay budget.
-/

namespace Solidity.Examples.Decision

open Solidity.Decide

-- The verdicts run one after another: run in parallel, their evaluations
-- together overflow a command-line `lean`'s stack (exit 135).
set_option Elab.async false

/-- info: ["proved", "refuted"] -/
#guard_msgs in #eval [payBalanceOk, payBalanceBad].map verdict

-- The refuting state: the payee `0`, its entry `0`, the contract at `1`.
/-- info: "[(0, 0), (0, 0), (0, 0), (0, 0)] self 1" -/
#guard_msgs in
#eval match decideGoal gapLedgerWrite with
  | .refuted σ => toString (σ.net.map fun (e : PrimTy.uint.Denote × Int) => (e.1.1, e.2)) ++
      " self " ++ toString σ.tx.selfAddress.1
  | _ => "-"

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
