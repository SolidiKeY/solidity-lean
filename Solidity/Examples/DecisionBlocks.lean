import Solidity.Examples.DecisionAPF

namespace Solidity.Examples.Decision

open Solidity.Decide

set_option Elab.async false

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


end Solidity.Examples.Decision
