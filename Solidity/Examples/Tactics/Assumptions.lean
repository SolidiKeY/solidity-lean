import Solidity.Calculus.Assumptions
import Solidity.Examples.Tactics.TailMode
import Solidity.Examples.Tactics.Callback

/-!
# Assumption records and policies (`docs/options.md`, O10, O13)

Witnesses and negative controls for `Calculus/Assumptions.lean`, over the
option examples already proved: `pushRead` (O6,
`Examples/Tactics/TailMode.lean`) holds under clean tails and is refuted
under `.solc`; `withdrawUnsafe` (O1, `Examples/Tactics/Callback.lean`)
holds without payment callbacks and is refuted with them.  A policy that
denies the reading a row holds under reports it `refused`; the decision
table at the end is the one `scripts/solidity-lean.test.mjs` pins for the
CLI's `--require`/`--deny`.
-/

namespace Solidity.Examples.Tactics.Assumptions

open Solidity
open Solidity.Examples.Tactics.TailMode (pushRead pushRead_clean pushRead_solc_refuted)
open Solidity.Examples.Tactics.Callback (Vault vaultInv withdrawUnsafe withdrawUnsafe_noCallback
  withdrawUnsafe_withCallback)

/-! ## Clean tails -/

/-- `tokens.push(); assert(tokens[tokens.length - 1].value == 0);` holds
under the record with clean tails. -/
theorem pushRead_validA_clean : ValidA .top { tail := .clean } pushRead :=
  validA_of_validTail .top .clean pushRead rfl rfl pushRead_clean

/-- Negative control: not under the runner's default record (`.solc`). -/
theorem pushRead_not_validA_solc : ¬ ValidA .top {} pushRead := fun h =>
  pushRead_solc_refuted ((validC_false_iff rfl).1 h.2)

/-- So a policy denying clean tails refuses it. -/
theorem pushRead_refused :
    ({ deny := [.tail .clean] } : Policy).verdict { tail := .clean } true = .refused := by decide

theorem pushRead_never_proved :
    ({ deny := [.tail .clean] } : Policy).verdict { tail := .clean } true ≠ .proved :=
  Policy.verdict_refused _ _ _ (by decide)

/-- A `.solc` row stays proved when `.solc` itself is denied: it holds under
clean tails too (`ValidA.weaken`). -/
theorem solc_row_admitted_under_clean :
    ({ deny := [.tail .solc] } : Policy).admits {} = true := by decide

/-! ## Callbacks -/

/-- `uint amt = balance; to.transfer(amt); balance = 0; paidOut += amt;`
keeps the vault's invariant when a `transfer` does not call back. -/
theorem withdrawUnsafe_validA : ValidA .top {} withdrawUnsafe :=
  (validA_iff_validT (.noCallback) withdrawUnsafe rfl).2 withdrawUnsafe_noCallback

/-- Negative control: not when it calls back keeping the invariant. -/
theorem withdrawUnsafe_not_validA_callback : ¬ ValidA vaultInv { callback := true } withdrawUnsafe :=
  fun h => withdrawUnsafe_withCallback
    ((validA_iff_validT (.withCallback vaultInv) withdrawUnsafe rfl).1 h)

/-- A row proved without callbacks is refused where callbacks are required. -/
theorem withdrawUnsafe_refused :
    ({ require := [.callback true] } : Policy).verdict {} true = .refused := by decide

/-! ## Order and profile -/

/-- Negative control: a legacy contract is not read under the via-IR
order, whatever the formula. -/
theorem not_validA_viaIR : ¬ ValidA (C := Vault) .top { order := .viaIR } withdrawUnsafe :=
  fun h => Bool.false_ne_true h.1

/-- The pinned profile fits the runner's record, not a via-IR one. -/
example : TargetProfile.pinned.fits {} = true := by decide
example : TargetProfile.pinned.fits { order := .viaIR } = false := by decide
example : ({ solc := ⟨0, 8, 38⟩, pipeline := .viaIR } : TargetProfile).fits { order := .viaIR } = true := by
  decide

/-- The pinned profile's pipeline is the vault's order. -/
theorem withdrawUnsafe_pinned : Vault.evalOrder = TargetProfile.pinned.pipeline.order.toEvalOrder :=
  TargetProfile.evalOrder_of_fits (by decide) withdrawUnsafe_validA

/-- A proved row as the report states it, under a policy denying via-IR. -/
def withdrawUnsafe_row : ProvedRow .top { deny := [.order .viaIR] } withdrawUnsafe :=
  ⟨{}, withdrawUnsafe_validA, by decide⟩

/-! ## The CLI's decision table

`[require, deny, row tails, verdict]`, as `POLICY_TABLE` in
`scripts/solidity-lean.test.mjs`; every other reading is the runner's. -/

/-- The table. -/
def table : List (List Atom × List Atom × TailMode × Verdict) := [
  ([], [], .solc, .proved),
  ([], [.tail .clean], .clean, .refused),
  ([], [.tail .clean], .solc, .proved),
  ([], [.tail .solc], .solc, .proved),
  ([], [.tail .solc], .clean, .proved),
  ([.tail .solc], [], .clean, .refused),
  ([.tail .clean], [.tail .solc], .solc, .proved),
  ([.callback true], [], .solc, .refused),
  ([.callback false], [.overflow .ignoring], .clean, .proved),
  ([], [.zeroAddress .noCode], .solc, .refused),
  ([], [.hash .opaque], .clean, .refused),
  ([.order .viaIR], [], .solc, .refused),
  ([.order .legacy], [.callback true, .overflow .checked], .solc, .proved)]

theorem table_verdicts : table.all (fun (r, d, t, v) =>
    ({ require := r, deny := d } : Policy).verdict { tail := t } true == v) = true := by decide

/-- Negative control: no row that is not proved is reported proved. -/
theorem table_notProved : table.all (fun (r, d, t, _) =>
    ({ require := r, deny := d } : Policy).verdict { tail := t } false == .notProved) = true := by
  decide

end Solidity.Examples.Tactics.Assumptions
