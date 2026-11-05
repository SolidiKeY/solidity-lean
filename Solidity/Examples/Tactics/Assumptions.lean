import Solidity.Calculus.TargetProfile
import Solidity.Examples.Tactics.TailMode
import Solidity.Examples.Tactics.Callback

/-!
# Assumption records, policies and profiles (`docs/options.md`, O10, O13)

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
  Policy.verdict_refused _ _ _ fun b hb => by
    rcases hb with rfl | ⟨h, rfl⟩
    · decide
    · exact absurd h (by decide)

/-- A `.solc` row stays proved when `.solc` itself is denied: it holds under
clean tails too (`ValidA.weaken`). -/
theorem solc_row_admitted_under_clean :
    ({ deny := [.tail .solc] } : Policy).admits {} = true := by decide

/-- Control: the policy does not accept the `.solc` record itself, so the
admission is the weakening's (`Assumptions.weakenings`), not `allows`. -/
theorem solc_record_not_allowed :
    ({ deny := [.tail .solc] } : Policy).allows {} = false := by decide

/-- Control: no weakening reaches `.solc` from `.clean`, so requiring `.solc`
refuses a clean row (`table` below, sixth line). -/
theorem clean_row_not_admitted_solc :
    ({ require := [.tail .solc] } : Policy).admits { tail := .clean } = false := by decide

/-! ## Callbacks -/

/-- `uint amt = balance; to.transfer(amt); balance = 0; paidOut += amt;`
keeps the vault's invariant when a `transfer` does not call back. -/
theorem withdrawUnsafe_validA : ValidA .top {} withdrawUnsafe :=
  (validA_iff_validT (.noCallback) withdrawUnsafe rfl).2 withdrawUnsafe_noCallback

/-- The same at the vault's invariant: without payment callbacks the
invariant a callee keeps is not read (`validC_false_iff`). -/
theorem withdrawUnsafe_validA_inv : ValidA vaultInv {} withdrawUnsafe :=
  validA_of_validTail vaultInv .solc withdrawUnsafe rfl rfl
    ((validT_noCallback_iff (I := .top) rfl).1 withdrawUnsafe_noCallback)

/-- Negative control, at the same invariant: not when a payment calls back
keeping it.  Only the flag differs from `withdrawUnsafe_validA_inv`. -/
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

/-- The pinned profile (solc 0.8.34, legacy, VS4's Osaka) fits the
runner's record, not a via-IR one; a via-IR profile fits the via-IR record. -/
example : TargetProfile.pinned.fits {} = true := by decide
example : TargetProfile.pinned.fits { order := .viaIR } = false := by decide
example : ({ solc := ⟨0, 8, 38⟩, pipeline := .viaIR } : TargetProfile).fits { order := .viaIR } = true := by
  decide
example : TargetProfile.pinned.fork.fork = .osaka := rfl

/-- The pinned profile's pipeline is the vault's order. -/
theorem withdrawUnsafe_pinned : Vault.evalOrder = TargetProfile.pinned.pipeline.order :=
  TargetProfile.evalOrder_of_fits (by decide) withdrawUnsafe_validA

/-- Negative control: a via-IR profile does not fit the vault's proof
(its record is legacy), and a contract in the via-IR order has no valid
legacy record (`not_validA_of_not_fits`). -/
theorem viaIR_profile_not_fits :
    ({ solc := ⟨0, 8, 38⟩, pipeline := .viaIR } : TargetProfile).fits {} = false := by decide

theorem legacy_record_not_valid_viaIR {C : Contract} (hC : C.evalOrder = EvalOrder.viaIR)
    (φ : Fml C []) : ¬ ValidA .top {} φ :=
  TargetProfile.not_validA_of_not_fits (p := { solc := ⟨0, 8, 38⟩, pipeline := .viaIR }) (by decide) hC

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

/-! ## The exhaustive table the CLI is checked against

`tests/cli/assumption-policies.txt` holds every record under the empty
policy, each single requirement or denial, and each requirement with a
denial of another reading (3192 cases), as `policyTable` in
`scripts/solidity-lean-assumptions.mjs` computes them; its test checks the
file is that output.  Here each line is checked against `Policy.verdict`:
the CLI's JavaScript verdict is Lean's on every case. -/

/-- A reading as the CLI names it. -/
def parseAtom : String → Option Atom
  | "callback=noCallback" => some (.callback false)
  | "callback=withCallback" => some (.callback true)
  | "overflow=default" => some (.overflow .default)
  | "overflow=checked" => some (.overflow .checked)
  | "overflow=ignoring" => some (.overflow .ignoring)
  | "tails=solc" => some (.tail .solc)
  | "tails=clean" => some (.tail .clean)
  | "order=legacy" => some (.order .legacy)
  | "order=viaIR" => some (.order .viaIR)
  | "hash=opaque" => some (.hash .opaque)
  | "zeroAddress=noCode" => some (.zeroAddress .noCode)
  | _ => none

/-- `-` for none, else one reading. -/
def parseAtoms (s : String) : Option (List Atom) :=
  if s == "-" then some [] else (parseAtom s).map ([·])

/-- A line `require deny callback overflow tails order verdict`: whether
`Policy.verdict` of a proof under the record is the line's verdict
(`none` for a malformed line). -/
def checkLine (l : String) : Option Bool := do
  match l.splitOn " " with
  | [r, d, cb, ov, tl, od, v] =>
    let require ← parseAtoms r
    let deny ← parseAtoms d
    let callback ← match cb with | "noCallback" => some false | "withCallback" => some true | _ => none
    let overflow ← match ov with
      | "default" => some .default | "checked" => some .checked | "ignoring" => some .ignoring
      | _ => none
    let tail ← match tl with | "solc" => some .solc | "clean" => some .clean | _ => none
    let order ← match od with | "legacy" => some .legacy | "viaIR" => some .viaIR | _ => none
    let verdict ← match v with | "proved" => some Verdict.proved | "refused" => some .refused | _ => none
    let a : Assumptions := { callback, overflow, tail, order }
    pure (({ require, deny } : Policy).verdict a true == verdict)
  | _ => none

/-- info: 3192 lines, 2040 refused, 0 mismatches -/
#guard_msgs in
#eval show IO Unit from do
  let text ← IO.FS.readFile "tests/cli/assumption-policies.txt"
  let lines := (text.splitOn "\n").filter (· ≠ "")
  let bad := lines.filter (checkLine · != some true)
  let refused := lines.filter (·.endsWith " refused")
  IO.println s!"{lines.length} lines, {refused.length} refused, {bad.length} mismatches"

-- Negative controls: a flipped verdict, and a malformed line, fail.
#guard checkLine "- tails=clean noCallback default clean legacy proved" = some false
#guard checkLine "- tails=clean noCallback default clean legacy refused" = some true
#guard checkLine "- tails=dirty noCallback default clean legacy refused" = none

end Solidity.Examples.Tactics.Assumptions
