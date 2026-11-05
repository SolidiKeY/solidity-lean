import Solidity.Frontend.Testing

open Lean Elab Command Solidity
set_option sol.testing.closedSpecs true
set_option trace.Solidity.Frontend.specProposal true

/-! Run with the deliberately corrupted native oracle plugin. The kernel
must reject its false closed residue, discard the declaration/error state,
and retry the original tactic. The logical definitions are unchanged. -/
solc_import "ClosedSpecs.ast.json" hash 0xc872bb562563eeed as RejectedSpec.ClosedSpecs testing
solc_scoped_problems RejectedSpec.ClosedSpecs decl
#solkey_test RejectedSpec.ClosedSpecs only "falseStore" to ".lake/rejected-closed-spec.json"
run_elab do
  let .ok json := Json.parse (← IO.FS.readFile ".lake/rejected-closed-spec.json")
    | throwError "invalid rejected results"
  let rows : Array Json ← Lean.ofExcept json.getArr?
  unless rows.size == 1 do throwError "missing rejected result"
  unless (← Lean.ofExcept (rows[0]!.getObjValAs? String "status")) == "pending" do
    throwError "a false native proposal was accepted or leaked its kernel error"
  unless !(← getEnv).contains `RejectedSpec.ClosedSpecs.falseStore.tested do
    throwError "the rejected declaration leaked"
#solkey_test RejectedSpec.ClosedSpecs only "store" to ".lake/healthy-after-rejection.json"
run_elab do
  let .ok json := Json.parse (← IO.FS.readFile ".lake/healthy-after-rejection.json")
    | throwError "invalid healthy results"
  let rows : Array Json ← Lean.ofExcept json.getArr?
  unless (← Lean.ofExcept (rows[0]!.getObjValAs? String "status")) == "proved" do
    throwError "a failed proposal damaged a later valid proof"
