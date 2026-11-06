import Solidity.Frontend.Testing

open Lean Elab Command Solidity
set_option sol.testing.closedSpecs true

solc_import "ClosedSpecs.ast.json" hash 0xc872bb562563eeed as ClosedSpec.ClosedSpecs testing
solc_scoped_problems ClosedSpec.ClosedSpecs decl
#solkey_test ClosedSpec.ClosedSpecs to ".lake/closed-spec-results.json"

run_elab do
  let .ok json := Json.parse (← IO.FS.readFile ".lake/closed-spec-results.json")
    | throwError "invalid results"
  let rows : Array Json ← Lean.ofExcept json.getArr?
  let actual ← rows.mapM fun row => do
    return (← Lean.ofExcept (row.getObjValAs? String "function"),
      ← Lean.ofExcept (row.getObjValAs? String "status"))
  unless actual == #[("maximum","proved"),("falseMaximum","pending"),
      ("storeMaximum","proved"),("twoChoices","proved"),
      ("constantOne","proved"),("falseConstant","pending"),("store","proved"),("falseStore","pending")] do
    throwError "unexpected closed-spec results: {repr actual}"
  let .thmInfo thm ← getConstInfo ``ClosedSpec.ClosedSpecs.store.tested
    | throwError "missing checked store proof"
  unless thm.value.consumeMData.isAppOf ``Proves.fmlValid do
    throwError "the closed derivation path was not used"
  unless (thm.value.find? fun e => e.isConstOf ``Solidity.Frontend.SpecProposal.sound).isSome do
    throwError "the trimmed certificate path was not used"
