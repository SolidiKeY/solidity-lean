import Solidity.Frontend.Testing

open Lean Elab Command Solidity
set_option sol.testing.direct true

solc_import "ClosedSpecs.ast.json" hash 0xc872bb562563eeed as DirectCheck.ClosedSpecs testing
solc_scoped_problems DirectCheck.ClosedSpecs decl
#solkey_test DirectCheck.ClosedSpecs to ".lake/direct-check-results.json"

run_elab do
  let .ok json := Json.parse (← IO.FS.readFile ".lake/direct-check-results.json")
    | throwError "invalid direct results"
  let rows : Array Json ← Lean.ofExcept json.getArr?
  let actual ← rows.mapM fun row => do
    return (← Lean.ofExcept (row.getObjValAs? String "function"),
      ← Lean.ofExcept (row.getObjValAs? String "status"))
  unless actual == #[("maximum","proved"),("falseMaximum","refuted"),
      ("storeMaximum","proved"),("twoChoices","proved"),
      ("constantOne","proved"),("falseConstant","refuted"),("store","proved"),("falseStore","refuted")] do
    throwError "unexpected direct verdicts: {repr actual}"
  if debug.skipKernelTC.get (← getOptions) then throwError "temporary evaluation option escaped"
  for row in rows do
    unless (← Lean.ofExcept (row.getObjValAs? String "verification")) == "direct" do
      throwError "missing direct mode identity"
    if (← Lean.ofExcept (row.getObjValAs? String "status")) == "refuted" then
      let witness ← Lean.ofExcept (row.getObjVal? "counterexample")
      unless (← Lean.ofExcept (witness.getObjValAs? Bool "certified")) == false do
        throwError "direct result falsely claims a certificate"
      if let .ok _ := witness.getObjVal? "certificateDeclaration" then
        throwError "direct result contains a certificate declaration"
  for name in [``DirectCheck.ClosedSpecs.store, ``DirectCheck.ClosedSpecs.falseStore] do
    if (← getEnv).contains (name ++ `tested) || (← getEnv).contains (name ++ `refuted) then
      throwError "direct mode constructed a proof declaration"
