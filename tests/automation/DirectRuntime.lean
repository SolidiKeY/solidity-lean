import Solidity.Tools.DirectRuntime
open Lean Solidity.Tools.DirectRuntime

run_elab do
  let .ok fixture := Json.parse (← IO.FS.readFile "tests/automation/ClosedSpecs.ast.json")
    | throwError "fixture parse"
  let ast ← Lean.ofExcept (fixture.getObjVal? "ast")
  let nodes ← Lean.ofExcept (ast.getObjValAs? (Array Json) "nodes")
  let some c := nodes.find? (fun n => (n.getObjValAs? String "nodeType").toOption == some "ContractDefinition")
    | throwError "contract not found"
  let result ← Lean.ofExcept (check (Json.mkObj [("contract",c)]))
  let rows ← Lean.ofExcept result.getArr?
  for row in rows do
    let name ← Lean.ofExcept (row.getObjValAs? String "function")
    let status ← Lean.ofExcept (row.getObjValAs? String "status")
    logInfo m!"{name}: {status}"
  let actual ← rows.mapM fun row => do
    return (← Lean.ofExcept (row.getObjValAs? String "function"), ← Lean.ofExcept (row.getObjValAs? String "status"))
  unless actual == #[("maximum","proved"),("falseMaximum","refuted"),("storeMaximum","proved"),
      ("twoChoices","proved"),("constantOne","proved"),("falseConstant","refuted"),
      ("store","proved"),("falseStore","refuted")] do throwError "unexpected compact verdicts: {repr actual}"

run_elab do
  let .ok fixture := Json.parse (← IO.FS.readFile "tests/automation/DirectRuntimeAdmission.ast.json")
    | throwError "admission fixture parse"
  let ast ← Lean.ofExcept (fixture.getObjVal? "ast")
  let nodes ← Lean.ofExcept (ast.getObjValAs? (Array Json) "nodes")
  for name in ["CompactBuiltinShadow", "CompactAssertShadow"] do
    let some c := nodes.find? (fun n => (n.getObjValAs? String "name").toOption == some name)
      | throwError "missing shadow fixture"
    let rows ← Lean.ofExcept (check (Json.mkObj [("contract", c), ("function",toJson "wrong")]))
    let rows ← Lean.ofExcept rows.getArr?
    unless rows.all (fun row => (row.getObjValAs? String "status").toOption == some "unsupported") do
      throwError "user function recognized as a builtin"
  let some c := nodes.find? (fun n => (n.getObjValAs? String "name").toOption == some "CompactScopes")
    | throwError "missing scope fixture"
  for (name, expected) in [("scoped","proved"),("reusedName","proved"),("falseScoped","refuted"),("stateShadow","proved")] do
    let rows ← Lean.ofExcept (check (Json.mkObj [("contract",c),("function",toJson name)]))
    let rows ← Lean.ofExcept rows.getArr?
    unless rows.size == 1 && (rows[0]!.getObjValAs? String "status").toOption == some expected do
      throwError "incorrect block scope verdict for {name}"


run_elab do
  let .ok fixture := Json.parse (← IO.FS.readFile "tests/automation/DirectRuntimeAdmission.ast.json")
    | throwError "constants fixture parse"
  let ast ← Lean.ofExcept (fixture.getObjVal? "ast")
  let nodes ← Lean.ofExcept (ast.getObjValAs? (Array Json) "nodes")
  let some c := nodes.find? (fun n => (n.getObjValAs? String "name").toOption == some "CompactConstants")
    | throwError "missing constant fixture"
  -- Exact compiler constants are folded before lowering; 1 / 2 * 2 is 1
  -- in Solidity's compile-time rational arithmetic, not integer division.
  for (name,expected) in [("rationalConstant","refuted"),("implicitDefault","proved"),("falseImplicitDefault","refuted"),
      ("builtinAssert","proved"),("falseAfterRequire","refuted"),("reverting","proved")] do
    let rows ← Lean.ofExcept (check (Json.mkObj [("contract",c),("function",toJson name)]))
    let rows ← Lean.ofExcept rows.getArr?
    unless rows.size == 1 && (rows[0]!.getObjValAs? String "status").toOption == some expected do
      throwError "incorrect compact control verdict for {name}"
