import Solidity.Tools.DirectRuntime
open Lean Solidity
run_elab do
  let fixture ← Lean.ofExcept (Json.parse (← IO.FS.readFile "tests/directruntime-20261104/control-tuples/Obligations.ast.json"))
  let ast ← Lean.ofExcept (fixture.getObjVal? "ast")
  let nodes ← Lean.ofExcept (ast.getObjValAs? (Array Json) "nodes")
  let some source := nodes.find? (fun j => (j.getObjValAs? String "name").toOption == some "ControlTupleObligations")
    | throwError "missing production fixture"
  for (name, expected) in [("goodDo", "proved"), ("badDo", "refuted"), ("zeroWhile", "proved"),
      ("continues", "proved"), ("breaks", "proved"), ("early", "proved"),
      ("tupleSwap", "proved"), ("repeat", "proved"), ("hole", "proved"), ("reverting", "refuted")] do
    let request := Json.mkObj [("contract", source), ("function", toJson name)]
    let rows ← Lean.ofExcept (Solidity.Tools.DirectRuntime.check request)
    let rows ← Lean.ofExcept rows.getArr?
    unless rows.size == 1 do throwError "production result count {name}"
    let status ← Lean.ofExcept (rows[0]!.getObjValAs? String "status")
    unless status == expected do throwError "production {name}: {status}, expected {expected}"
    logInfo m!"PRODUCTION_CHECK {name}: {status}"
