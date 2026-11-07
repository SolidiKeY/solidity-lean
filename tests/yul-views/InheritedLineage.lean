import Solidity.Frontend.SolcJson.Contract

open Lean Solidity.Frontend

/-- Executes the EXISTING frontend lineage validator on pinned compiler ASTs.
Finite fixture check, not a source/C3/compiler correspondence theorem. -/
def checkInheritedLineage (ast : Json) : IO Unit := do
  let nodes := (J.arrD ast "nodes").toList
  let some active := nodes.find? (fun n => J.str? n "name" == some "InheritedSequence")
    | throw (IO.userError "missing fixture active contract")
  let expected := ["InheritedSequence","DiamondC","DiamondB","DiamondA"]
  match contractLineage nodes active with
  | .error reason => throw (IO.userError reason)
  | .ok chain =>
    unless chain.map (fun c => (J.str? c "name").getD "") == expected do
      throw (IO.userError "wrong actual frontend C3 order")
  let ids := J.arrD active "linearizedBaseContracts"
  let bad : List (String × List Json × Json) := [
    ("reversed",nodes,active.setObjVal! "linearizedBaseContracts" (.arr ids.reverse)),
    ("trimmed",nodes,active.setObjVal! "linearizedBaseContracts" (.arr (ids.extract 0 3))),
    ("reordered",nodes,active.setObjVal! "linearizedBaseContracts" (.arr #[ids[0]!,ids[2]!,ids[1]!,ids[3]!])),
    ("duplicate",nodes,active.setObjVal! "linearizedBaseContracts" (.arr #[ids[0]!,ids[1]!,ids[1]!,ids[3]!])),
    ("missing ancestor",nodes.filter (fun n => J.str? n "name" != some "DiamondA"),active),
    ("missing identity",nodes,active.setObjVal! "id" .null)]
  for (name,units,changed) in bad do
    match contractLineage units changed with
    | .ok _ => throw (IO.userError s!"accepted malformed lineage: {name}")
    | .error reason =>
      if reason.isEmpty then throw (IO.userError "empty diagnostic")
      IO.println s!"refused {name}: {reason}"

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "AST pipelines path required")
  let asts ← match Json.parse (← IO.FS.readFile path) with
    | .ok j => match j.getArr? with
      | .ok xs => pure xs
      | .error reason => throw (IO.userError reason)
    | .error reason => throw (IO.userError reason)
  unless asts.size == 2 do throw (IO.userError "both pipelines required")
  for ast in asts do checkInheritedLineage ast
  IO.println "Frontend contractLineage: 2 pinned pipeline ASTs, 12 negative controls passed"
