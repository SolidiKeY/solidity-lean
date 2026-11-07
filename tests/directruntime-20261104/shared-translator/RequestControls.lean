import Solidity.Tools.DirectRuntime

/-! Request-schema and declaration-identity refusals. Listing never proves a goal. -/
namespace SharedTranslatorRequestControls
open Lean Solidity Solidity.Frontend
private def checked {α : Type} : Except String α → IO α
  | .ok value => pure value | .error e => throw (IO.userError e)
private def rejects (request : Json) (expected : String) : IO Unit := do
  match Tools.DirectRuntime.check request with
  | .error actual => unless actual == expected do throw (IO.userError s!"expected {expected}, got {actual}")
  | .ok _ => throw (IO.userError s!"accepted invalid request: {expected}")
private def controls : IO Unit := do
  let fixture ← checked (Json.parse (← IO.FS.readFile "tests/directruntime-20261104/shared-translator/artifacts/h68-bulk/ReaderFixtures.ast.json"))
  let some source := (J.nodes fixture).find? (fun n => J.kind n == "ContractDefinition")
    | throw (IO.userError "missing contract")
  let request := Json.mkObj [("contract", source), ("function", "specified"),
    ("sourceId", toJson (161 : Int)), ("listing", .bool true)]
  for value in [Json.null, .bool true, toJson (161 : Int)] do
    rejects (request.setObjVal! "function" value) "invalid function selector"
  for value in [Json.null, .bool true, "161"] do
    rejects (request.setObjVal! "sourceId" value) "invalid sourceId selector"
  for value in [Json.null, "true", toJson (1 : Nat)] do
    rejects (request.setObjVal! "listing" value) "invalid listing flag"
  for value in [Json.null, .bool true, "UnknownContract"] do
    rejects (request.setObjVal! "contract" (source.setObjVal! "nodeType" value))
      "compact verifier: expected contract definition"
  let nodes ← checked (source.getObjValAs? (Array Json) "nodes")
  for value in [Json.null, "161", toJson (-1 : Int), toJson (0 : Int)] do
    let malformed := source.setObjVal! "nodes" (toJson (nodes.map fun n =>
      if J.id? n == some 161 then n.setObjVal! "id" value else n))
    rejects (request.setObjVal! "contract" malformed) "invalid function identity"
  let duplicate := source.setObjVal! "nodes" (toJson (nodes.map fun n =>
    if J.id? n == some 219 then n.setObjVal! "id" (toJson (209 : Int)) else n))
  rejects (request.setObjVal! "contract" duplicate) "duplicate function identity"
  IO.println "Request controls: malformed selectors/flags, contract root tags and duplicate function IDs refused."
#eval controls
end SharedTranslatorRequestControls
