import Solidity.Tools.DirectRuntime

/-! Actual DirectRuntime request selection/listing controls. A ready listing
establishes obligation construction only, not proof closure or runtime correctness.
Guards exact overload identity after primitive-return admission: both wide
primitive overloads must construct; malformed sibling/refusal controls remain. -/
namespace SharedTranslatorSelectionControls
open Lean Solidity Solidity.Frontend
private def checked {α : Type} : Except String α → IO α
  | .ok value => pure value | .error e => throw (IO.userError e)
private def contractFrom (path : String) : IO Json := do
  let fixture ← checked (Json.parse (← IO.FS.readFile path))
  let some source := (J.nodes fixture).find? (fun n => J.kind n == "ContractDefinition")
    | throw (IO.userError "fixture contract missing")
  return source
private def request (source : Json) (name : String) (id : Int) : Json := Json.mkObj [
  ("contract", source), ("function", toJson name), ("sourceId", toJson id), ("listing", .bool true)]
private def oneRow (source : Json) (name : String) (id : Int) : IO Json := do
  let rows ← checked (Tools.DirectRuntime.check (request source name id))
  let rows ← checked rows.getArr?
  unless rows.size == 1 do throw (IO.userError "selection did not return exactly one row")
  let row := rows[0]!
  unless (← checked (row.getObjValAs? Int "sourceId")) == id do throw (IO.userError "selected declaration identity changed")
  unless (← checked (row.getObjValAs? String "function")) == name do throw (IO.userError "selected function name changed")
  return row
private def noSelection (source : Json) (name : String) (id : Int) : IO Unit := do
  match Tools.DirectRuntime.check (request source name id) with
  | .error "no selected functions" => pure ()
  | _ => throw (IO.userError "unmatched identity/name was accepted")
private def controls : IO Unit := do
  let source ← contractFrom "tests/directruntime-20261104/shared-translator/artifacts/h68-bulk/ReaderFixtures.ast.json"
  for id in [(209 : Int), 219] do
    let row ← oneRow source "overloaded" id
    unless (← checked (row.getObjValAs? String "status")) == "ready" do
      throw (IO.userError "primitive-return overload did not construct")
    unless (← checked (row.getObjValAs? String "reason")) == "" do
      throw (IO.userError "ready overload diagnostic changed")
  let ready ← oneRow source "specified" 161
  unless (← checked (ready.getObjValAs? String "status")) == "ready" do
    throw (IO.userError "supported selected obligation no longer constructs")
  noSelection source "overloaded" 999999
  noSelection source "specified" 209
  let nodes ← checked (source.getObjValAs? (Array Json) "nodes")
  let malformed := Json.mkObj [("nodeType", "Literal"), ("kind", "bool"), ("value", "tru"),
    ("typeDescriptions", Json.mkObj [("typeString", "bool")])]
  let nodes := nodes.map fun n => if J.id? n == some 219 then
    n.setObjVal! "body" (Json.mkObj [("nodeType", "Block"), ("statements", toJson #[
      Json.mkObj [("nodeType", "Return"), ("expression", malformed)]])]) else n
  let mutated := source.setObjVal! "nodes" (toJson nodes)
  let ready ← oneRow mutated "specified" 161
  unless (← checked (ready.getObjValAs? String "status")) == "ready" do
    throw (IO.userError "malformed unselected sibling blocked a supported selection")
  let bad ← oneRow mutated "overloaded" 219
  unless (← checked (bad.getObjValAs? String "reason")) == "a malformed boolean literal" do
    throw (IO.userError "selected malformed sibling was not refused")
  let unsupported ← contractFrom "tests/directruntime-20261104/shared-translator/artifacts/h68-bulk/UnsupportedContract.ast.json"
  match Tools.DirectRuntime.check (Json.mkObj [("contract", unsupported), ("listing", .bool true)]) with
  | .error "contract member" => pure ()
  | _ => throw (IO.userError "unsupported contract member was silently dropped")
  IO.println "DirectRuntime selection: exact overload IDs, name/ID disagreement, supported/malformed sibling isolation and contract-member refusal passed; listing is not proof closure."
#eval controls
end SharedTranslatorSelectionControls
