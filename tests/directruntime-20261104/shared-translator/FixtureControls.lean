import Solidity.Frontend.ExecutableAst.Shared.Translate

/-! Real-solc source-admission controls. These execute the raw reader only;
no formula proof, semantic equivalence or native/WASM closure is claimed. -/
open Lean Solidity Solidity.Frontend Solidity.Frontend.ExecutableAst.Shared
private def checked {α : Type} : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError e)
private def fixtureContract (path : String) : IO Json := do
  let json ← checked (Json.parse (← IO.FS.readFile path))
  let ast ← checked (field json "ast")
  let some c := (J.nodes ast).find? (fun n => J.kind n == "ContractDefinition")
    | throw (IO.userError "fixture has no contract")
  return c
private def fixtureControls : IO Unit := do
  let source ← fixtureContract "tests/directruntime-20261104/shared-translator/artifacts/h68-bulk/ReaderFixtures.ast.json"
  let _ ← checked (contract reader source)
  let mut rows : Array Json := #[]
  let mut overloadIds : List Int := []
  for n in ← checked (arr source "nodes") do
    unless J.kind n == "FunctionDefinition" do continue
    let name ← checked (str n "name")
    let id ← checked (n.getObjValAs? Int "id")
    let expected := match name with
      | "unsupportedMemory" => some "compact verifier: unsupported type uint256[]"
      | "unsupportedTuple" => some "compact verifier: unsupported expression"
      | "unsupportedDoWhile" => some "compact verifier: unsupported statement"
      | _ => none
    let result := function reader n source.compress
    match expected, result with
    | none, .ok (modelName, _) =>
      unless modelName == name do throw (IO.userError "model name changed")
    | some e, .error actual =>
      unless actual == e do throw (IO.userError s!"{name}: expected {e}; got {actual}")
    | none, .error actual => throw (IO.userError s!"{name}: unexpected refusal {actual}")
    | some e, .ok _ => throw (IO.userError s!"{name}: unsupported became success; expected {e}")
    if name == "overloaded" then overloadIds := id :: overloadIds
    rows := rows.push (Json.mkObj [("sourceId", toJson id), ("function", toJson name),
      ("outcome", toJson (match result with | .ok _ => "admitted" | .error e => e))])
  unless rows.size == 9 do throw (IO.userError "fixture function count changed")
  unless overloadIds.length == 2 && overloadIds[0]! != overloadIds[1]! do
    throw (IO.userError "overload source identities were lost")
  let unsupported ← fixtureContract "tests/directruntime-20261104/shared-translator/artifacts/h68-bulk/UnsupportedContract.ast.json"
  match contract reader unsupported with
  | .error "contract member" => pure ()
  | _ => throw (IO.userError "unsupported contract sibling was ignored")
  IO.println (Json.mkObj [("rawReaderFixtureRows", Json.arr rows),
    ("unsupportedContractSibling", "contract member"),
    ("proofBoundary", "source admission only; no formula/native/WASM proof")]).compress
#eval fixtureControls
