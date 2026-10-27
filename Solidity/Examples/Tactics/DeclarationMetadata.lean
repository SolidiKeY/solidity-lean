import Solidity.Frontend.Testing
import Solidity.Tools.Run

/-!
# Declaration metadata from validated solc identities

The fixture exercises contract-name bytes, interface selectors without
inherited members, and canonical error/event signatures. Malformed selector
metadata and anonymous events are rejected at the importer boundary.
-/

namespace Solidity.Examples.Tactics.DeclarationMetadata

open Lean (Json toJson ofExcept)
open Frontend
open scoped Scoped

solc_import "../../../tests/solc/DeclarationMetadata.ast.json" hash 0x22c417e9ab4111f1
  as Imported.DeclarationMetadata testing
solc_scoped_problems Imported.DeclarationMetadata decl

/-- Only the child's own method contributes to its interface ID. -/
theorem ownInterface : ⊢ Imported.DeclarationMetadata.interfaceOwnOnly.problem := by
  sol_prove

/-- Source error selectors retain the canonical enum/value-type ABI signature. -/
theorem errorSelectors : ⊢ Imported.DeclarationMetadata.errorSelector.problem := by
  sol_prove

/-- Source event selectors retain all 32 bytes of the canonical tuple signature. -/
theorem eventSelector : ⊢ Imported.DeclarationMetadata.eventSelector.problem := by
  sol_prove

/-- Reading a selector still evaluates its receiver exactly once. -/
theorem evaluatesReceiver : ⊢ Imported.DeclarationMetadata.receiverEffects.problem := by
  sol_prove

/-- Selector receivers in skipped boolean/conditional arms stay skipped. -/
theorem lazyReceiver : ⊢ Imported.DeclarationMetadata.lazyReceiverEffects.problem := by
  sol_prove

/-- A generated receiver helper has no source-level internal function value. -/
example : (fnTag Imported.DeclarationMetadata "solcMetadataSelector239__").isOk = false := by
  decide +kernel

/-- Nor can an ABI function selector expose the implementation helper. -/
example : fnSelector? Imported.DeclarationMetadata "solcMetadataSelector239__" = none := by
  decide +kernel

private def event (anonymous : Bool) : Json := Json.mkObj [
  ("nodeType", .str "EventDefinition"), ("id", toJson (1 : Int)),
  ("anonymous", .bool anonymous),
  ("eventSelector", .str "0000000000000000000000000000000000000000000000000000000000000001")]

private def eventRef : Json := Json.mkObj [
  ("nodeType", .str "Identifier"), ("referencedDeclaration", toJson (1 : Int))]

/-- The full 32-byte event selector is retained. -/
example : (declarationMetadata [event false] eventRef "selector").toOption =
    some (some "bytes32(1)") := by decide +kernel

/-- Anonymous events have no selector, including in manually supplied fixtures. -/
example : (declarationMetadata [event true] eventRef "selector").isOk = false := by
  decide +kernel

/-- Truncated selector metadata cannot silently become zero. -/
example : (declarationSelector (Json.mkObj [("functionSelector", .str "123")])
    "functionSelector" 4).isOk = false := by decide +kernel

/-- Correct length alone does not admit a non-hexadecimal selector. -/
example : (declarationSelector (Json.mkObj [("errorSelector", .str "0000000g")])
    "errorSelector" 4).isOk = false := by decide +kernel

private def put (json : Json) (key : String) (value : Json) : Json :=
  Json.mkObj ((key, value) :: ((json.getObj?.toOption.map (·.toList)).getD []).filter (·.1 != key))

-- Exercise modern admission independently of the legacy fixture import above.
-- The declaration bytes and expected canonical values remain unchanged.
run_cmd do
  let fixture ← ofExcept (Json.parse (← IO.FS.readFile "tests/solc/DeclarationMetadata.ast.json"))
  let ast ← ofExcept (fixture.getObjVal? "ast")
  let modern ← ofExcept (Json.parse (← IO.FS.readFile "tests/solc/SourceAdmission.ast.json"))
  let provenance ← ofExcept (Source.read modern (← ofExcept (modern.getObjVal? "ast")))
  let declarations := J.nodes ast
  let contract := (declarations.find? (fun d => J.kind d == "ContractDefinition" &&
    J.str? d "name" == some "DeclarationMetadata")).getD .null
  let body (name : String) := ((J.nodes contract).find? (fun d =>
    J.kind d == "FunctionDefinition" && J.str? d "name" == some name)).getD .null
  let scan (a node : Json) := Admission.scan a provenance { entry := node, evaluatedRoots := [node] }
  for name in ["errorSelector", "eventSelector"] do
    unless J.kind (body name) == "FunctionDefinition" do
      throwError "missing selector control function: {name}"
    unless (scan ast (body name)).diagnostic?.isNone do
      throwError "static declaration selector was refused: {name}"
  let selector := ((J.nodes (body "errorSelector")).find? (fun d =>
    J.kind d == "MemberAccess" && J.str? d "memberName" == some "selector")).getD .null
  let some receiver := J.opt selector "expression" | throwError "missing error receiver"
  let id := (J.ref? receiver).getD (-1)
  let rec replace (fuel : Nat) (node : Json) (edit : Json → Json) : Json :=
    match fuel with
    | 0 => node
    | n + 1 =>
      let node := if J.id? node == some id then edit node else node
      match node with
      | .arr xs => .arr (xs.map fun x => replace n x edit)
      | .obj fields => Json.mkObj (fields.toList.map fun (k, v) => (k, replace n v edit))
      | _ => node
  for malformed in ["123", "0000000g"] do
    let bad := replace 128 ast (fun d => put d "errorSelector" (.str malformed))
    unless (scan bad selector).diagnostic?.isSome do
      throwError "malformed error selector admitted"
  unless (scan ast (put selector "memberName" (.str "address"))).diagnostic?.isSome do
    throwError "error declaration acquired a function address"
  let dynamicReceiver := put (put receiver "nodeType" (.str "MemberAccess")) "expression"
    (Json.mkObj [("nodeType", .str "Identifier"), ("name", .str "value"),
      ("typeDescriptions", Json.mkObj [("typeString", .str "contract DeclarationMetadata")])])
  unless (scan ast (put selector "expression" dynamicReceiver)).diagnostic?.isSome do
    throwError "effectful/non-static error receiver admitted"
  let eventSelector := ((J.nodes (body "eventSelector")).find? (fun d =>
    J.kind d == "MemberAccess" && J.str? d "memberName" == some "selector")).getD .null
  let some eventReceiver := J.opt eventSelector "expression" | throwError "missing event receiver"
  let eventId := (J.ref? eventReceiver).getD (-1)
  let malformedEvent := put (put (event false) "id" (toJson eventId)) "eventSelector" (.str "123")
  let malformedAst := Json.mkObj [("nodeType", .str "SourceUnit"), ("nodes", toJson [malformedEvent])]
  unless (scan malformedAst eventSelector).diagnostic?.isSome do
    throwError "truncated event selector admitted"
  let anonymous := put (event true) "id" (toJson eventId)
  let badAst := Json.mkObj [("nodeType", .str "SourceUnit"), ("nodes", toJson [anonymous])]
  unless (scan badAst eventSelector).diagnostic?.isSome do
    throwError "anonymous event selector admitted"

end Solidity.Examples.Tactics.DeclarationMetadata
