import Solidity.Frontend.SolcJson.Admission
import Solidity.Frontend.ExecutableAst.Shared.Translate

/-! Admission diagnostic controls and Shared expression-header refusal parity.
These check diagnostic categories separately from executable refusal strings. -/
namespace SharedTranslatorAdmissionControls
open Lean Solidity Solidity.Frontend
private def obj (xs : List (String × Json)) : Json := Json.mkObj xs
private def checked {α : Type} : Except String α → IO α
  | .ok value => pure value | .error e => throw (IO.userError e)
private def sharedRefusal (node : Json) (expected : String) : Bool :=
  match ExecutableAst.Shared.checkedExpression node with
  | .error actual => actual == expected | .ok _ => false
private def controls : IO Unit := do
  let fixture ← checked (Json.parse (← IO.FS.readFile "tests/directruntime-20261104/shared-translator/artifacts/h68-bulk/ReaderFixtures.ast.json"))
  let ast ← checked (fixture.getObjVal? "ast")
  let provenance ← checked (Source.read fixture ast)
  let check (node : Json) (kind : Source.DiagnosticKind) (name : Lean.Name) (line : Nat) : IO Unit := do
    let result := Admission.scan ast provenance { entry := node, evaluatedRoots := [node] }
    unless result.diagnostic?.any (fun d => d.kind == kind && d.name == name && d.line == line) do
      throw (IO.userError s!"admission diagnostic mismatch: {repr result.diagnostic?}")
  check (obj [("nodeType", "FutureSyntax"), ("line", toJson (47 : Nat))])
    .unknownNode `solidity.unknownAstNode 47
  check (obj [("nodeType", .bool true), ("line", toJson (48 : Nat))])
    .unknownNode `solidity.unknownAstNode 48
  let number := obj [("nodeType", "Literal"), ("kind", "number"), ("value", "1"), ("line", toJson (49 : Nat))]
  check number .invalidAst `solidity.expressionType 49
  unless sharedRefusal number "expression lacks its compiler type" do
    throw (IO.userError "literal header was accepted")
  let typed := number.setObjVal! "typeDescriptions" (obj [("typeString", "uint256")])
  let unary := obj [("nodeType", "UnaryOperation"), ("operator", "-"),
    ("subExpression", typed), ("typeDescriptions", obj [("typeString", "uint256")]), ("line", toJson (50 : Nat))]
  check unary .invalidAst `solidity.unaryPrefix 50
  unless sharedRefusal unary "unary expression lacks its prefix flag" do
    throw (IO.userError "unary prefix header was accepted")
  check (unary.setObjVal! "prefix" .null) .invalidAst `solidity.unaryPrefix 50
  let binary := obj [("nodeType", "BinaryOperation"), ("operator", "+"),
    ("leftExpression", typed), ("rightExpression", typed),
    ("typeDescriptions", obj [("typeString", "uint256")]), ("line", toJson (51 : Nat))]
  check binary .invalidAst `solidity.commonType 51
  unless sharedRefusal binary "binary expression lacks its common type" do
    throw (IO.userError "binary common-type header was accepted")
  let duplicate := obj [("nodeType", "FunctionDefinition"), ("id", toJson (123 : Int)), ("line", toJson (52 : Nat))]
  let result := Admission.scan (.arr #[duplicate, duplicate]) provenance { entry := typed, evaluatedRoots := [typed] }
  unless result.diagnostic?.any (fun d => d.kind == .invalidAst && d.name == `solidity.duplicateDeclaration && d.line == 52) do
    throw (IO.userError "duplicate declaration identity was not refused")
  IO.println "Admission diagnostics checked by kind/name/line; matching Shared header refusals checked."
#eval controls
end SharedTranslatorAdmissionControls
