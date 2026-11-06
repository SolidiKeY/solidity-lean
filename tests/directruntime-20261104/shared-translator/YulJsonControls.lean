import Solidity.Frontend.SolcJson.Yul
import Solidity.Frontend.ExecutableAst.Shared.Translate

/-! Direct JSON decoder/static/shape controls. They do not establish whole
assembly admission, Solidity execution correspondence, or backend closure. -/
namespace SharedTranslatorYulControls
open Lean Solidity Solidity.Frontend
private def obj (xs : List (String × Json)) : Json := Json.mkObj xs
private def lit (kind value : String) : Json := obj [("nodeType", "YulLiteral"),
  ("type", ""), ("kind", toJson kind), ("value", toJson value)]
private def ident (name : String) : Json := obj [("nodeType", "YulIdentifier"), ("name", toJson name)]
private def block (xs : Array Json := #[]) : Json := obj [("nodeType", "YulBlock"), ("statements", toJson xs)]
private def caseNode (value : Json) : Json := obj [("nodeType", "YulCase"), ("value", value), ("body", block)]
private def switchNode (cases : Array Json) : Json := obj [("nodeType", "YulSwitch"),
  ("expression", lit "number" "0"), ("cases", toJson cases)]
private def env0 : Yul.ExprEnv [] [] 0 := { locals := [], functions := [], externals := [] }

#check YulJson.CheckedExpression.contract
#check YulJson.ShapedBlock.contract
#guard match YulJson.expressionAux 0 (lit "number" "1") with
  | .error .depth => true | _ => false
#guard match YulJson.literal (lit "bool" "tru") with
  | .error (.literal "bool") => true | _ => false
#guard match YulJson.typedName (obj [("nodeType", "YulTypedName"), ("name", "x"), ("type", "uint256")]) with
  | .error (.annotation "uint256") => true | _ => false
#guard match YulJson.identifierPath (ident "x..y") with
  | .error (.identifier "x..y") => true | _ => false
#guard match YulJson.expressionAux 8 (obj [("nodeType", "YulFunctionCall"),
    ("functionName", ident "foo.bar"), ("arguments", toJson (#[] : Array Json))]) with
  | .error (.identifier "foo.bar") => true | _ => false
#guard match YulJson.expressionAux 8 (obj [("nodeType", "YulFunctionCall"), ("functionName", ident "add")]) with
  | .error (.field "arguments") => true | _ => false
#guard match YulJson.statementAux 8 (obj [("nodeType", "YulVariableDeclaration"), ("variables", toJson (#[] : Array Json))]) with
  | .error (.node "empty variable declaration") => true | _ => false
#guard match YulJson.statementAux 8 (obj [("nodeType", "YulAssignment"), ("variableNames", toJson (#[] : Array Json))]) with
  | .error (.node "empty assignment") => true | _ => false
#guard match YulJson.statementAux 8 (switchNode #[]) with
  | .error (.node "empty switch") => true | _ => false
#guard match YulJson.statementAux 8 (switchNode #[caseNode (lit "bool" "true"), caseNode (lit "number" "1")]) with
  | .error (.node "duplicate case word") => true | _ => false
#guard match YulJson.statementAux 8 (switchNode #[caseNode "default", caseNode (lit "number" "1")]) with
  | .error (.node "default must be last") => true | _ => false
#guard match YulJson.checkBlockShape 8 (block #[obj [("nodeType", "YulExpressionStatement"), ("expression", lit "number" "1")]]) with
  | .error .shape => true | _ => false
#guard match YulJson.checkExpression env0 8 (ident "missing") with
  | .error .staticExpression => true | _ => false
#guard match YulJson.checkExpression env0 8 (lit "number" "7") with
  | .ok _ => true | _ => false
#guard match YulJson.expressionAux 8 (obj [("nodeType", "UnknownYul")]) with
  | .error (.node "UnknownYul") => true | _ => false
#guard match YulJson.expressionAux 8 (obj []) with
  | .error (.field "nodeType") => true | _ => false
#guard match ExecutableAst.Shared.checkedStatements (obj [("nodeType", "Throw")]) with
  | .error "compact verifier: unsupported statement" => true | _ => false

private def checkedJson {α : Type} : Except String α → IO α
  | .ok value => pure value | .error e => throw (IO.userError e)
private def requireDecode {α : Type} : Except YulJson.Error α → IO α
  | .ok value => pure value | .error e => throw (IO.userError (reprStr e))
private def fixtureControls : IO Unit := do
  let fixture ← checkedJson (Json.parse (← IO.FS.readFile "tests/directruntime-20261104/shared-translator/artifacts/h68-bulk/YulKinds.ast.json"))
  let some assembly := (J.nodes fixture).find? (fun n => J.kind n == "InlineAssembly")
    | throw (IO.userError "missing source assembly fixture")
  let ast ← checkedJson (assembly.getObjVal? "AST")
  let kinds := (J.nodes ast).map J.kind
  let expected := ["YulAssignment", "YulBlock", "YulBreak", "YulCase", "YulContinue",
    "YulExpressionStatement", "YulForLoop", "YulFunctionCall", "YulFunctionDefinition",
    "YulIdentifier", "YulIf", "YulLeave", "YulLiteral", "YulSwitch", "YulTypedName", "YulVariableDeclaration"]
  unless expected.all kinds.contains do throw (IO.userError "source fixture lacks a required Yul kind")
  let _ ← requireDecode (YulJson.parseBlock (ast.compress.toUTF8.size + 1) ast)
  let _ ← requireDecode (YulJson.checkBlockShape (ast.compress.toUTF8.size + 1) ast)
  IO.println "YulJson: 16 compiler-emitted kinds decoded; grammar shape checked; no whole-assembly admission/execution claim."
#eval fixtureControls
end SharedTranslatorYulControls
