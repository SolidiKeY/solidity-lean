import Solidity.Lowering.P8.SourceAstTupleCorrespondence

/-! Runtime checks of every expression node in both existing LibraryTry ASTs.
Regression purpose: retain delegated storage receiver t, the dirty write of 9,
return tuple order, holes, empty/inline tuple refusal and failure string bytes.
These checks are not Source
resolution/execution/admission or independent compiler validation. -/
namespace H62.StorageAudit.SourceAstExpressionsControls
open Lean Solidity.Source Solidity.Lowering.P8.SourceAstExpressions

def children : Json → List Json
  | .obj values => values.toList.map Prod.snd
  | .arr values => values.toList
  | _ => []

def expressions : Nat → Json → Except String (List Json)
  | 0, _ => .error "fixture traversal depth exhausted"
  | fuel + 1, node => do
    let nested ← (children node).mapM (expressions fuel)
    let kind := (node.getObjValAs? String "nodeType").toOption.getD ""
    let own := if ["Identifier", "Literal", "MemberAccess", "FunctionCall",
      "Assignment", "TupleExpression"].contains kind then [node] else []
    return own ++ nested.flatten

def delegated : Syn .expr → Bool
  | .call (.member (.ident "t") "stru") _ => true
  | _ => false

def dirtyWrite : Syn .expr → Bool
  | .assign .assign (.member (.ident "t") "x") (.lit (.num (.dec 9 0 0))) => true
  | _ => false

def failureBytes : Syn .expr → Bool
  | .lit (.str bytes) => bytes == "failure".toUTF8.toList
  | _ => false

def successTuple : Syn .expr → Bool
  | .tuple (.some (.ident "x")) (.cons (.some (.lit (.str []))) .nil) => true
  | _ => false

def inspect (doc : Json) : Except String Nat := do
  let nodes ← expressions 128 (← doc.getObjVal? "ast")
  let converted ← nodes.mapM (expression 128)
  unless nodes.length == 37 && (converted.filter delegated).length == 1 do
    throw "expression census or delegated receiver changed"
  unless (converted.filter dirtyWrite).length == 1 &&
      (converted.filter failureBytes).length == 2 &&
      (converted.filter successTuple).length == 1 do
    throw "storage write, literal bytes or tuple order changed"
  let some member := nodes.find? (fun node =>
    (node.getObjValAs? String "nodeType").toOption == some "MemberAccess")
    | throw "missing nontrivial depth control"
  unless !(expression 1 member).isOk && (expression 2 member).isOk do
    throw "nonzero member-depth boundary changed"
  return converted.length

/-- Malformed inputs and unsupported operators must not silently become a
successful expression. These runtime checks do not restrict Source semantics. -/
def refusalChecks : Except String Unit := do
  for raw in [
    "{\"nodeType\":\"TupleExpression\",\"isInlineArray\":false,\"components\":[]}",
    "{\"nodeType\":\"TupleExpression\",\"isInlineArray\":true,\"components\":[]}",
    "{\"nodeType\":\"Literal\",\"kind\":\"string\",\"hexValue\":\"f\"}",
    "{\"nodeType\":\"Literal\",\"kind\":\"string\",\"hexValue\":\"66_66\"}",
    "{\"nodeType\":\"Assignment\",\"operator\":\"+=\"}",
    "{\"nodeType\":\"FunctionCall\",\"kind\":\"functionCall\",\"names\":[\"x\"]}",
    "{\"nodeType\":\"Literal\",\"kind\":\"number\",\"value\":\"9\",\"subdenomination\":\"ether\"}"] do
    unless !(expression 128 (← Json.parse raw)).isOk do throw "invalid expression accepted"

  let hole ← Json.parse "{\"nodeType\":\"TupleExpression\",\"isInlineArray\":false,\"components\":[null,{\"nodeType\":\"Identifier\",\"name\":\"x\"}]}"
  match ← expression 128 hole with
  | .tuple .none (.cons (.some (.ident "x")) .nil) => pure ()
  | _ => throw "tuple hole or trailing component changed"

#eval do
  match refusalChecks with
  | .error why => throw (IO.userError why)
  | .ok _ => pure ()
  for file in ["tests/solc/LibraryTry.ast.json", "tests/solc/LibraryTryIR.ast.json"] do
    let raw ← IO.FS.readFile file
    match (do inspect (← Json.parse raw)) with
    | .ok n => IO.println s!"{file}: {n} actual expressions converted"
    | .error why => throw (IO.userError why)
end H62.StorageAudit.SourceAstExpressionsControls
