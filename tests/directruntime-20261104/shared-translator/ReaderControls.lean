import Solidity.Frontend.ExecutableAst.Shared.Translate

/-! Executed elaboration-time controls for the extracted reader callbacks.
These checks are external tests, not solc semantic-equivalence theorems,
and do not establish native/WASM compiled closure. -/
open Lean Solidity Solidity.Frontend.ExecutableAst.Shared

private def obj (xs : List (String × Json)) : Json := Json.mkObj xs
private def lit (s : String) : Json := obj [("nodeType", "Literal"), ("kind", "number"), ("value", toJson s)]
private def typed (kind : String) (fields : List (String × Json) := []) : Json :=
  obj ([("nodeType", toJson kind), ("typeDescriptions", obj [("typeString", "uint256")])] ++ fields)

#guard match expression (lit "7") with | .ok (.num 7) => true | _ => false
#guard match expression (typed "UnknownExpression") with
  | .error "compact verifier: unsupported expression" => true | _ => false
#guard match typeName (obj [("nodeType", "ElementaryTypeName"), ("name", "bytes")]) with
  | .error "compact verifier: unsupported type bytes" => true | _ => false
#guard match statements (obj [("nodeType", "DoWhileStatement")]) with
  | .error "compact verifier: unsupported statement" => true | _ => false

-- A recursively connected extension reaches children of existing parents.
private partial def extendedExpression (j : Json) : Except String RawExpr := do
  if (← node j) == "ExtensionLiteral" then return .num 9
  expressionStep extendedExpression j
private partial def extendedStatements (j : Json) : Except String (List RawStmt) :=
  statementsStep extendedExpression extendedStatements typeName j
private def binary : Json := typed "BinaryOperation"
  [("operator", "+"), ("leftExpression", typed "ExtensionLiteral"), ("rightExpression", lit "2")]
#guard match extendedExpression binary with
  | .ok (.binop .add (.num 9) (.num 2)) => true | _ => false
private def block : Json := obj [("nodeType", "Block"), ("statements", toJson #[
  obj [("nodeType", "Return"), ("expression", binary)]])]
#guard match extendedStatements block with
  | .ok [.block [.ret (some (.binop .add (.num 9) (.num 2)))]] => true | _ => false

-- Replacing only a record field does not reconnect the default statement reader.
private def disconnected : Reader := { reader with expression := extendedExpression }
#guard match disconnected.statements block with
  | .error "compact verifier: unsupported expression" => true | _ => false

-- Both branch bodies use the supplied statement callback.
private def branch (j : Json) : Except String (List RawStmt) := do
  if (← str j "branch") == "true" then return [.cont] else return [.brk]
private def conditional : Json := obj [("nodeType", "IfStatement"),
  ("condition", .null), ("trueBody", obj [("branch", "true")]),
  ("falseBody", obj [("branch", "false")])]
#guard match statementsStep (fun _ => .ok (.bool true)) branch typeName conditional with
  | .ok [.ite (.bool true) [.cont] [.brk]] => true | _ => false

-- Left-child refusal wins; errors are never reinterpreted as a fallback request.
#guard match expressionStep (fun j => if j == typed "ExtensionLiteral" then
    .error "left-child refusal" else .error "right-child refusal") binary with
  | .error "left-child refusal" => true | _ => false
#guard match statementsStep (fun _ => .error "condition refusal") branch typeName conditional with
  | .error "condition refusal" => true | _ => false

-- Type extensions also recurse through the supplied callback.
#guard match typeNameStep (fun _ => .ok (.prim .bool, .named "bool"))
    (obj [("nodeType", "ArrayTypeName"), ("baseType", .null)]) with
  | .ok (.array (.prim .bool), .array (.named "bool")) => true | _ => false
