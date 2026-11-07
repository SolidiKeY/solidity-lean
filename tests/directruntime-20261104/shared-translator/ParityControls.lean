import Solidity.Frontend.ExecutableAst.Shared.Translate

/-! Pure producer/shared expression controls. This does not run Admission.scan,
prove source equivalence, or establish native/WASM closure. Deliberate profile
and diagnostic differences are pinned explicitly, never treated as success. -/
open Lean Solidity Solidity.Frontend.ExecutableAst.Shared
private def obj (xs : List (String × Json)) : Json := Json.mkObj xs
private def typed (kind ty : String) (fields : List (String × Json) := []) : Json :=
  obj ([("nodeType", toJson kind), ("typeDescriptions", obj [("typeString", toJson ty)])] ++
    (if kind == "BinaryOperation" then [("commonType", obj [("typeString", toJson ty)])] else []) ++ fields)
private def number (value ty : String) : Json := typed "Literal" ty [("kind", "number"), ("value", toJson value)]
private def boolean (value : String) : Json := typed "Literal" "bool" [("kind", "bool"), ("value", toJson value)]
private def producerText (j : Json) (expected : String) : Bool :=
  match (Solidity.Frontend.expr j).run' {} with | .ok s => s == expected | _ => false
private def producerError (j : Json) (expected : String) (line : Nat := 0) : Bool :=
  match (Solidity.Frontend.expr j).run' {} with
  | .error (.unsupported s l) => s == expected && l == line
  | _ => false
private def sharedError (j : Json) (expected : String) : Bool :=
  match checkedExpression j with | .error s => s == expected | _ => false

#guard producerText (boolean "true") "true"
#guard match checkedExpression (boolean "true") with | .ok (.bool true) => true | _ => false
#guard producerText (boolean "false") "false"
#guard match checkedExpression (boolean "false") with | .ok (.bool false) => true | _ => false
#guard producerError (boolean "tru") "a malformed boolean literal"
#guard sharedError (boolean "tru") "a malformed boolean literal"
#guard producerText (number "7" "int_const 7") "7"
#guard match checkedExpression (number "7" "int_const 7") with | .ok (.num 7) => true | _ => false
private def unitValue : Json := (number "1" "int_const 1000000000").setObjVal! "subdenomination" "gwei"
#guard producerText unitValue "1000000000"
#guard match checkedExpression unitValue with | .ok (.num 1000000000) => true | _ => false
private def negative : Json := typed "UnaryOperation" "int_const -7"
  [("operator", "-"), ("prefix", .bool true), ("subExpression", number "7" "int_const 7")]
#guard producerText negative "-7"
#guard match checkedExpression negative with | .ok (.unop .neg (.num 7)) => true | _ => false
#guard producerError (number "0.5" "rational_const 1 / 2") "the constant `1/2`, which is not an integer"
#guard sharedError (number "0.5" "rational_const 1 / 2") "nonintegral compiler constant"
#guard producerError (typed "UnknownExpression" "uint256") "the expression `UnknownExpression`"
#guard sharedError (typed "UnknownExpression" "uint256") "compact verifier: unsupported expression"
#guard producerError (typed "UnknownExpression" "int_const 7") "the expression `UnknownExpression`"
#guard sharedError (typed "UnknownExpression" "int_const 7") "nonintegral compiler constant"
#guard producerText (number "0xff" "uint256") "255"
#guard sharedError (number "0xff" "uint256") "nondecimal literal"

private def binary : Json := typed "BinaryOperation" "uint256" [("operator", "+"),
  ("leftExpression", typed "Identifier" "uint256" [("name", "x")]),
  ("rightExpression", number "1" "int_const 1"), ("line", toJson (17 : Nat))]
#guard producerText binary "«x» + 1"
#guard match checkedExpression binary with | .ok (.binop .add (.name "x") (.num 1)) => true | _ => false
private def malformedAlias : Json := binary.setObjVal! "function" .null
#guard producerError malformedAlias "a malformed resolved operator function annotation" 17
#guard sharedError malformedAlias "a malformed resolved operator function annotation"
#guard sharedError (negative.setObjVal! "function" .null) "a malformed resolved operator function annotation"
#guard sharedError (binary.setObjVal! "function" (toJson (0 : Int))) "an operator alias must name a positive declaration identity"
#guard sharedError (binary.setObjVal! "function" (toJson (12 : Int))) "compact verifier: unsupported operator alias"

-- Old node/operator/child errors retain priority over newly refused metadata.
#guard sharedError (malformedAlias.setObjVal! "leftExpression" (typed "UnknownExpression" "uint256"))
  "compact verifier: unsupported expression"
#guard sharedError (malformedAlias.setObjVal! "operator" "unknown") "binary operator"

-- An old later-sibling refusal wins even when an earlier child is malformed.
private def malformedSibling : Json := typed "BinaryOperation" "bool" [("operator", "&&"),
  ("leftExpression", boolean "tru"), ("rightExpression", typed "UnknownExpression" "bool")]
#guard sharedError malformedSibling "compact verifier: unsupported expression"

-- Folding must not hide nested malformed metadata or resolved operator aliases.
private def folded : Json := typed "BinaryOperation" "int_const 3" [("operator", "+"),
  ("leftExpression", number "2" "int_const 2"), ("rightExpression", number "1" "int_const 1")]
private def foldedAlias : Json := folded.setObjVal! "leftExpression"
  (negative.setObjVal! "function" .null)
#guard sharedError foldedAlias "a malformed resolved operator function annotation"
#guard sharedError (folded.setObjVal! "leftExpression" (negative.setObjVal! "function" (toJson (12 : Int))))
  "compact verifier: unsupported operator alias"
#guard sharedError (folded.setObjVal! "leftExpression" ((boolean "2").setObjVal! "typeDescriptions"
    (obj [("typeString", "int_const 2")]))) "a malformed boolean literal"

-- Whole-function decoding also preserves a later unsupported sibling statement.
private def functionRoot (ss : Array Json) : Json := obj [
  ("nodeType", "FunctionDefinition"), ("kind", "function"), ("name", "f"),
  ("stateMutability", "pure"), ("parameters", obj [("parameters", toJson (#[] : Array Json))]),
  ("returnParameters", obj [("parameters", toJson (#[] : Array Json))]),
  ("body", obj [("nodeType", "Block"), ("statements", toJson ss)])]
private def malformedReturn : Json := obj [("nodeType", "Return"), ("expression", boolean "tru")]
#guard match function reader (functionRoot #[malformedReturn]) "" with
  | .error "a malformed boolean literal" => true | _ => false
#guard match function reader (functionRoot #[malformedReturn, obj [("nodeType", "UnknownStatement")]]) "" with
  | .error "compact verifier: unsupported statement" => true | _ => false

-- A malformed sibling function must not reject another selected function.
private def malformedFunction : Json := (functionRoot #[malformedReturn]).setObjVal! "name" "bad"
private def cleanFunction : Json := (functionRoot #[]).setObjVal! "name" "good"
private def siblingContract : Json := obj [("nodeType", "ContractDefinition"),
  ("contractKind", "contract"), ("nodes", toJson #[malformedFunction, cleanFunction])]
#guard match contract reader siblingContract with | .ok _ => true | _ => false
#guard match function reader cleanFunction "" with | .ok ("good", _) => true | _ => false
#guard match function reader malformedFunction "" with
  | .error "a malformed boolean literal" => true | _ => false

-- Root tags are part of admission, even when all legacy payload fields decode.
#guard match contract reader (siblingContract.setObjVal! "nodeType" "UnknownContract") with
  | .error "compact verifier: expected contract definition" => true | _ => false
#guard match contract reader (siblingContract.setObjVal! "nodeType" .null) with
  | .error "compact verifier: expected contract definition" => true | _ => false
#guard match function reader (cleanFunction.setObjVal! "nodeType" "UnknownFunction") "" with
  | .error "compact verifier: expected function definition" => true | _ => false
#guard match function reader (cleanFunction.setObjVal! "nodeType" .null) "" with
  | .error "compact verifier: expected function definition" => true | _ => false
-- Legacy payload refusal still wins over the newly checked root tag.
#guard match function reader ((functionRoot #[obj [("nodeType", "UnknownStatement")]]).setObjVal! "nodeType" "UnknownFunction") "" with
  | .error "compact verifier: unsupported statement" => true | _ => false
#guard match contract reader ((siblingContract.setObjVal! "nodes" (toJson #[obj [("nodeType", "UnknownMember")]])).setObjVal! "nodeType" "UnknownContract") with
  | .error "contract member" => true | _ => false

-- Folded descendants still require compiler expression headers.
#guard sharedError (folded.setObjVal! "leftExpression" ((number "2" "int_const 2").setObjVal! "typeDescriptions" .null))
  "expression lacks its compiler type"
#guard sharedError (folded.setObjVal! "leftExpression" (negative.setObjVal! "prefix" .null))
  "unary expression lacks its prefix flag"
#guard sharedError (folded.setObjVal! "commonType" .null)
  "binary expression lacks its common type"
