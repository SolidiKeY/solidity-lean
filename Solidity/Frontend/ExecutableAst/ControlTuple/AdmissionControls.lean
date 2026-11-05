import Solidity.Frontend.ExecutableAst.ControlTuple.Adapter
import Lean.Elab.Command

/-! Executable admission controls. These are reader checks, not proof certificates. -/
namespace Solidity.Frontend.ExecutableAst.ControlTuple.Controls
open Lean

private def lit (n : String) : Json := Json.mkObj [
  ("nodeType", toJson "Literal"), ("kind", toJson "number"), ("value", toJson n),
  ("typeDescriptions", Json.mkObj [("typeString", toJson s!"int_const {n}")])]
private def ident (n : String) : Json := Json.mkObj [
  ("nodeType", toJson "Identifier"), ("name", toJson n),
  ("typeDescriptions", Json.mkObj [("typeString", toJson "uint256")])]
private def tup (cs : List Json) : Json := Json.mkObj [
  ("nodeType", toJson "TupleExpression"), ("isInlineArray", toJson false),
  ("components", Json.arr cs.toArray),
  ("typeDescriptions", Json.mkObj [("typeString", toJson "tuple(uint256,uint256)")])]
private def assign (ls rs : Json) : Json := Json.mkObj [
  ("nodeType", toJson "ExpressionStatement"), ("expression", Json.mkObj [
    ("nodeType", toJson "Assignment"), ("operator", toJson "="),
    ("leftHandSide", ls), ("rightHandSide", rs)])]
private def accepted {α : Type} : Except String α → Bool
  | .ok _ => true | .error _ => false

#guard match expression (tup [lit "1", lit "2"]) with
  | .ok (.tuple [.num 1, .num 2]) => true | _ => false
#guard match expression (tup [ident "x"]) with
  | .ok (.name "x") => true | _ => false
#guard match statements (assign (tup [ident "a", .null]) (tup [lit "1", lit "2"])) with
  | .ok [.tupleAssign [some (.name "a"), none] (.tuple [.num 1, .num 2])] => true
  | _ => false
#guard match statements (assign (tup [ident "a", ident "a"]) (tup [lit "1", lit "2"])) with
  | .ok [.tupleAssign [some (.name "a"), some (.name "a")] (.tuple [.num 1, .num 2])] => true
  | _ => false
#guard !accepted (expression (tup []))
#guard !accepted (expression (tup [lit "1", .null]))
#guard !accepted (expression ((tup [lit "1", lit "2"]).setObjVal! "isInlineArray" (toJson true)))
#guard !accepted (expression ((tup [lit "1", lit "2"]).setObjVal! "typeDescriptions" (Json.mkObj [])))
#guard !accepted (expression (tup [lit "1", tup [lit "2", lit "3"]]))
#guard !accepted (statements (assign (tup [.null, .null]) (tup [lit "1", lit "2"])))
#guard !accepted (statements (assign (tup [ident "a", ident "b"]) (tup [lit "1"])))
#guard !accepted (statements (assign (tup [lit "1", ident "b"]) (tup [lit "1", lit "2"])))
#guard match target (fun _ => .error "child failure") (ident "a") with
  | .error "child failure" => true | _ => false
#guard match values (fun _ => .error "child failure") 2 (tup [lit "1", lit "2"]) with
  | .error "child failure" => true | _ => false

#guard !accepted (preserveDiscarded [false, true] (.tuple [.field (.name "r") "x", .num 1]))
#guard accepted (preserveDiscarded [false, true] (.tuple [.binop .div (.num 1) (.num 0), .num 1]))

private def loop (clauses : List String) : Json := Json.mkObj [
  ("nodeType", toJson "DoWhileStatement"), ("loopSpec", toJson clauses),
  ("body", Json.mkObj [("nodeType", toJson "Block"), ("statements", Json.arr #[])]),
  ("condition", Json.mkObj [("nodeType", toJson "Literal"), ("kind", toJson "bool"),
    ("value", toJson "false")])]
#guard match statements (loop ["unwind 1"]) with
  | .ok [.doWhile spec [.block []] (.bool false)] => spec.unwind == some 1
  | _ => false
#guard match statements (loop ["invariant true", "decreases 1"]) with
  | .ok [.doWhile spec _ _] => spec.qinv.length == 1 && spec.dec.isSome
  | _ => false
#guard !accepted (statements (loop ["unwind 1", "unwind 2"]))
#guard !accepted (statements (loop ["decreases 1", "decreases 2"]))
#guard match statementsStep expression (fun _ => .error "body failure") Shared.typeName (loop []) with
  | .error "body failure" => true | _ => false

run_elab do
  let fixture ← Lean.ofExcept (Json.parse (← IO.FS.readFile
    "tests/directruntime-20261104/control-tuples/Controls.ast.json"))
  let ast ← Lean.ofExcept (fixture.getObjVal? "ast")
  let nodes ← Lean.ofExcept (ast.getObjValAs? (Array Json) "nodes")
  let some contract := nodes.find? (fun j => (j.getObjValAs? String "name").toOption == some "ControlTuples")
    | throwError "missing fixture contract"
  let nodes ← Lean.ofExcept (contract.getObjValAs? (Array Json) "nodes")
  for (name, expected) in [("executeFirst", true), ("whileZero", true),
      ("continueTest", true), ("breakTest", true), ("earlyReturn", true),
      ("swap", true), ("declaration", true), ("skipped", true), ("repeated", true),
      ("aliased", false), ("sideEffect", false), ("inlineArray", false), ("callTuple", false)] do
    let some j := nodes.find? (fun j => (j.getObjValAs? String "name").toOption == some name)
      | throwError "missing fixture function {name}"
    unless accepted (Shared.function reader j contract.compress) == expected do
      throwError "unexpected reader admission for {name}: {repr (Shared.function reader j contract.compress)}"
  logInfo "13 fixture admission expectations passed; no intrinsic proof or runtime verdict implied"
end Solidity.Frontend.ExecutableAst.ControlTuple.Controls
