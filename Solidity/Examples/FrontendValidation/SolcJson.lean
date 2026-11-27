import Solidity.Frontend.SolcJson.Body

/-! Literal controls for the frozen solc JSON field validators. -/
namespace Solidity.Examples.FrontendValidation.SolcJson
open Lean Solidity.Frontend

#guard (J.get (Json.mkObj [("x", .str "ok")]) "x").isOk
#guard (J.get (Json.mkObj []) "x").toOption.isNone
#guard J.opt (Json.mkObj [("x", .str "ok")]) "x" == some (.str "ok")
#guard J.opt (Json.mkObj [("x", .null)]) "x" == none
#guard J.opt (Json.mkObj []) "x" == none
#guard (J.str (Json.mkObj [("x", .str "ok")]) "x").toOption == some "ok"
#guard (J.str (Json.mkObj [("x", .bool true)]) "x").toOption.isNone
#guard (J.arr (Json.mkObj [("x", .arr #[.str "ok"])]) "x").toOption ==
  some [.str "ok"]
#guard (J.arr (Json.mkObj [("x", .str "bad")]) "x").toOption.isNone
#guard J.str? (Json.mkObj [("x", .str "ok")]) "x" == some "ok"
#guard J.str? (Json.mkObj [("x", .bool true)]) "x" == none
#guard J.arr? (Json.mkObj [("x", .arr #[])]) "x" == some #[]
#guard J.arr? (Json.mkObj [("x", .bool true)]) "x" == none
#guard J.ref? (Json.mkObj [("referencedDeclaration", toJson (7 : Int))]) == some 7
#guard J.ref? (Json.mkObj [("referencedDeclaration", .str "7")]) == none
#guard J.id? (Json.mkObj [("id", toJson (9 : Int))]) == some 9
#guard J.id? (Json.mkObj [("id", .str "9")]) == none
#guard J.hasOperatorFunction (Json.mkObj [
  ("nodeType", .str "BinaryOperation"), ("function", .null)])
#guard !J.hasOperatorFunction (Json.mkObj [
  ("nodeType", .str "Identifier"), ("function", toJson (7 : Int))])
#guard J.operatorFunction? (Json.mkObj [
  ("nodeType", .str "UnaryOperation"), ("function", toJson (7 : Int))]) == some 7
#guard J.operatorFunction? (Json.mkObj [
  ("nodeType", .str "UnaryOperation"), ("function", .null)]) == none
#guard J.typeRef? (Json.mkObj [("pathNode", Json.mkObj [
  ("referencedDeclaration", toJson (11 : Int))])]) == some 11
#guard J.typeRef? (Json.mkObj [("pathNode", .null)]) == none

end Solidity.Examples.FrontendValidation.SolcJson
