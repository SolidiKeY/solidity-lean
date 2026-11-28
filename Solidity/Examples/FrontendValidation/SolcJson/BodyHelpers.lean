import Solidity.Frontend.SolcJson.Contract

/-! Literal controls for otherwise unexercised expression/body helpers. -/
namespace Solidity.Examples.FrontendValidation.SolcJson.BodyHelpers
open Lean Solidity.Frontend

#guard Q.sub ⟨3, 1⟩ ⟨1, 1⟩ == some ⟨2, 1⟩
#guard (Q.sub ⟨3, 0⟩ ⟨1, 1⟩).isNone
#guard Q.div ⟨3, 1⟩ ⟨1, 1⟩ == some ⟨3, 1⟩
#guard (Q.div ⟨3, 1⟩ ⟨0, 1⟩).isNone

private def structType : Json := Json.mkObj [
  ("typeDescriptions", Json.mkObj [("typeString", .str "struct C.S storage ref")])]
#guard ((pushedTy structType).run'
  { structs := [("#canonicalC.S", .ok "S")] }).toOption == some "«S»"
#guard ((pushedTy structType).run' default).toOption.isNone
#guard ((storageRefTy structType).run'
  { structs := [("#canonicalC.S", .ok "S")] }).toOption == some "«S»"
#guard ((storageRefTy structType).run' default).toOption.isNone

#guard staticCompilerLength? "00ff" == some 2
#guard (staticCompilerLength? "0").isNone
#guard specReadsName "x" ["x.field"]
#guard !specReadsName "x" ["\\", "x"]
#guard isNamedCall (Json.mkObj [("nodeType", .str "FunctionCall"),
  ("expression", Json.mkObj [("nodeType", .str "Identifier")])])
#guard !isNamedCall (Json.mkObj [("nodeType", .str "FunctionCall"),
  ("expression", Json.mkObj [("nodeType", .str "Literal")])])
#guard condCalleeOk (Json.mkObj [("nodeType", .str "FunctionCall"),
  ("expression", Json.mkObj [("nodeType", .str "Literal")]), ("arguments", .arr #[])])
#guard !condCalleeOk (Json.mkObj [("nodeType", .str "FunctionCall"),
  ("expression", Json.mkObj [("nodeType", .str "FunctionCall"),
    ("kind", .str "functionCall")]), ("arguments", .arr #[])])

private def number : Json := Json.mkObj [
  ("nodeType", .str "Literal"), ("kind", .str "number"), ("value", .str "1"),
  ("typeDescriptions", Json.mkObj [("typeString", .str "int_const 1")])]
#guard (tupleAssignmentLeaves .null number).isOk
#guard (tupleAssignmentLeaves .null .null).toOption.isNone
#guard ((explicitTupleAssignment .null number).run' default).isOk
#guard ((explicitTupleAssignment .null .null).run' default).toOption.isNone
#guard ((localStmt (Json.mkObj [("nodeType", .str "PlaceholderStatement")])).run'
  default).toOption == some ["_"]
#guard ((localStmt (Json.mkObj [("nodeType", .str "Invalid")])).run' default).toOption.isNone

private def plainArray : Json := Json.mkObj [("nodeType", .str "ArrayTypeName"),
  ("baseType", Json.mkObj [("nodeType", .str "ElementaryTypeName"), ("name", .str "uint")])]
private def enumDeclaration : Json :=
  Json.mkObj [("nodeType", .str "EnumDefinition"), ("id", toJson (7 : Int))]
private def enumArray : Json := Json.mkObj [("nodeType", .str "ArrayTypeName"),
  ("baseType", Json.mkObj [("nodeType", .str "UserDefinedTypeName"),
    ("referencedDeclaration", toJson (7 : Int))])]
-- True marks the unsafe aggregate; the operational checker refuses it.
#guard !errorAggregateHasEnum [] plainArray
#guard errorAggregateHasEnum [enumDeclaration] enumArray
#guard ((checkErrorAggregateParams [Json.mkObj [("typeName", plainArray)]]).run' default).isOk
#guard ((checkErrorAggregateParams [Json.mkObj [("typeName", enumArray)]]).run'
  { declarations := [enumDeclaration] }).toOption.isNone

private def owned : Json := Json.mkObj [("id", toJson (1 : Int))]
private def owner : Json := Json.mkObj [
  ("nodeType", .str "ContractDefinition"), ("id", toJson (9 : Int)),
  ("nodes", .arr #[owned])]
#guard declarationOwner [owner] owned == some 9
#guard (declarationOwner [owner] (Json.mkObj [("id", toJson (2 : Int))])).isNone
#guard isPushCall (Json.mkObj [("nodeType", .str "FunctionCall"),
  ("expression", Json.mkObj [("nodeType", .str "MemberAccess"), ("memberName", .str "push"),
    ("referencedDeclaration", toJson (-1 : Int))])])
#guard !isPushCall (Json.mkObj [("nodeType", .str "FunctionCall"),
  ("expression", Json.mkObj [("nodeType", .str "MemberAccess"), ("memberName", .str "push"),
    ("referencedDeclaration", toJson (1 : Int))])])

end Solidity.Examples.FrontendValidation.SolcJson.BodyHelpers
