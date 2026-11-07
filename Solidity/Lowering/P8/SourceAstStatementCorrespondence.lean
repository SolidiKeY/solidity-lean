import Solidity.Lowering.P8.SourceAstTypeCorrespondence

/-! Structural statement correspondence through unchanged Source readers.
Regression purpose: retain block contents, expression/return values and local
name/type/location/initialization before resolution. Field/child-result premises
are syntax facts, not Source validity, artifact binding or execution evidence. -/
namespace Solidity.Lowering.P8.SourceAstStatementCorrespondence
open Lean Solidity.Source
open SourceAstExpressionCorrespondence

theorem block_statement_exact (fuel : Nat) (node : Json) (body : Syn (.block .body))
    (kind : node.getObjValAs? String "nodeType" = .ok "Block")
    (converted : SourceAstStatements.blockWith (SourceAstStatements.statement fuel) node = .ok body) :
    SourceAstStatements.statement (fuel + 1) node = .ok (.blockStmt body) := by
  rw [SourceAstStatements.statement]
  simp only [kind, converted, ok_bind]
  rfl

theorem expression_statement_exact (fuel : Nat) (node raw : Json) (value : Syn .expr)
    (kind : node.getObjValAs? String "nodeType" = .ok "ExpressionStatement")
    (field : node.getObjVal? "expression" = .ok raw)
    (converted : SourceAstExpressions.expression fuel raw = .ok value) :
    SourceAstStatements.statement (fuel + 1) node = .ok (.simpleStmt (.exprStmt value)) := by
  rw [SourceAstStatements.statement]
  simp only [kind, field, converted, ok_bind]
  rfl

theorem return_exact (fuel : Nat) (node raw : Json) (value : Syn (.opt .expr))
    (kind : node.getObjValAs? String "nodeType" = .ok "Return")
    (field : node.getObjVal? "expression" = .ok raw)
    (converted : SourceAstStatements.optionalExpression fuel raw = .ok value) :
    SourceAstStatements.statement (fuel + 1) node = .ok (.returnStmt value) := by
  rw [SourceAstStatements.statement]
  simp only [kind, field, converted, ok_bind]
  rfl

/-- A successfully converted single local keeps its complete declaration and initializer.
This does not turn the reader's unsupported tuple declarations into exclusions. -/
theorem local_exact (fuel : Nat) (node declaration rawType rawInit : Json)
    (ty : Syn .typeName) (location name : String) (loc : Option DataLoc)
    (initial : Syn (.opt .expr))
    (kind : node.getObjValAs? String "nodeType" = .ok "VariableDeclarationStatement")
    (declarations : node.getObjValAs? (Array Json) "declarations" = .ok #[declaration])
    (declarationKind : declaration.getObjValAs? String "nodeType" = .ok "VariableDeclaration")
    (typeField : declaration.getObjVal? "typeName" = .ok rawType)
    (typeValue : SourceAstCompoundTypes.typeName fuel rawType = .ok ty)
    (locationField : declaration.getObjValAs? String "storageLocation" = .ok location)
    (locationValue : SourceAstTypes.location location = .ok loc)
    (nameField : declaration.getObjValAs? String "name" = .ok name)
    (initialField : node.getObjVal? "initialValue" = .ok rawInit)
    (initialValue : SourceAstStatements.optionalExpression fuel rawInit = .ok initial) :
    SourceAstStatements.statement (fuel + 1) node =
      .ok (.simpleStmt (.declVar (.varDecl ty loc name) initial)) := by
  rw [SourceAstStatements.statement]
  simp only [kind, declarations, declarationKind, typeField, typeValue, locationField,
    locationValue, nameField, initialField, initialValue, ok_bind, beq_self_eq_true,
    ite_true, pure_bind]
  rfl

/-- info: 'Solidity.Lowering.P8.SourceAstStatementCorrespondence.block_statement_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms block_statement_exact
/-- info: 'Solidity.Lowering.P8.SourceAstStatementCorrespondence.expression_statement_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms expression_statement_exact
/-- info: 'Solidity.Lowering.P8.SourceAstStatementCorrespondence.return_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms return_exact
/-- info: 'Solidity.Lowering.P8.SourceAstStatementCorrespondence.local_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms local_exact
end Solidity.Lowering.P8.SourceAstStatementCorrespondence
