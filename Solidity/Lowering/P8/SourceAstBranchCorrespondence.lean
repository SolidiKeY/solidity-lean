import Solidity.Lowering.P8.SourceAstStatementCorrespondence

/-! Conditional and catch structural correspondence.
Regression purpose: retain conditional branches and catch signatures/bodies
through unchanged readers. Syntax correspondence is not Source typing,
execution, artifact provenance or admission. -/
namespace Solidity.Lowering.P8.SourceAstBranchCorrespondence
open Lean Solidity.Source
open SourceAstExpressionCorrespondence

theorem if_without_else_exact (fuel : Nat) (node rawCondition rawYes : Json)
    (condition : Syn .expr) (yes : Syn (.stmt .body))
    (kind : node.getObjValAs? String "nodeType" = .ok "IfStatement")
    (conditionField : node.getObjVal? "condition" = .ok rawCondition)
    (conditionValue : SourceAstExpressions.expression fuel rawCondition = .ok condition)
    (yesField : node.getObjVal? "trueBody" = .ok rawYes)
    (yesValue : SourceAstStatements.statement fuel rawYes = .ok yes)
    (noField : node.getObjVal? "falseBody" = .ok .null) :
    SourceAstStatements.statement (fuel + 1) node = .ok (.ifStmt condition yes .none) := by
  rw [SourceAstStatements.statement]
  simp only [kind, conditionField, conditionValue, yesField, yesValue, noField, ok_bind, pure_bind]
  rfl

theorem if_with_else_exact (fuel : Nat) (node rawCondition rawYes rawNo : Json)
    (condition : Syn .expr) (yes no : Syn (.stmt .body))
    (kind : node.getObjValAs? String "nodeType" = .ok "IfStatement")
    (conditionField : node.getObjVal? "condition" = .ok rawCondition)
    (conditionValue : SourceAstExpressions.expression fuel rawCondition = .ok condition)
    (yesField : node.getObjVal? "trueBody" = .ok rawYes)
    (yesValue : SourceAstStatements.statement fuel rawYes = .ok yes)
    (noField : node.getObjVal? "falseBody" = .ok rawNo)
    (notNull : rawNo ≠ .null)
    (noValue : SourceAstStatements.statement fuel rawNo = .ok no) :
    SourceAstStatements.statement (fuel + 1) node = .ok (.ifStmt condition yes (.some no)) := by
  cases rawNo
  case null => exact False.elim (notNull rfl)
  all_goals
    rw [SourceAstStatements.statement]
    simp only [kind, conditionField, conditionValue, yesField, yesValue, noField, noValue, ok_bind]
    rfl

theorem catch_plain_exact (fuel : Nat)
    (readBlock : Json → Except String (Syn (.block .body))) (node rawBody : Json)
    (body : Syn (.block .body))
    (kind : node.getObjValAs? String "nodeType" = .ok "TryCatchClause")
    (nameField : node.getObjValAs? String "errorName" = .ok "")
    (parameters : SourceAstStatements.clauseParameters fuel node = .ok [])
    (bodyField : node.getObjVal? "block" = .ok rawBody)
    (bodyValue : readBlock rawBody = .ok body) :
    SourceAstStatements.catchWith fuel readBlock node = .ok (.catchPlain body) := by
  unfold SourceAstStatements.catchWith
  simp only [kind, nameField, parameters, bodyField, bodyValue, ok_bind,
    beq_self_eq_true, ite_true, pure_bind]
  rfl

theorem catch_signature_exact (fuel : Nat)
    (readBlock : Json → Except String (Syn (.block .body))) (node rawBody : Json)
    (name : String) (head : Syn .param) (tail : List (Syn .param)) (body : Syn (.block .body))
    (kind : node.getObjValAs? String "nodeType" = .ok "TryCatchClause")
    (nameField : node.getObjValAs? String "errorName" = .ok name)
    (parameters : SourceAstStatements.clauseParameters fuel node = .ok (head :: tail))
    (bodyField : node.getObjVal? "block" = .ok rawBody)
    (bodyValue : readBlock rawBody = .ok body) :
    SourceAstStatements.catchWith fuel readBlock node = .ok
      (.catchSig (if name.isEmpty then none else some name) head (SourceAstParameters.syntaxList tail) body) := by
  unfold SourceAstStatements.catchWith
  simp only [kind, nameField, parameters, bodyField, bodyValue, ok_bind,
    beq_self_eq_true, ite_true, pure_bind]
  rfl

/-- info: 'Solidity.Lowering.P8.SourceAstBranchCorrespondence.if_without_else_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms if_without_else_exact
/-- info: 'Solidity.Lowering.P8.SourceAstBranchCorrespondence.if_with_else_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms if_with_else_exact
/-- info: 'Solidity.Lowering.P8.SourceAstBranchCorrespondence.catch_plain_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms catch_plain_exact
/-- info: 'Solidity.Lowering.P8.SourceAstBranchCorrespondence.catch_signature_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms catch_signature_exact
end Solidity.Lowering.P8.SourceAstBranchCorrespondence
