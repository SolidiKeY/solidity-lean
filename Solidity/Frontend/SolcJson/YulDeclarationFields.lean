import Solidity.Frontend.SolcJson.YulStatementTags
/-! Actual declaration decoder fields; missing/null initializers are distinct
from a successfully decoded expression. These are decoder facts only. -/
namespace Solidity.Frontend.YulJson.DeclarationFields
open Lean (Json)
open Solidity.Source (Syn)

theorem some_fields (fuel : Nat) {node first rest expression}
    (parsed : statementAux fuel node = .ok (.yulLet first rest (.some expression))) :
    ∃ childFuel valueNode, fuel = childFuel+1 ∧
      string node "nodeType" = .ok "YulVariableDeclaration" ∧
      names node "variables" = .ok (first::rest) ∧
      field node "value" = .ok valueNode ∧ expressionAux childFuel valueNode = .ok expression := by
  have kind := StatementTags.kind_of_tag fuel parsed (wanted := "YulVariableDeclaration") rfl
  cases fuel with
  | zero => cases parsed
  | succ fuel =>
      rw [statementAux] at parsed
      simp only [kind,bind,Except.bind] at parsed
      simp only [
        show ("YulVariableDeclaration" = "YulBlock") = False from propext (by decide +kernel),
        if_false,if_true] at parsed
      cases namesEq : names node "variables" with
      | error reason =>
          simp only [namesEq] at parsed
          cases parsed
      | ok variables =>
          simp only [namesEq] at parsed
          cases valueEq : node.getObjVal? "value" with
          | error reason =>
              simp only [valueEq,pure,Except.pure] at parsed
              cases variables <;> cases parsed
          | ok valueNode =>
              cases valueNode with
              | null =>
                  simp only [valueEq,pure,Except.pure] at parsed
                  cases variables <;> cases parsed
              | bool flag =>
                  simp only [valueEq] at parsed
                  cases expressionEq : expressionAux fuel (Json.bool flag) with
                  | error reason =>
                      simp only [expressionEq] at parsed
                      cases parsed
                  | ok actualExpression =>
                      simp only [expressionEq,pure,Except.pure] at parsed
                      cases variables with
                      | nil => cases parsed
                      | cons actualFirst actualRest =>
                          cases parsed
                          refine ⟨fuel,Json.bool flag,rfl,kind,rfl,?_,expressionEq⟩
                          simp only [field,valueEq,Except.mapError]
              | num number =>
                  simp only [valueEq] at parsed
                  cases expressionEq : expressionAux fuel (Json.num number) with
                  | error reason =>
                      simp only [expressionEq] at parsed
                      cases parsed
                  | ok actualExpression =>
                      simp only [expressionEq,pure,Except.pure] at parsed
                      cases variables with
                      | nil => cases parsed
                      | cons actualFirst actualRest =>
                          cases parsed
                          refine ⟨fuel,Json.num number,rfl,kind,rfl,?_,expressionEq⟩
                          simp only [field,valueEq,Except.mapError]
              | str text =>
                  simp only [valueEq] at parsed
                  cases expressionEq : expressionAux fuel (Json.str text) with
                  | error reason =>
                      simp only [expressionEq] at parsed
                      cases parsed
                  | ok actualExpression =>
                      simp only [expressionEq,pure,Except.pure] at parsed
                      cases variables with
                      | nil => cases parsed
                      | cons actualFirst actualRest =>
                          cases parsed
                          refine ⟨fuel,Json.str text,rfl,kind,rfl,?_,expressionEq⟩
                          simp only [field,valueEq,Except.mapError]
              | arr values =>
                  simp only [valueEq] at parsed
                  cases expressionEq : expressionAux fuel (Json.arr values) with
                  | error reason =>
                      simp only [expressionEq] at parsed
                      cases parsed
                  | ok actualExpression =>
                      simp only [expressionEq,pure,Except.pure] at parsed
                      cases variables with
                      | nil => cases parsed
                      | cons actualFirst actualRest =>
                          cases parsed
                          refine ⟨fuel,Json.arr values,rfl,kind,rfl,?_,expressionEq⟩
                          simp only [field,valueEq,Except.mapError]
              | obj fields =>
                  simp only [valueEq] at parsed
                  cases expressionEq : expressionAux fuel (Json.obj fields) with
                  | error reason =>
                      simp only [expressionEq] at parsed
                      cases parsed
                  | ok actualExpression =>
                      simp only [expressionEq,pure,Except.pure] at parsed
                      cases variables with
                      | nil => cases parsed
                      | cons actualFirst actualRest =>
                          cases parsed
                          refine ⟨fuel,Json.obj fields,rfl,kind,rfl,?_,expressionEq⟩
                          simp only [field,valueEq,Except.mapError]

theorem none_fields (fuel : Nat) {node first rest}
    (parsed : statementAux fuel node = .ok (.yulLet first rest .none)) :
    ∃ childFuel, fuel = childFuel+1 ∧
      string node "nodeType" = .ok "YulVariableDeclaration" ∧
      names node "variables" = .ok (first::rest) ∧
      ((∃ reason : String, node.getObjVal? "value" = .error reason) ∨
        field node "value" = .ok .null) := by
  have kind := StatementTags.kind_of_tag fuel parsed (wanted := "YulVariableDeclaration") rfl
  cases fuel with
  | zero => cases parsed
  | succ fuel =>
      rw [statementAux] at parsed
      simp only [kind,bind,Except.bind] at parsed
      simp only [
        show ("YulVariableDeclaration" = "YulBlock") = False from propext (by decide +kernel),
        if_false,if_true] at parsed
      cases namesEq : names node "variables" with
      | error reason =>
          simp only [namesEq] at parsed
          cases parsed
      | ok variables =>
          simp only [namesEq] at parsed
          cases valueEq : node.getObjVal? "value" with
          | error reason =>
              simp only [valueEq,pure,Except.pure] at parsed
              cases variables with
              | nil => cases parsed
              | cons actualFirst actualRest =>
                  cases parsed
                  exact ⟨fuel,rfl,kind,rfl,.inl ⟨reason,rfl⟩⟩
          | ok valueNode =>
              cases valueNode with
              | null =>
                  simp only [valueEq,pure,Except.pure] at parsed
                  cases variables with
                  | nil => cases parsed
                  | cons actualFirst actualRest =>
                      cases parsed
                      refine ⟨fuel,rfl,kind,rfl,.inr ?_⟩
                      simp only [field,valueEq,Except.mapError]
              | bool flag =>
                  simp only [valueEq] at parsed
                  cases expressionEq : expressionAux fuel (Json.bool flag) with
                  | error reason =>
                      simp only [expressionEq] at parsed
                      cases parsed
                  | ok actualExpression =>
                      simp only [expressionEq,pure,Except.pure] at parsed
                      cases variables <;> cases parsed
              | num number =>
                  simp only [valueEq] at parsed
                  cases expressionEq : expressionAux fuel (Json.num number) with
                  | error reason =>
                      simp only [expressionEq] at parsed
                      cases parsed
                  | ok actualExpression =>
                      simp only [expressionEq,pure,Except.pure] at parsed
                      cases variables <;> cases parsed
              | str text =>
                  simp only [valueEq] at parsed
                  cases expressionEq : expressionAux fuel (Json.str text) with
                  | error reason =>
                      simp only [expressionEq] at parsed
                      cases parsed
                  | ok actualExpression =>
                      simp only [expressionEq,pure,Except.pure] at parsed
                      cases variables <;> cases parsed
              | arr values =>
                  simp only [valueEq] at parsed
                  cases expressionEq : expressionAux fuel (Json.arr values) with
                  | error reason =>
                      simp only [expressionEq] at parsed
                      cases parsed
                  | ok actualExpression =>
                      simp only [expressionEq,pure,Except.pure] at parsed
                      cases variables <;> cases parsed
              | obj fields =>
                  simp only [valueEq] at parsed
                  cases expressionEq : expressionAux fuel (Json.obj fields) with
                  | error reason =>
                      simp only [expressionEq] at parsed
                      cases parsed
                  | ok actualExpression =>
                      simp only [expressionEq,pure,Except.pure] at parsed
                      cases variables <;> cases parsed

end Solidity.Frontend.YulJson.DeclarationFields
