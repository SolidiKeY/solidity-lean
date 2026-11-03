import Solidity.Frontend.SolcJson.YulStatementTags
/-! Concrete successful decoder inversion for nested control components.
No caller-supplied decoder/alignment law is an input. -/
namespace Solidity.Frontend.YulJson.ControlFields
open Lean (Json)

theorem if_fields (fuel : Nat) {node condition body}
    (parsed : statementAux fuel node = .ok (.yulIf condition body)) :
    ∃ childFuel, fuel = childFuel+1 ∧
      string node "nodeType" = .ok "YulIf" ∧
      ∃ conditionNode bodyNode,
        field node "condition" = .ok conditionNode ∧
        expressionAux childFuel conditionNode = .ok condition ∧
        field node "body" = .ok bodyNode ∧
        blockAux childFuel bodyNode = .ok body := by
  have kind := StatementTags.kind_of_tag fuel parsed (wanted := "YulIf") rfl
  cases fuel with
  | zero => cases parsed
  | succ fuel =>
      rw [statementAux] at parsed
      simp only [kind,bind,Except.bind] at parsed
      simp only [
        show ("YulIf" = "YulBlock") = False from propext (by decide +kernel),
        show ("YulIf" = "YulVariableDeclaration") = False from propext (by decide +kernel),
        show ("YulIf" = "YulAssignment") = False from propext (by decide +kernel),
        show ("YulIf" = "YulExpressionStatement") = False from propext (by decide +kernel),
        if_false,if_true] at parsed
      cases conditionEq : field node "condition" with
      | error reason =>
          simp only [conditionEq] at parsed
          cases parsed
      | ok conditionNode =>
          simp only [conditionEq] at parsed
          cases expressionEq : expressionAux fuel conditionNode with
          | error reason =>
              simp only [expressionEq] at parsed
              cases parsed
          | ok actualCondition =>
              simp only [expressionEq] at parsed
              cases bodyNodeEq : field node "body" with
              | error reason =>
                  simp only [bodyNodeEq] at parsed
                  cases parsed
              | ok bodyNode =>
                  simp only [bodyNodeEq] at parsed
                  cases bodyEq : blockAux fuel bodyNode with
                  | error reason =>
                      simp only [bodyEq] at parsed
                      cases parsed
                  | ok actualBody =>
                      simp only [bodyEq,pure,Except.pure] at parsed
                      cases parsed
                      exact ⟨fuel,rfl,kind,conditionNode,bodyNode,rfl,expressionEq,rfl,bodyEq⟩

theorem block_fields (fuel : Nat) {node body}
    (parsed : statementAux fuel node = .ok (.yulBlock body)) :
    ∃ childFuel, fuel = childFuel+1 ∧
      string node "nodeType" = .ok "YulBlock" ∧ blockAux childFuel node = .ok body := by
  have kind := StatementTags.kind_of_tag fuel parsed (wanted := "YulBlock") rfl
  cases fuel with
  | zero => cases parsed
  | succ fuel =>
      rw [statementAux] at parsed
      simp only [kind,bind,Except.bind,if_true] at parsed
      cases bodyEq : blockAux fuel node with
      | error reason =>
          simp only [bodyEq] at parsed
          cases parsed
      | ok actualBody =>
          simp only [bodyEq,pure,Except.pure] at parsed
          cases parsed
          exact ⟨fuel,rfl,kind,bodyEq⟩

theorem expression_fields (fuel : Nat) {node expression}
    (parsed : statementAux fuel node = .ok (.yulExprStmt expression)) :
    ∃ childFuel, fuel = childFuel+1 ∧
      string node "nodeType" = .ok "YulExpressionStatement" ∧
      ∃ expressionNode,
        field node "expression" = .ok expressionNode ∧
        expressionAux childFuel expressionNode = .ok expression := by
  have kind := StatementTags.kind_of_tag fuel parsed (wanted := "YulExpressionStatement") rfl
  cases fuel with
  | zero => cases parsed
  | succ fuel =>
      rw [statementAux] at parsed
      simp only [kind,bind,Except.bind] at parsed
      simp only [
        show ("YulExpressionStatement" = "YulBlock") = False from propext (by decide +kernel),
        show ("YulExpressionStatement" = "YulVariableDeclaration") = False from propext (by decide +kernel),
        show ("YulExpressionStatement" = "YulAssignment") = False from propext (by decide +kernel),
        if_false,if_true] at parsed
      cases expressionNodeEq : field node "expression" with
      | error reason =>
          simp only [expressionNodeEq] at parsed
          cases parsed
      | ok expressionNode =>
          simp only [expressionNodeEq] at parsed
          cases expressionEq : expressionAux fuel expressionNode with
          | error reason =>
              simp only [expressionEq] at parsed
              cases parsed
          | ok actualExpression =>
              simp only [expressionEq] at parsed
              simp only [pure,Except.pure] at parsed
              cases parsed
              exact ⟨fuel,rfl,kind,expressionNode,rfl,expressionEq⟩

theorem for_fields (fuel : Nat) {node pre condition post body}
    (parsed : statementAux fuel node = .ok (.yulFor pre condition post body)) :
    ∃ childFuel, fuel = childFuel+1 ∧
      string node "nodeType" = .ok "YulForLoop" ∧
      ∃ preNode conditionNode postNode bodyNode,
        field node "pre" = .ok preNode ∧
        blockAux childFuel preNode = .ok pre ∧
        field node "condition" = .ok conditionNode ∧
        expressionAux childFuel conditionNode = .ok condition ∧
        field node "post" = .ok postNode ∧
        blockAux childFuel postNode = .ok post ∧
        field node "body" = .ok bodyNode ∧
        blockAux childFuel bodyNode = .ok body := by
  have kind := StatementTags.kind_of_tag fuel parsed (wanted := "YulForLoop") rfl
  cases fuel with
  | zero => cases parsed
  | succ fuel =>
      rw [statementAux] at parsed
      simp only [kind,bind,Except.bind] at parsed
      simp only [
        show ("YulForLoop" = "YulBlock") = False from propext (by decide +kernel),
        show ("YulForLoop" = "YulVariableDeclaration") = False from propext (by decide +kernel),
        show ("YulForLoop" = "YulAssignment") = False from propext (by decide +kernel),
        show ("YulForLoop" = "YulExpressionStatement") = False from propext (by decide +kernel),
        show ("YulForLoop" = "YulIf") = False from propext (by decide +kernel),
        if_false,if_true] at parsed
      cases preNodeEq : field node "pre" with
      | error reason =>
          simp only [preNodeEq] at parsed
          cases parsed
      | ok preNode =>
          simp only [preNodeEq] at parsed
          cases preEq : blockAux fuel preNode with
          | error reason =>
              simp only [preEq] at parsed
              cases parsed
          | ok actualPre =>
              simp only [preEq] at parsed
              cases conditionNodeEq : field node "condition" with
              | error reason =>
                  simp only [conditionNodeEq] at parsed
                  cases parsed
              | ok conditionNode =>
                  simp only [conditionNodeEq] at parsed
                  cases conditionEq : expressionAux fuel conditionNode with
                  | error reason =>
                      simp only [conditionEq] at parsed
                      cases parsed
                  | ok actualCondition =>
                      simp only [conditionEq] at parsed
                      cases postNodeEq : field node "post" with
                      | error reason =>
                          simp only [postNodeEq] at parsed
                          cases parsed
                      | ok postNode =>
                          simp only [postNodeEq] at parsed
                          cases postEq : blockAux fuel postNode with
                          | error reason =>
                              simp only [postEq] at parsed
                              cases parsed
                          | ok actualPost =>
                              simp only [postEq] at parsed
                              cases bodyNodeEq : field node "body" with
                              | error reason =>
                                  simp only [bodyNodeEq] at parsed
                                  cases parsed
                              | ok bodyNode =>
                                  simp only [bodyNodeEq] at parsed
                                  cases bodyEq : blockAux fuel bodyNode with
                                  | error reason =>
                                      simp only [bodyEq] at parsed
                                      cases parsed
                                  | ok actualBody =>
                                      simp only [bodyEq] at parsed
                                      simp only [pure,Except.pure] at parsed
                                      cases parsed
                                      exact ⟨fuel,rfl,kind,preNode,conditionNode,postNode,bodyNode,rfl,preEq,rfl,conditionEq,rfl,postEq,rfl,bodyEq⟩

theorem function_fields (fuel : Nat) {node name args rets body}
    (parsed : statementAux fuel node = .ok (.yulFun name args rets body)) :
    ∃ childFuel, fuel = childFuel+1 ∧
      string node "nodeType" = .ok "YulFunctionDefinition" ∧
      string node "name" = .ok name ∧
      optionalNames node "parameters" = .ok args ∧
      optionalNames node "returnVariables" = .ok rets ∧
      ∃ bodyNode, field node "body" = .ok bodyNode ∧
        blockAux childFuel bodyNode = .ok body := by
  have kind := StatementTags.kind_of_tag fuel parsed (wanted := "YulFunctionDefinition") rfl
  cases fuel with
  | zero => cases parsed
  | succ fuel =>
      rw [statementAux] at parsed
      simp only [kind,bind,Except.bind] at parsed
      simp only [
        show ("YulFunctionDefinition" = "YulBlock") = False from propext (by decide +kernel),
        show ("YulFunctionDefinition" = "YulVariableDeclaration") = False from propext (by decide +kernel),
        show ("YulFunctionDefinition" = "YulAssignment") = False from propext (by decide +kernel),
        show ("YulFunctionDefinition" = "YulExpressionStatement") = False from propext (by decide +kernel),
        show ("YulFunctionDefinition" = "YulIf") = False from propext (by decide +kernel),
        show ("YulFunctionDefinition" = "YulForLoop") = False from propext (by decide +kernel),
        show ("YulFunctionDefinition" = "YulSwitch") = False from propext (by decide +kernel),
        if_false,if_true] at parsed
      cases nameEq : string node "name" with
      | error reason =>
          simp only [nameEq] at parsed
          cases parsed
      | ok actualName =>
          simp only [nameEq] at parsed
          split at parsed
          · split at parsed
            · cases parsed
            · simp only [pure,Except.pure] at parsed
              cases argsEq : optionalNames node "parameters" with
              | error reason =>
                  simp only [argsEq] at parsed
                  cases parsed
              | ok actualArgs =>
                  simp only [argsEq] at parsed
                  cases retsEq : optionalNames node "returnVariables" with
                  | error reason =>
                      simp only [retsEq] at parsed
                      cases parsed
                  | ok actualRets =>
                      simp only [retsEq] at parsed
                      cases bodyNodeEq : field node "body" with
                      | error reason =>
                          simp only [bodyNodeEq] at parsed
                          cases parsed
                      | ok bodyNode =>
                          simp only [bodyNodeEq] at parsed
                          cases bodyEq : blockAux fuel bodyNode with
                          | error reason =>
                              simp only [bodyEq] at parsed
                              cases parsed
                          | ok actualBody =>
                              simp only [bodyEq] at parsed
                              cases parsed
                              exact ⟨fuel,rfl,kind,rfl,rfl,rfl,bodyNode,rfl,bodyEq⟩
          · cases parsed

/-- Actual switch decoder fields, including the nonempty raw case array and
the unchanged real case decoder. Default elision is not reconstructed here. -/
theorem switch_fields (fuel : Nat) {node selector cases fallback}
    (parsed : statementAux fuel node = .ok (.yulSwitch selector cases fallback)) :
    ∃ childFuel, fuel = childFuel+1 ∧
      string node "nodeType" = .ok "YulSwitch" ∧
      ∃ selectorNode values,
        field node "expression" = .ok selectorNode ∧
        expressionAux childFuel selectorNode = .ok selector ∧
        array node "cases" = .ok values ∧ values.isEmpty = false ∧
        switchCases (blockAux childFuel) values.toList [] = .ok (cases,fallback) := by
  have kind := StatementTags.kind_of_tag fuel parsed (wanted := "YulSwitch") rfl
  cases fuel with
  | zero => cases parsed
  | succ fuel =>
      rw [statementAux] at parsed
      simp only [kind,bind,Except.bind] at parsed
      simp only [
        show ("YulSwitch" = "YulBlock") = False from propext (by decide +kernel),
        show ("YulSwitch" = "YulVariableDeclaration") = False from propext (by decide +kernel),
        show ("YulSwitch" = "YulAssignment") = False from propext (by decide +kernel),
        show ("YulSwitch" = "YulExpressionStatement") = False from propext (by decide +kernel),
        show ("YulSwitch" = "YulIf") = False from propext (by decide +kernel),
        show ("YulSwitch" = "YulForLoop") = False from propext (by decide +kernel),
        if_false,if_true] at parsed
      cases selectorEq : field node "expression" with
      | error reason =>
          simp only [selectorEq] at parsed
          cases parsed
      | ok selectorNode =>
          simp only [selectorEq] at parsed
          cases expressionEq : expressionAux fuel selectorNode with
          | error reason =>
              simp only [expressionEq] at parsed
              cases parsed
          | ok actualSelector =>
              simp only [expressionEq] at parsed
              cases valuesEq : array node "cases" with
              | error reason =>
                  simp only [valuesEq] at parsed
                  cases parsed
              | ok values =>
                  simp only [valuesEq] at parsed
                  cases emptyEq : values.isEmpty with
                  | true =>
                      simp only [emptyEq,if_true] at parsed
                      cases parsed
                  | false =>
                      simp only [emptyEq,Bool.false_eq_true,if_false] at parsed
                      cases casesEq : switchCases (blockAux fuel) values.toList [] with
                      | error reason =>
                          simp only [casesEq] at parsed
                          cases parsed
                      | ok pair =>
                          rcases pair with ⟨actualCases,actualFallback⟩
                          simp only [casesEq,pure,Except.pure] at parsed
                          cases parsed
                          exact ⟨fuel,rfl,kind,selectorNode,values,rfl,expressionEq,rfl,emptyEq,casesEq⟩

/-- A successful raw default entry is necessarily last. Its body is decoded
by the actual child block decoder; no callback agreement law is assumed. -/
theorem default_fields (fuel : Nat) {node rest seen cases fallback}
    (valueEq : field node "value" = .ok (.str "default"))
    (parsed : switchCases (blockAux fuel) (node::rest) seen = .ok (cases,fallback)) :
    rest = [] ∧ requireNode node "YulCase" = .ok () ∧
      ∃ bodyNode body,
        field node "body" = .ok bodyNode ∧ blockAux fuel bodyNode = .ok body ∧
        cases = .nil ∧ fallback = .some body := by
  rw [switchCases] at parsed
  cases kindEq : requireNode node "YulCase" with
  | error reason =>
      simp only [kindEq,bind,Except.bind] at parsed
      cases parsed
  | ok result =>
      cases result
      simp only [kindEq,bind,Except.bind,valueEq] at parsed
      cases rest with
      | cons first tail =>
          simp only [List.isEmpty_cons,Bool.not_false,if_true] at parsed
          cases parsed
      | nil =>
          simp only [List.isEmpty_nil,Bool.not_true,Bool.false_eq_true,if_false] at parsed
          cases bodyNodeEq : field node "body" with
          | error reason =>
              simp only [bodyNodeEq] at parsed
              cases parsed
          | ok bodyNode =>
              simp only [bodyNodeEq] at parsed
              cases bodyEq : blockAux fuel bodyNode with
              | error reason =>
                  simp only [bodyEq] at parsed
                  cases parsed
              | ok body =>
                  simp only [bodyEq,pure,Except.pure] at parsed
                  cases parsed
                  exact ⟨rfl,rfl,bodyNode,body,rfl,bodyEq,rfl,rfl⟩

/-- Real ordinary-case inversion for a supplied non-default value. This
preserves the decoder's accumulated word set and recursive residual result. -/
theorem case_fields (fuel : Nat) {node rest seen value cases fallback}
    (valueEq : field node "value" = .ok value)
    (ordinary : value ≠ .str "default")
    (parsed : switchCases (blockAux fuel) (node::rest) seen = .ok (cases,fallback)) :
    requireNode node "YulCase" = .ok () ∧
      ∃ decoded : Literal, ∃ bodyNode body remaining,
        literal value = .ok decoded ∧ seen.contains decoded.value = false ∧
        field node "body" = .ok bodyNode ∧ blockAux fuel bodyNode = .ok body ∧
        switchCases (blockAux fuel) rest (decoded.value::seen) = .ok (remaining,fallback) ∧
        cases = .cons (.yulCase decoded.tree body) remaining := by
  rw [switchCases] at parsed
  cases kindEq : requireNode node "YulCase" with
  | error reason =>
      simp only [kindEq,bind,Except.bind] at parsed
      cases parsed
  | ok result =>
      cases result
      simp only [kindEq,bind,Except.bind,valueEq] at parsed
      cases literalEq : literal value with
      | error reason =>
          simp only [literalEq] at parsed
          cases parsed
      | ok decoded =>
          simp only [literalEq] at parsed
          cases duplicateEq : seen.contains decoded.value with
          | true =>
              simp only [duplicateEq,if_true] at parsed
              cases parsed
          | false =>
              simp only [duplicateEq,Bool.false_eq_true,if_false,pure,Except.pure] at parsed
              cases bodyNodeEq : field node "body" with
              | error reason =>
                  simp only [bodyNodeEq] at parsed
                  cases parsed
              | ok bodyNode =>
                  simp only [bodyNodeEq] at parsed
                  cases bodyEq : blockAux fuel bodyNode with
                  | error reason =>
                      simp only [bodyEq] at parsed
                      cases parsed
                  | ok body =>
                      simp only [bodyEq] at parsed
                      cases restEq : switchCases (blockAux fuel) rest (decoded.value::seen) with
                      | error reason =>
                          simp only [restEq] at parsed
                          cases parsed
                      | ok pair =>
                          rcases pair with ⟨remaining,actualFallback⟩
                          simp only [restEq] at parsed
                          cases parsed
                          exact ⟨rfl,decoded,bodyNode,body,remaining,rfl,duplicateEq,rfl,bodyEq,restEq,rfl⟩


/-- Any successful nonempty case decoder actually read its head value. -/
theorem case_value (fuel : Nat) {node rest seen cases fallback}
    (parsed : switchCases (blockAux fuel) (node::rest) seen = .ok (cases,fallback)) :
    requireNode node "YulCase" = .ok () ∧ ∃ value, field node "value" = .ok value := by
  rw [switchCases] at parsed
  cases kindEq : requireNode node "YulCase" with
  | error reason =>
      simp only [kindEq,bind,Except.bind] at parsed
      cases parsed
  | ok result =>
      cases result
      simp only [kindEq,bind,Except.bind] at parsed
      cases valueEq : field node "value" with
      | error reason =>
          simp only [valueEq] at parsed
          cases parsed
      | ok value => exact ⟨rfl,value,rfl⟩

/-- A successful nonempty SOURCE case result necessarily came from an
ordinary raw head. This discharges the non-default premise from real decoding. -/
theorem cons_fields (fuel : Nat) {node rest seen first remaining fallback}
    (parsed : switchCases (blockAux fuel) (node::rest) seen = .ok (.cons first remaining,fallback)) :
    ∃ value, field node "value" = .ok value ∧ value ≠ .str "default" ∧
      ∃ decoded : Literal, ∃ bodyNode body,
        requireNode node "YulCase" = .ok () ∧ literal value = .ok decoded ∧
        seen.contains decoded.value = false ∧ field node "body" = .ok bodyNode ∧
        blockAux fuel bodyNode = .ok body ∧
        switchCases (blockAux fuel) rest (decoded.value::seen) = .ok (remaining,fallback) ∧
        first = .yulCase decoded.tree body := by
  obtain ⟨_,value,valueEq⟩ := case_value fuel parsed
  have ordinary : value ≠ .str "default" := by
    intro same
    cases same
    obtain ⟨_,_,_,_,_,_,impossible,_⟩ := default_fields fuel valueEq parsed
    cases impossible
  obtain ⟨kind,decoded,bodyNode,body,actualRemaining,literalEq,notSeen,
    fieldEq,bodyEq,restEq,same⟩ := case_fields fuel valueEq ordinary parsed
  cases same
  exact ⟨value,valueEq,ordinary,decoded,bodyNode,body,kind,literalEq,
    notSeen,fieldEq,bodyEq,restEq,rfl⟩

/-- Forward companion to switch_fields. Every actual decoder field and
child equation is explicit; consumers must discharge them concretely. -/
theorem switch_decode (fuel : Nat) {node selectorNode values selector cases fallback}
    (kind : string node "nodeType" = .ok "YulSwitch")
    (selectorField : field node "expression" = .ok selectorNode)
    (selectorDecoded : expressionAux fuel selectorNode = .ok selector)
    (casesField : array node "cases" = .ok values)
    (nonempty : values.isEmpty = false)
    (casesDecoded : switchCases (blockAux fuel) values.toList [] = .ok (cases,fallback)) :
    statementAux (fuel+1) node = .ok (.yulSwitch selector cases fallback) := by
  rw [statementAux]
  simp only [kind,bind,Except.bind]
  simp only [
    show ("YulSwitch" = "YulBlock") = False from propext (by decide +kernel),
    show ("YulSwitch" = "YulVariableDeclaration") = False from propext (by decide +kernel),
    show ("YulSwitch" = "YulAssignment") = False from propext (by decide +kernel),
    show ("YulSwitch" = "YulExpressionStatement") = False from propext (by decide +kernel),
    show ("YulSwitch" = "YulIf") = False from propext (by decide +kernel),
    show ("YulSwitch" = "YulForLoop") = False from propext (by decide +kernel),
    if_false,if_true]
  simp only [selectorField,selectorDecoded,casesField,nonempty,
    Bool.false_eq_true,if_false,casesDecoded,pure,Except.pure]

end Solidity.Frontend.YulJson.ControlFields
