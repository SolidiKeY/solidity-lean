import Solidity.Frontend.SolcJson.YulDeclarationFields
import Solidity.Frontend.SolcJson.YulTypedChildren
/-! Actual declaration initializer positions under the original PRE-extension
environment. Parent equality preserves the original extension and certificate.
No execution/zero-writeback or recursive global path theorem is asserted. -/
namespace Solidity.Frontend.YulJson.DeclarationChildren
open Lean (Json)
open Solidity.Yul
open Solidity.Yul.ScopedBlockTyping

theorem some_positions {X scope F n E c first rest expression} (fuel : Nat) {node}
    (parsed : statementAux fuel node = .ok (.yulLet first rest (.some expression)))
    (typed : @StatementD X scope F n E c (.yulLet first rest (.some expression))
      ((first::rest).length+n) (E.extend (first::rest))) :
    ∃ childFuel valueNode,
    ∃ initializer : BlockScope.ExpressionD scope E expression (first::rest).length,
      fuel = childFuel+1 ∧ names node "variables" = .ok (first::rest) ∧
      field node "value" = .ok valueNode ∧ expressionAux childFuel valueNode = .ok expression ∧
      typed = .declaration (.value initializer) ∧
      (TypingLeaves.expressionInput scope E initializer).1 = (first::rest).length ∧
      TypedChildren.Reads valueNode initializer := by
  cases typed with
  | declaration initializer =>
      cases initializer with
      | value expressionTyped =>
          obtain ⟨childFuel,valueNode,horizon,_,namesEq,fieldEq,decoded⟩ :=
            DeclarationFields.some_fields fuel parsed
          exact ⟨childFuel,valueNode,expressionTyped,horizon,namesEq,fieldEq,decoded,rfl,
            TypingLeaves.expressionInput_count _ _ expressionTyped,
            TypedChildren.decoded_reads childFuel decoded expressionTyped⟩

theorem none_positions {X scope F n E c first rest} (fuel : Nat) {node}
    (parsed : statementAux fuel node = .ok (.yulLet first rest .none))
    (typed : @StatementD X scope F n E c (.yulLet first rest .none)
      ((first::rest).length+n) (E.extend (first::rest))) :
    ∃ childFuel, fuel = childFuel+1 ∧ names node "variables" = .ok (first::rest) ∧
      ((∃ reason : String, node.getObjVal? "value" = .error reason) ∨
        field node "value" = .ok .null) ∧
      typed = .declaration .zero ∧
      TypingSites.initializer
        (InitializerD.zero : InitializerD scope E (first::rest).length .none) [] = [] := by
  cases typed with
  | declaration initializer =>
      cases initializer with
      | zero =>
          obtain ⟨childFuel,horizon,_,namesEq,absent⟩ := DeclarationFields.none_fields fuel parsed
          exact ⟨childFuel,horizon,namesEq,absent,rfl,rfl⟩

end Solidity.Frontend.YulJson.DeclarationChildren
