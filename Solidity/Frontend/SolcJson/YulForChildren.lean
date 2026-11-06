import Solidity.Frontend.SolcJson.YulTypedChildren
import Solidity.Frontend.SolcJson.YulWalkPath
/-! Actual initializer-walk and for child contexts, preserving every original
subcertificate. Positions are child-local, not recursive global prefixes. -/
namespace Solidity.Frontend.YulJson.ForChildren
open Lean (Json)
open Solidity.Yul
open Solidity.Yul.BlockTyping (Env)
open Solidity.Yul.ScopedBlockTyping

abbrev Walks {X scope F n E c body m final} (fuel : Nat) (node : Json)
    (typed : @WalkD X scope F n E c body m final) : Prop :=
  TypingStatements.All (fun ordinal item => Nonempty (BlockPath.Witness fuel node (ordinal,item)))
    (TypingStatements.walk typed 0)

theorem for_positions {X scope F n E c pre condition post body} (fuel : Nat) {node}
    (parsed : statementAux fuel node = .ok (.yulFor pre condition post body))
    (typed : @StatementD X scope F n E c (.yulFor pre condition post body) n E) :
    ∃ childFuel preNode conditionNode postNode bodyNode initSlots,
    ∃ initFinal : Env F initSlots,
    ∃ headers : HeadersD pre [],
    ∃ initializer : WalkD scope E ⟨c.function,false⟩ pre initFinal,
    ∃ guard : BlockScope.ExpressionD scope initFinal condition 1,
    ∃ postTyped : BlockD scope initFinal ⟨c.function,false⟩ post,
    ∃ bodyTyped : BlockD scope initFinal ⟨c.function,true⟩ body,
      fuel = childFuel+1 ∧
      field node "pre" = .ok preNode ∧ blockAux childFuel preNode = .ok pre ∧
      field node "condition" = .ok conditionNode ∧
      expressionAux childFuel conditionNode = .ok condition ∧
      field node "post" = .ok postNode ∧ blockAux childFuel postNode = .ok post ∧
      field node "body" = .ok bodyNode ∧ blockAux childFuel bodyNode = .ok body ∧
      typed = .for_ headers initializer guard postTyped bodyTyped ∧
      (TypingLeaves.expressionInput scope initFinal guard).1 = 1 ∧
      Walks childFuel preNode initializer ∧ TypedChildren.Reads conditionNode guard ∧
      TypedChildren.Blocks childFuel postNode postTyped ∧
      TypedChildren.Blocks childFuel bodyNode bodyTyped := by
  cases typed with
  | for_ headers initializer guard postTyped bodyTyped =>
      obtain ⟨childFuel,horizon,_,preNode,conditionNode,postNode,bodyNode,
        preEq,preDecoded,conditionEq,conditionDecoded,postEq,postDecoded,bodyEq,bodyDecoded⟩ :=
        ControlFields.for_fields fuel parsed
      refine ⟨childFuel,preNode,conditionNode,postNode,bodyNode,_,_,
        headers,initializer,guard,postTyped,bodyTyped,horizon,
        preEq,preDecoded,conditionEq,conditionDecoded,postEq,postDecoded,bodyEq,bodyDecoded,
        rfl,TypingLeaves.expressionInput_count _ _ guard,?_,?_,?_,?_⟩
      · exact WalkPath.decoded_walk childFuel preDecoded initializer
      · exact TypedChildren.decoded_reads childFuel conditionDecoded guard
      · exact BlockPath.decoded_block childFuel postDecoded postTyped
      · exact BlockPath.decoded_block childFuel bodyDecoded bodyTyped

end Solidity.Frontend.YulJson.ForChildren
