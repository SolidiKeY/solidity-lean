import Solidity.Frontend.SolcJson.YulControlPrefix
/-! Concrete enclosing-block membership composition for actual Yul if fields.
All new structures retain original certificates and JSON positions as metadata. -/
namespace Solidity.Frontend.YulJson.IfRoot
open Lean (Json)
open Solidity.Yul
open Occurrences
open Solidity.Yul.ScopedBlockTyping
open ControlPrefix

structure Read {fuel root statement key node F X n E}
    (outer : BlockPath.Witness fuel root statement)
    (field : ReadField outer.values[outer.index] key node)
    (leaf : TypingLeaves.Path × @TypingLeaves.ReadLeaf F X n E) where
  inner : ControlPrefix.Read field leaf
  occurrence : OccurrenceD root false
    (outer.path++(field.path++inner.inner.path)) false inner.inner.found

structure Statement {fuel root statement key node childFuel}
    (outer : BlockPath.Witness fuel root statement)
    (field : ReadField outer.values[outer.index] key node)
    (entry : Nat × TypingStatements.Item) where
  inner : ControlPrefix.Statement (fuel := childFuel) field entry
  route : Prefix.Route root false inner.inner.values[inner.inner.index] false
    (outer.path++(field.path++inner.inner.path))

/-- All payloads retain the actual child derivations of the supplied ORIGINAL
item. Existence alone does not supply enclosing-block membership; decoded_if
below additionally proves membership via the original root BlockD. -/
structure Children {fuel root statement}
    (outer : BlockPath.Witness fuel root statement)
    (condition : Solidity.Source.Syn .yulExpr)
    (body : Solidity.Source.Syn (.list .yulStmt)) where
  childFuel : Nat
  conditionNode : Json
  bodyNode : Json
  conditionTyped : BlockScope.ExpressionD statement.2.scope statement.2.environment condition 1
  bodyTyped : BlockD statement.2.scope statement.2.environment statement.2.control body
  conditionField : ReadField outer.values[outer.index] "condition" conditionNode
  bodyField : ReadField outer.values[outer.index] "body" bodyNode
  horizon : outer.childFuel = childFuel+1
  conditionParsed : expressionAux childFuel conditionNode = .ok condition
  bodyParsed : blockAux childFuel bodyNode = .ok body
  original : HEq statement.2.typed (StatementD.if_ conditionTyped bodyTyped)
  count : (TypingLeaves.expressionInput statement.2.scope statement.2.environment conditionTyped).1 = 1
  reads : TypingLeaves.All (fun path leaf => Nonempty (Read outer conditionField (path,leaf)))
    (TypingLeaves.reads
      (TypingLeaves.expressionInput statement.2.scope statement.2.environment conditionTyped).2 [])
  statements : TypingStatements.All (fun ordinal item =>
    Nonempty (Statement (childFuel := childFuel) outer bodyField (ordinal,item)))
    (TypingStatements.block bodyTyped)

theorem if_statement {fuel root statement condition body}
    (outer : BlockPath.Witness fuel root statement)
    (shape : statement.2.tree = .yulIf condition body) :
    Nonempty (Children outer condition body) := by
  rcases statement with ⟨ordinal,item⟩
  rcases item with ⟨X,scope,F,n,m,E,c,tree,final,typed⟩
  cases shape
  cases typed with
  | if_ originalCondition originalBody =>
      obtain ⟨childFuel,conditionNode,bodyNode,conditionTyped,bodyTyped,conditionField,bodyField,
        horizon,conditionParsed,bodyParsed,parent,count,reads,statements⟩ :=
        ControlPrefix.if_positions outer.childFuel outer.decoded
          (.if_ (c := c) originalCondition originalBody)
      refine ⟨⟨childFuel,conditionNode,bodyNode,conditionTyped,bodyTyped,conditionField,bodyField,
        horizon,conditionParsed,bodyParsed,heq_of_eq parent,count,?_,?_⟩⟩
      · intro entry present
        obtain ⟨inner⟩ := reads entry present
        exact ⟨⟨inner,Prefix.block_occurrence outer inner.occurrence⟩⟩
      · intro entry present
        obtain ⟨inner⟩ := statements entry present
        exact ⟨⟨inner,(Prefix.block_statement outer).comp inner.route⟩⟩

/-- Concrete final root composition requires actual root decoding, SAME
original BlockD and FULL original Item membership, not a prepared context. -/
theorem decoded_if {X scope F n E c terms condition body} (fuel : Nat) {root}
    (parsed : blockAux fuel root = .ok terms)
    (typed : @BlockD X scope F n E c terms)
    (statement : Nat × TypingStatements.Item)
    (member : statement ∈ TypingStatements.block typed)
    (shape : statement.2.tree = .yulIf condition body) :
    ∃ outer : BlockPath.Witness fuel root statement, Nonempty (Children outer condition body) := by
  obtain ⟨outer⟩ := BlockPath.decoded_block fuel parsed typed statement member
  exact ⟨outer,if_statement outer shape⟩

theorem Statement.lift {fuel root statement key node childFuel entry}
    {outer : BlockPath.Witness fuel root statement}
    {field : ReadField outer.values[outer.index] key node}
    (actual : Statement (childFuel := childFuel) outer field entry)
    {path write found}
    (inside : OccurrenceD actual.inner.inner.values[actual.inner.inner.index] false path write found) :
    OccurrenceD root false
      ((outer.path++(field.path++actual.inner.inner.path))++path) write found :=
  actual.route.lift inside


theorem Children.field_separation {fuel root statement condition body}
    {outer : BlockPath.Witness fuel root statement} (actual : Children outer condition body)
    (oneSuffix twoSuffix : List Edge) :
    outer.path++(actual.conditionField.path++oneSuffix) ≠
      outer.path++(actual.bodyField.path++twoSuffix) := by
  intro equal
  exact actual.conditionField.different_keys actual.bodyField (by decide +kernel)
    oneSuffix twoSuffix (List.append_cancel_left equal)

end Solidity.Frontend.YulJson.IfRoot
