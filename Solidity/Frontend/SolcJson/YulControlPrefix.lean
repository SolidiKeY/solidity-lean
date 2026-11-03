import Solidity.Frontend.SolcJson.YulPrefix
/-! Actual control-field prefix transport retaining original child certificates.
This module proves direct if-field composition, not whole-tree provenance. -/
namespace Solidity.Frontend.YulJson.ControlPrefix
open Lean (Json)
open Solidity.Yul
open Occurrences
open Solidity.Yul.ScopedBlockTyping

/-- A real decoder-selected read-role field at its actual raw ordinal.
No object-map WF, reverse lookup or uniqueness premise is introduced. -/
structure ReadField (root : Json) (key : String) (child : Json) where
  fields : Std.TreeMap.Raw String Json
  rootEq : root = .obj fields
  index : Fin fields.toList.length
  selected : fields.toList[index] = (key,child)
  notIdentifier : isIdentifier root = false
  included : includeField root key = true
  readRole : fieldRole root key = false

def ReadField.path {root key child} (field : ReadField root key child) : List Edge :=
  [.field key field.index.val]

theorem ReadField.route {root key child} (field : ReadField root key child) :
    Prefix.Route root false child false field.path := by
  have actual := Prefix.selected_field (start := false) field.index field.rootEq
    field.selected field.notIdentifier field.included
  simpa only [field.readRole] using actual

theorem ReadField.from_lookup {root key child}
    (lookup : YulJson.field root key = .ok child)
    (notIdentifier : isIdentifier root = false)
    (included : includeField root key = true)
    (readRole : fieldRole root key = false) :
    Nonempty (ReadField root key child) := by
  obtain ⟨fields,rootEq,index,selected⟩ := ObjectLookup.field_ordinal lookup
  exact ⟨⟨fields,rootEq,index,selected,notIdentifier,included,readRole⟩⟩

structure Read {root key child F X n E}
    (field : ReadField root key child)
    (leaf : TypingLeaves.Path × @TypingLeaves.ReadLeaf F X n E) where
  inner : ExpressionPath.Witness child leaf
  occurrence : OccurrenceD root false (field.path++inner.path) false inner.found

structure Statement {root key child fuel}
    (field : ReadField root key child) (entry : Nat × TypingStatements.Item) where
  inner : BlockPath.Witness fuel child entry
  route : Prefix.Route root false inner.values[inner.index] false (field.path++inner.path)

theorem reads {root key child X scope F n E term count}
    (field : ReadField root key child)
    (typed : @BlockScope.ExpressionD X F n scope E term count)
    (actual : TypedChildren.Reads child typed) :
    TypingLeaves.All (fun path leaf => Nonempty (Read field (path,leaf)))
      (TypingLeaves.reads (TypingLeaves.expressionInput scope E typed).2 []) := by
  intro entry present
  obtain ⟨inner⟩ := actual entry present
  exact ⟨⟨inner,field.route.lift inner.occurrence⟩⟩

theorem statements {root key child X scope F n E c body fuel}
    (field : ReadField root key child)
    (typed : @BlockD X scope F n E c body)
    (actual : TypedChildren.Blocks fuel child typed) :
    TypingStatements.All (fun ordinal item => Nonempty (Statement (fuel := fuel) field (ordinal,item)))
      (TypingStatements.block typed) := by
  intro entry present
  obtain ⟨inner⟩ := actual entry present
  exact ⟨⟨inner,field.route.comp (Prefix.block_statement inner)⟩⟩

/-- Concrete final if-field composition derives schema facts from the ACTUAL
decoder and extracts both children from the SAME original StatementD. -/
theorem if_positions {X scope F n E c condition body} (fuel : Nat) {node}
    (parsed : statementAux fuel node = .ok (.yulIf condition body))
    (typed : @StatementD X scope F n E c (.yulIf condition body) n E) :
    ∃ childFuel conditionNode bodyNode,
    ∃ conditionTyped : BlockScope.ExpressionD scope E condition 1,
    ∃ bodyTyped : BlockD scope E c body,
    ∃ conditionField : ReadField node "condition" conditionNode,
    ∃ bodyField : ReadField node "body" bodyNode,
      fuel = childFuel+1 ∧ expressionAux childFuel conditionNode = .ok condition ∧
      blockAux childFuel bodyNode = .ok body ∧ typed = .if_ conditionTyped bodyTyped ∧
      (TypingLeaves.expressionInput scope E conditionTyped).1 = 1 ∧
      TypingLeaves.All (fun path leaf => Nonempty (Read conditionField (path,leaf)))
        (TypingLeaves.reads (TypingLeaves.expressionInput scope E conditionTyped).2 []) ∧
      TypingStatements.All (fun ordinal item =>
        Nonempty (Statement (fuel := childFuel) bodyField (ordinal,item)))
        (TypingStatements.block bodyTyped) := by
  obtain ⟨childFuel,conditionNode,bodyNode,conditionTyped,bodyTyped,horizon,
    conditionEq,conditionParsed,bodyEq,bodyParsed,parent,count,conditionReads,bodyPositions⟩ :=
      TypedChildren.if_positions fuel parsed typed
  have kindEq : kind node = "YulIf" :=
    ObjectLookup.kind_of_string (StatementTags.kind_of_tag fuel parsed (wanted := "YulIf") rfl)
  have notIdentifier : isIdentifier node = false := by
    simp only [isIdentifier,kindEq]
    decide +kernel
  have conditionIncluded : includeField node "condition" = true := by
    simp only [includeField,kindEq,childKeys]
    decide +kernel
  have bodyIncluded : includeField node "body" = true := by
    simp only [includeField,kindEq,childKeys]
    decide +kernel
  have conditionRole : fieldRole node "condition" = false := by
    simp only [fieldRole,kindEq]
    decide +kernel
  have bodyRole : fieldRole node "body" = false := by
    simp only [fieldRole,kindEq]
    decide +kernel
  obtain ⟨conditionField⟩ := ReadField.from_lookup conditionEq notIdentifier conditionIncluded conditionRole
  obtain ⟨bodyField⟩ := ReadField.from_lookup bodyEq notIdentifier bodyIncluded bodyRole
  exact ⟨childFuel,conditionNode,bodyNode,conditionTyped,bodyTyped,conditionField,bodyField,
    horizon,conditionParsed,bodyParsed,parent,count,
    reads conditionField conditionTyped conditionReads,
    statements bodyField bodyTyped bodyPositions⟩


/-- Different actual field keys separate every descendant suffix, even when
the selected child JSON values are identical. No raw-map uniqueness needed. -/
theorem ReadField.different_keys {root oneKey twoKey oneChild twoChild}
    (one : ReadField root oneKey oneChild) (two : ReadField root twoKey twoChild)
    (different : oneKey ≠ twoKey) (oneSuffix twoSuffix : List Edge) :
    one.path++oneSuffix ≠ two.path++twoSuffix := by
  intro equal
  have heads : Edge.field oneKey one.index.val = Edge.field twoKey two.index.val :=
    (List.cons.inj equal).1
  have keys : oneKey = twoKey := (Edge.field.inj heads).1
  exact different keys

theorem Statement.lift {root key child fuel entry}
    {field : ReadField root key child} (actual : Statement (fuel := fuel) field entry)
    {path write found}
    (inside : OccurrenceD actual.inner.values[actual.inner.index] false path write found) :
    OccurrenceD root false ((field.path++actual.inner.path)++path) write found :=
  actual.route.lift inside

end Solidity.Frontend.YulJson.ControlPrefix
