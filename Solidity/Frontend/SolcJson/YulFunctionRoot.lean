import Solidity.Frontend.SolcJson.YulIfBodyLeaves
/-! Actual enclosing-root Yul function-body provenance. The existing generic
IfRoot.Statement position record is reused; no phantom if certificate or
new function semantics is introduced. -/
namespace Solidity.Frontend.YulJson.FunctionRoot
open Lean (Json)
open Solidity.Yul
open Solidity.Yul.ScopedBlockTyping
open Occurrences
open ControlPrefix

structure Children {fuel root parent}
    (outer : BlockPath.Witness fuel root parent) (name : String) (args rets : List String)
    (body : Solidity.Source.Syn (.list .yulStmt)) where
  childFuel : Nat
  bodyNode : Json
  bodyTyped : BlockD parent.2.scope.function (BlockTyping.Env.frame parent.2.environment args rets)
    ⟨true,false⟩ body
  field : ReadField outer.values[outer.index] "body" bodyNode
  horizon : outer.childFuel = childFuel+1
  parsed : blockAux childFuel bodyNode = .ok body
  original : HEq parent.2.typed (StatementD.function (name := name) (args := args) (rets := rets) (c := parent.2.control) bodyTyped)
  statements : TypingStatements.All (fun ordinal item =>
    Nonempty (IfRoot.Statement (childFuel := childFuel) outer field (ordinal,item)))
    (TypingStatements.block bodyTyped)

/-- Supplied-item helper, preserving ORIGINAL function globals/frame/control.
The final root membership proof is decoded_function below. -/
theorem function_statement {fuel root parent name args rets body}
    (outer : BlockPath.Witness fuel root parent)
    (shape : parent.2.tree = .yulFun name args rets body) :
    Nonempty (Children outer name args rets body) := by
  rcases parent with ⟨ordinal,item⟩
  rcases item with ⟨X,scope,F,n,m,E,c,tree,final,typed⟩
  cases shape
  cases typed with
  | function originalBody =>
      obtain ⟨childFuel,bodyNode,bodyTyped,horizon,bodyEq,parsed,parentEq,positions⟩ :=
        TypedChildren.function_positions outer.childFuel outer.decoded (.function (c := c) originalBody)
      have kindEq : kind outer.values[outer.index] = "YulFunctionDefinition" :=
        ObjectLookup.kind_of_string
          (StatementTags.kind_of_tag outer.childFuel outer.decoded
            (wanted := "YulFunctionDefinition") rfl)
      have notIdentifier : isIdentifier outer.values[outer.index] = false := by
        simp only [isIdentifier,kindEq]
        decide +kernel
      have included : includeField outer.values[outer.index] "body" = true := by
        simp only [includeField,kindEq,childKeys]
        decide +kernel
      have role : fieldRole outer.values[outer.index] "body" = false := by
        simp only [fieldRole,kindEq]
        decide +kernel
      obtain ⟨field⟩ := ReadField.from_lookup bodyEq notIdentifier included role
      refine ⟨⟨childFuel,bodyNode,bodyTyped,field,horizon,parsed,heq_of_eq parentEq,?_⟩⟩
      have actual := ControlPrefix.statements field bodyTyped positions
      intro entry present
      obtain ⟨inner⟩ := actual entry present
      exact ⟨⟨inner,(Prefix.block_statement outer).comp inner.route⟩⟩

def Assignments {fuel root parent name args rets body}
    {outer : BlockPath.Witness fuel root parent} (children : Children outer name args rets body) : Prop :=
  ∀ entry ∈ TypingStatements.block children.bodyTyped, ∀ first rest rhs,
    entry.2.tree = .yulAssign first rest rhs →
    ∃ actual : IfRoot.Statement (childFuel := children.childFuel) outer children.field entry,
    ∃ child : BlockScope.AssignmentD entry.2.scope entry.2.environment (first::rest) rhs,
      HEq entry.2.typed (StatementD.assignment (c := entry.2.control) child) ∧
      TypingLeaves.All (fun path leaf => Nonempty (IfBodyLeaves.Read actual (path,leaf)))
        (TypingLeaves.reads (TypingLeaves.assignmentReads entry.2.scope entry.2.environment child) []) ∧
      TypingLeaves.All (fun path leaf => Nonempty (IfBodyLeaves.Target actual (path,leaf)))
        (TypingLeaves.targets (TypingLeaves.assignmentTargets entry.2.scope entry.2.environment child) [])

theorem children_assignments {fuel root parent name args rets body}
    {outer : BlockPath.Witness fuel root parent} (children : Children outer name args rets body) :
    Assignments children := by
  intro entry member first rest rhs shape
  obtain ⟨actual⟩ := children.statements entry member
  obtain ⟨child,original,reads,targets⟩ := IfBodyLeaves.assignment actual shape
  exact ⟨actual,child,original,reads,targets⟩

/-- Concrete root composition, not an assumed function/namespace agreement.
Original root/full item and original function-body item memberships remain. -/
theorem decoded_function {X scope F n E c terms name args rets body} (fuel : Nat) {root}
    (parsed : blockAux fuel root = .ok terms)
    (typed : @BlockD X scope F n E c terms)
    (parent : Nat × TypingStatements.Item)
    (member : parent ∈ TypingStatements.block typed)
    (shape : parent.2.tree = .yulFun name args rets body) :
    ∃ outer : BlockPath.Witness fuel root parent,
    ∃ children : Children outer name args rets body, Assignments children := by
  obtain ⟨outer⟩ := BlockPath.decoded_block fuel parsed typed parent member
  obtain ⟨children⟩ := function_statement outer shape
  exact ⟨outer,children,children_assignments children⟩

end Solidity.Frontend.YulJson.FunctionRoot
