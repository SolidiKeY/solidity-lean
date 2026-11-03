import Solidity.Frontend.SolcJson.YulIfRoot
/-! Concrete enclosing-root leaves for original direct if-body assignments.
This is static certificate/position composition, not execution semantics. -/
namespace Solidity.Frontend.YulJson.IfBodyLeaves
open Lean (Json)
open Solidity.Yul
open Occurrences

structure Read {fuel root parent key node childFuel entry F X n E}
    {outer : BlockPath.Witness fuel root parent}
    {field : ControlPrefix.ReadField outer.values[outer.index] key node}
    (actual : IfRoot.Statement (childFuel := childFuel) outer field entry)
    (leaf : TypingLeaves.Path × @TypingLeaves.ReadLeaf F X n E) where
  inner : Prefix.AssignmentRead actual.inner.inner leaf
  occurrence : OccurrenceD root false
    (outer.path++(field.path++(actual.inner.inner.path++inner.inner.path))) false inner.inner.found

structure Target {fuel root parent key node childFuel entry X n E}
    {outer : BlockPath.Witness fuel root parent}
    {field : ControlPrefix.ReadField outer.values[outer.index] key node}
    (actual : IfRoot.Statement (childFuel := childFuel) outer field entry)
    (leaf : TypingLeaves.Path × @TypingLeaves.WriteLeaf X n E) where
  inner : Prefix.AssignmentTarget actual.inner.inner leaf
  occurrence : OccurrenceD root false
    (outer.path++(field.path++(actual.inner.inner.path++inner.inner.path))) true inner.inner.found

/-- Supplied-statement helper; the final root/body membership obligations are
discharged below through actual Children.statements and IfRoot.decoded_if. -/
theorem assignment {fuel root parent key node childFuel entry first rest rhs}
    {outer : BlockPath.Witness fuel root parent}
    {field : ControlPrefix.ReadField outer.values[outer.index] key node}
    (actual : IfRoot.Statement (childFuel := childFuel) outer field entry)
    (shape : entry.2.tree = .yulAssign first rest rhs) :
    ∃ child : BlockScope.AssignmentD entry.2.scope entry.2.environment (first::rest) rhs,
      HEq entry.2.typed (ScopedBlockTyping.StatementD.assignment (c := entry.2.control) child) ∧
      TypingLeaves.All (fun path leaf => Nonempty (Read actual (path,leaf)))
        (TypingLeaves.reads (TypingLeaves.assignmentReads entry.2.scope entry.2.environment child) []) ∧
      TypingLeaves.All (fun path leaf => Nonempty (Target actual (path,leaf)))
        (TypingLeaves.targets (TypingLeaves.assignmentTargets entry.2.scope entry.2.environment child) []) := by
  obtain ⟨child,original,reads,targets⟩ := Prefix.block_assignment actual.inner.inner shape
  refine ⟨child,original,?_,?_⟩
  · intro leaf present
    obtain ⟨inner⟩ := reads leaf present
    exact ⟨⟨inner,((Prefix.block_statement outer).comp field.route).lift inner.occurrence⟩⟩
  · intro leaf present
    obtain ⟨inner⟩ := targets leaf present
    exact ⟨⟨inner,((Prefix.block_statement outer).comp field.route).lift inner.occurrence⟩⟩

def Assignments {fuel root parent condition body}
    {outer : BlockPath.Witness fuel root parent} (children : IfRoot.Children outer condition body) : Prop :=
  ∀ entry ∈ TypingStatements.block children.bodyTyped, ∀ first rest rhs,
    entry.2.tree = .yulAssign first rest rhs →
    ∃ actual : IfRoot.Statement (childFuel := children.childFuel) outer children.bodyField entry,
    ∃ child : BlockScope.AssignmentD entry.2.scope entry.2.environment (first::rest) rhs,
      HEq entry.2.typed (ScopedBlockTyping.StatementD.assignment (c := entry.2.control) child) ∧
      TypingLeaves.All (fun path leaf => Nonempty (Read actual (path,leaf)))
        (TypingLeaves.reads (TypingLeaves.assignmentReads entry.2.scope entry.2.environment child) []) ∧
      TypingLeaves.All (fun path leaf => Nonempty (Target actual (path,leaf)))
        (TypingLeaves.targets (TypingLeaves.assignmentTargets entry.2.scope entry.2.environment child) [])

theorem children_assignments {fuel root parent condition body}
    {outer : BlockPath.Witness fuel root parent} (children : IfRoot.Children outer condition body) :
    Assignments children := by
  intro entry member first rest rhs shape
  obtain ⟨actual⟩ := children.statements entry member
  obtain ⟨child,original,reads,targets⟩ := assignment actual shape
  exact ⟨actual,child,original,reads,targets⟩

/-- Concrete final composition: actual original enclosing block membership,
same original if/body certificates and actual body-item membership. -/
theorem decoded_if {X scope F n E c terms condition body} (fuel : Nat) {root}
    (parsed : blockAux fuel root = .ok terms)
    (typed : @ScopedBlockTyping.BlockD X scope F n E c terms)
    (parent : Nat × TypingStatements.Item)
    (member : parent ∈ TypingStatements.block typed)
    (shape : parent.2.tree = .yulIf condition body) :
    ∃ outer : BlockPath.Witness fuel root parent,
    ∃ children : IfRoot.Children outer condition body, Assignments children := by
  obtain ⟨outer,⟨children⟩⟩ := IfRoot.decoded_if fuel parsed typed parent member shape
  exact ⟨outer,children,children_assignments children⟩


def Read.path {fuel root parent key node childFuel entry F X n E}
    {outer : BlockPath.Witness fuel root parent}
    {field : ControlPrefix.ReadField outer.values[outer.index] key node}
    {actual : IfRoot.Statement (childFuel := childFuel) outer field entry}
    {leaf : TypingLeaves.Path × @TypingLeaves.ReadLeaf F X n E}
    (witness : Read actual leaf) : List Edge :=
  outer.path++(field.path++(actual.inner.inner.path++witness.inner.inner.path))

def Target.path {fuel root parent key node childFuel entry X n E}
    {outer : BlockPath.Witness fuel root parent}
    {field : ControlPrefix.ReadField outer.values[outer.index] key node}
    {actual : IfRoot.Statement (childFuel := childFuel) outer field entry}
    {leaf : TypingLeaves.Path × @TypingLeaves.WriteLeaf X n E}
    (witness : Target actual leaf) : List Edge :=
  outer.path++(field.path++(actual.inner.inner.path++witness.inner.inner.path))

theorem Read.position_unique {fuel root parent key node childFuel entry F X n E}
    {outer : BlockPath.Witness fuel root parent}
    {field : ControlPrefix.ReadField outer.values[outer.index] key node}
    {actual : IfRoot.Statement (childFuel := childFuel) outer field entry}
    {oneLeaf twoLeaf : TypingLeaves.Path × @TypingLeaves.ReadLeaf F X n E}
    (one : Read actual oneLeaf) (two : Read actual twoLeaf)
    (same : one.path = two.path) : oneLeaf = twoLeaf := by
  have inner : one.inner.inner.path = two.inner.inner.path :=
    List.append_cancel_left (List.append_cancel_left (List.append_cancel_left same))
  exact one.inner.inner.position_unique two.inner.inner inner

theorem Read.read_write_disjoint {fuel root parent key node childFuel entry F X n reads writes}
    {outer : BlockPath.Witness fuel root parent}
    {field : ControlPrefix.ReadField outer.values[outer.index] key node}
    {actual : IfRoot.Statement (childFuel := childFuel) outer field entry}
    {readLeaf : TypingLeaves.Path × @TypingLeaves.ReadLeaf F X n reads}
    {writeLeaf : TypingLeaves.Path × @TypingLeaves.WriteLeaf X n writes}
    (one : Read actual readLeaf) (two : Target actual writeLeaf) :
    one.path ≠ two.path := by
  intro same
  have impossible := (one.occurrence.deterministic two.occurrence same).1
  cases impossible

end Solidity.Frontend.YulJson.IfBodyLeaves
