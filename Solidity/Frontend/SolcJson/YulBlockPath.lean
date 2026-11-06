import Solidity.Frontend.SolcJson.YulAssignmentPath
import Solidity.Yul.TypingStatements

/-! Direct block statement positions, retaining the original sequential and
hoisted intrinsic contexts. Nested statement/site/leaf alignment is separate. -/
namespace Solidity.Frontend.YulJson.BlockPath
open Lean (Json)
open Solidity.Yul
open Solidity.Yul.ScopedBlockTyping

def ChildAt (fuel : Nat) (nodes : List Json) (offset : Nat)
    (entry : Nat × TypingStatements.Item) : Prop :=
  ∃ index : Fin nodes.length, entry.1 = offset+index.val ∧
    statementAux fuel nodes[index] = .ok entry.2.tree

/-- The actual per-statement decoder equation and exact input-list index.
Every sibling consumes one ordinal, including functions and control statements. -/
theorem walk_indexed (fuel : Nat) (nodes : List Json) {trees}
    (parsed : nodes.mapM (statementAux fuel) = .ok trees)
    {X scope F n E c m final}
    (typed : @WalkD X scope F n E c (Solidity.Frontend.Checked.toSynList trees) m final)
    (offset : Nat) :
    TypingStatements.All (fun ordinal item => ChildAt fuel nodes offset (ordinal,item))
      (TypingStatements.walk typed offset) := by
  induction nodes generalizing trees n m offset with
  | nil =>
      change (Except.ok [] : Except Error (List (Solidity.Source.Syn .yulStmt))) = .ok trees at parsed
      cases parsed
      cases typed
      intro entry impossible
      cases impossible
  | cons node rest ih =>
      cases headEq : statementAux fuel node with
      | error reason =>
          simp only [List.mapM_cons,headEq,bind,Except.bind] at parsed
          cases parsed
      | ok headTree =>
          cases tailEq : rest.mapM (statementAux fuel) with
          | error reason =>
              simp only [List.mapM_cons,headEq,tailEq,bind,Except.bind] at parsed
              cases parsed
          | ok tailTrees =>
              have same : headTree::tailTrees = trees := Except.ok.inj (by
                simpa only [List.mapM_cons,headEq,tailEq,bind,Except.bind,pure,Except.pure] using parsed)
              cases same
              cases typed with
              | cons head tail =>
                  intro entry present
                  change entry ∈ (offset,TypingStatements.Item.ofD head)::
                    TypingStatements.walk tail (offset+1) at present
                  rcases List.mem_cons.mp present with same | later
                  · cases same
                    exact ⟨⟨0,Nat.zero_lt_succ _⟩,rfl,headEq⟩
                  · obtain ⟨index,position,decoded⟩ := ih tailEq tail (offset+1) entry later
                    exact ⟨⟨index.val+1,Nat.succ_lt_succ index.isLt⟩,by
                      change entry.1 = offset+(index.val+1)
                      omega,decoded⟩

/-- Actual block decoder inversion, including its precise child fuel. -/
theorem decoded_fields (fuel : Nat) {node body}
    (parsed : blockAux fuel node = .ok body) :
    ∃ childFuel, fuel = childFuel+1 ∧ string node "nodeType" = .ok "YulBlock" ∧
      ∃ values trees, array node "statements" = .ok values ∧
        values.toList.mapM (statementAux childFuel) = .ok trees ∧
        Solidity.Frontend.Checked.toSynList trees = body := by
  cases fuel with
  | zero => cases parsed
  | succ fuel =>
      rw [blockAux] at parsed
      unfold requireNode at parsed
      cases kindEq : string node "nodeType" with
      | error reason =>
          simp only [kindEq,bind,Except.bind] at parsed
          cases parsed
      | ok kind =>
          simp only [kindEq,bind,Except.bind] at parsed
          by_cases correct : kind = "YulBlock"
          · simp only [correct,if_true,pure,Except.pure] at parsed
            cases valuesEq : array node "statements" with
            | error reason =>
                simp only [valuesEq] at parsed
                cases parsed
            | ok values =>
                simp only [valuesEq] at parsed
                cases treesEq : values.toList.mapM (statementAux fuel) with
                | error reason =>
                    simp only [treesEq] at parsed
                    cases parsed
                | ok trees =>
                    simp only [treesEq] at parsed
                    exact ⟨fuel,rfl,congrArg Except.ok correct,values,trees,rfl,treesEq,Except.ok.inj parsed⟩
          · simp only [correct,if_false,throw] at parsed
            cases parsed

structure Witness (fuel : Nat) (node : Json) (entry : Nat × TypingStatements.Item) where
  childFuel : Nat
  horizon : fuel = childFuel+1
  kind : string node "nodeType" = .ok "YulBlock"
  fields : Std.TreeMap.Raw String Json
  root : node = .obj fields
  fieldIndex : Fin fields.toList.length
  values : Array Json
  selected : fields.toList[fieldIndex] = ("statements",.arr values)
  valuesEq : array node "statements" = .ok values
  index : Fin values.size
  position : entry.1 = index.val
  decoded : statementAux childFuel values[index] = .ok entry.2.tree

def Witness.path {fuel node entry} (actual : Witness fuel node entry) : List Occurrences.Edge :=
  [.field "statements" actual.fieldIndex.val,.array actual.index.val]

/-- Final concrete direct-block correspondence. Both contexts in each item
come from the original BlockD's actual hoisted/sequential WalkD. -/
theorem decoded_block {X scope F n E c} (fuel : Nat) {node body}
    (parsed : blockAux fuel node = .ok body)
    (typed : @BlockD X scope F n E c body) :
    TypingStatements.All (fun ordinal item => Nonempty (Witness fuel node (ordinal,item)))
      (TypingStatements.block typed) := by
  obtain ⟨childFuel,horizon,kind,values,trees,valuesEq,treesEq,bodyEq⟩ :=
    decoded_fields fuel parsed
  have positions : ∀ body, Solidity.Frontend.Checked.toSynList trees = body →
      ∀ typed : @BlockD X scope F n E c body,
      TypingStatements.All (fun ordinal item => ChildAt childFuel values.toList 0 (ordinal,item))
        (TypingStatements.block typed) := by
    intro body same
    cases same
    intro typed
    cases typed with
    | intro headers typedWalk =>
        exact walk_indexed childFuel values.toList treesEq typedWalk 0
  obtain ⟨fields,root,fieldIndex,selected⟩ :=
    ObjectLookup.field_ordinal (ObjectLookup.array_field valuesEq)
  intro entry present
  obtain ⟨index,ordinal,decoded⟩ := positions body bodyEq typed entry present
  have bound : index.val < values.size := by
    simpa only [Array.length_toList] using index.isLt
  let actual : Fin values.size := ⟨index.val,bound⟩
  have statementEq : statementAux childFuel values[actual] = .ok entry.2.tree := by
    change statementAux childFuel (values[index.val]'bound) = _
    change statementAux childFuel (values.toList[index.val]'index.isLt) = _ at decoded
    simpa only [Array.getElem_toList] using decoded
  exact ⟨⟨childFuel,horizon,kind,fields,root,fieldIndex,values,selected,valuesEq,actual,
    by simpa only [Nat.zero_add] using ordinal,statementEq⟩⟩

theorem Witness.position_unique {X scope F n E c body fuel node}
    (typed : @BlockD X scope F n E c body) {first second : Nat × TypingStatements.Item}
    (one : Witness fuel node first) (two : Witness fuel node second)
    (firstMember : first ∈ TypingStatements.block typed)
    (secondMember : second ∈ TypingStatements.block typed)
    (same : one.path = two.path) : first = second := by
  have indices := congrArg (fun path : List Occurrences.Edge =>
    match path with | _::.array index::_ => index | _ => 0) same
  change one.index.val = two.index.val at indices
  exact TypingStatements.block_position_unique typed firstMember secondMember
    (one.position.trans (indices.trans two.position.symm))

end Solidity.Frontend.YulJson.BlockPath
