import Solidity.Frontend.SolcJson.YulBlockPath
/-! Actual direct WalkD positions without adding/rehoisting a BlockD.
Header emptiness belongs to consumers such as the real for parent. -/
namespace Solidity.Frontend.YulJson.WalkPath
open Lean (Json)
open Solidity.Yul
open Solidity.Yul.ScopedBlockTyping

theorem decoded_walk {X scope F n E c m final} (fuel : Nat) {node body}
    (parsed : blockAux fuel node = .ok body)
    (typed : @WalkD X scope F n E c body m final) :
    TypingStatements.All (fun ordinal item => Nonempty (BlockPath.Witness fuel node (ordinal,item)))
      (TypingStatements.walk typed 0) := by
  obtain ⟨childFuel,horizon,kind,values,trees,valuesEq,treesEq,bodyEq⟩ :=
    BlockPath.decoded_fields fuel parsed
  have positions : ∀ body, Solidity.Frontend.Checked.toSynList trees = body →
      ∀ typed : @WalkD X scope F n E c body m final,
      TypingStatements.All (fun ordinal item => BlockPath.ChildAt childFuel values.toList 0 (ordinal,item))
        (TypingStatements.walk typed 0) := by
    intro body same
    cases same
    intro typed
    exact BlockPath.walk_indexed childFuel values.toList treesEq typed 0
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

/-- Full item identity requires memberships in the SAME original walk. -/
theorem position_unique {X scope F n E c body m final fuel node}
    (typed : @WalkD X scope F n E c body m final)
    {first second : Nat × TypingStatements.Item}
    (one : BlockPath.Witness fuel node first) (two : BlockPath.Witness fuel node second)
    (firstMember : first ∈ TypingStatements.walk typed 0)
    (secondMember : second ∈ TypingStatements.walk typed 0)
    (same : one.path = two.path) : first = second := by
  have indices := congrArg (fun path : List Occurrences.Edge =>
    match path with | _::.array index::_ => index | _ => 0) same
  change one.index.val = two.index.val at indices
  exact TypingStatements.walk_position_unique typed 0 firstMember secondMember
    (one.position.trans (indices.trans two.position.symm))

end Solidity.Frontend.YulJson.WalkPath
