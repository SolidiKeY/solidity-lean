import Solidity.Yul.TypingLeafPaths

/-! Exact target observer identity/path facts over the existing indexed typing
certificates. No program AST or execution semantics is introduced. -/
namespace Solidity.Yul.TypingLeaves

theorem mem_targets_rebase {X n E paths} (typed : @TargetsD X n E paths)
    (prefixPath : Path) (entry : Path × WriteLeaf E)
    (present : entry ∈ targets typed prefixPath) :
    ∃ relative ∈ targets typed [], entry = (prefixPath++relative.1,relative.2) := by
  have same : targets typed prefixPath = rebase prefixPath (targets typed []) := by
    simpa only [List.append_nil] using targets_rebase typed prefixPath []
  rw [same] at present
  obtain ⟨relative,member,equal⟩ := List.mem_map.mp present
  exact ⟨relative,member,equal.symm⟩

theorem WriteLeaf.spelling_unique {X n E} (one two : @WriteLeaf X n E)
    (sameName : one.name = two.name) (sameParts : one.parts = two.parts) : one = two := by
  cases one with
  | mk name parts target first =>
      cases two with
      | mk otherName otherParts otherTarget second =>
          dsimp only at sameName sameParts
          cases sameName
          cases sameParts
          have pairEq := Option.some.inj (first.complete.symm.trans second.complete)
          have targetEq : target = otherTarget := congrArg Sigma.fst pairEq
          cases targetEq
          have typedEq : first = second := eq_of_heq (Sigma.mk.inj pairEq).2
          cases typedEq
          rfl

end Solidity.Yul.TypingLeaves
