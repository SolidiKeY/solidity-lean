import Solidity.Yul.TypingLeaves

/-! Exact relative-path rebasing of existing typed leaf observers.
This is static path metadata; it does not execute or replace a program. -/
namespace Solidity.Yul.TypingLeaves

def rebase {α : Type} (prefixPath : Path) (trace : List (Path × α)) : List (Path × α) :=
  trace.map (fun entry => (prefixPath++entry.1,entry.2))

mutual
theorem reads_rebase {F X n E term arity} (typed : @ExprD F X n E term arity)
    (prefixPath suffixPath : Path) :
    reads typed (prefixPath++suffixPath) = rebase prefixPath (reads typed suffixPath) := by
  revert prefixPath suffixPath
  apply ExprD.casesOn (motive_1 := fun _ _ typed => ∀ prefixPath suffixPath,
    reads typed (prefixPath++suffixPath) = rebase prefixPath (reads typed suffixPath)) typed
  case literal => intros; rfl
  case «variable» => intros; rfl
  case external => intros; rfl
  case builtin =>
    intro name args a r builtin spelling arguments prefixPath suffixPath
    change TypingLeaves.arguments arguments ((prefixPath++suffixPath)++[.arguments]) = _
    rw [List.append_assoc]
    exact arguments_rebase arguments prefixPath (suffixPath++[.arguments])
  case call =>
    intro name args signature function noBuiltin resolved arguments prefixPath suffixPath
    change TypingLeaves.arguments arguments ((prefixPath++suffixPath)++[.arguments]) = _
    rw [List.append_assoc]
    exact arguments_rebase arguments prefixPath (suffixPath++[.arguments])
termination_by structural typed

theorem arguments_rebase {F X n E terms arity} (typed : @ArgsD F X n E terms arity)
    (prefixPath suffixPath : Path) :
    arguments typed (prefixPath++suffixPath) = rebase prefixPath (arguments typed suffixPath) := by
  revert prefixPath suffixPath
  apply ArgsD.casesOn (motive_2 := fun _ _ typed => ∀ prefixPath suffixPath,
    arguments typed (prefixPath++suffixPath) = rebase prefixPath (arguments typed suffixPath)) typed
  case nil => intros; rfl
  case cons =>
    intro first rest count head tail prefixPath suffixPath
    change reads head ((prefixPath++suffixPath)++[.first]) ++
      arguments tail ((prefixPath++suffixPath)++[.rest]) =
      (reads head (suffixPath++[.first]) ++ arguments tail (suffixPath++[Edge.rest])).map
        (fun entry => (prefixPath++entry.1,entry.2))
    rw [List.map_append,List.append_assoc,List.append_assoc]
    have headEq : reads head (prefixPath++(suffixPath++[Edge.first])) =
        rebase prefixPath (reads head (suffixPath++[Edge.first])) :=
      reads_rebase head prefixPath (suffixPath++[Edge.first])
    have tailEq : arguments tail (prefixPath++(suffixPath++[Edge.rest])) =
        rebase prefixPath (arguments tail (suffixPath++[Edge.rest])) :=
      arguments_rebase tail prefixPath (suffixPath++[Edge.rest])
    rw [headEq,tailEq]
    rfl
termination_by structural typed
end

theorem targets_rebase {X n E paths} (typed : @TargetsD X n E paths)
    (prefixPath suffixPath : Path) :
    targets typed (prefixPath++suffixPath) = rebase prefixPath (targets typed suffixPath) := by
  revert prefixPath suffixPath
  apply TargetsD.casesOn (motive := fun _ typed => ∀ prefixPath suffixPath,
    targets typed (prefixPath++suffixPath) = rebase prefixPath (targets typed suffixPath)) typed
  case nil => intros; rfl
  case cons =>
    intro first rest target head tail prefixPath suffixPath
    change [( (prefixPath++suffixPath)++[.first],targetPath head)] ++
      targets tail ((prefixPath++suffixPath)++[.rest]) =
      ([(suffixPath++[Edge.first],targetPath head)] ++ targets tail (suffixPath++[Edge.rest])).map
        (fun (entry : Path × WriteLeaf E) => (prefixPath++entry.1,entry.2))
    rw [List.map_append,List.append_assoc,List.append_assoc]
    have tailEq : targets tail (prefixPath++(suffixPath++[Edge.rest])) =
        rebase prefixPath (targets tail (suffixPath++[Edge.rest])) :=
      targets_rebase tail prefixPath (suffixPath++[Edge.rest])
    rw [tailEq]
    rfl
termination_by structural typed

theorem mem_reads_rebase {F X n E term arity}
    (typed : @ExprD F X n E term arity) (prefixPath : Path) (entry : Path × ReadLeaf E)
    (present : entry ∈ reads typed prefixPath) :
    ∃ relative ∈ reads typed [], entry = (prefixPath++relative.1,relative.2) := by
  have same : reads typed prefixPath = rebase prefixPath (reads typed []) := by
    simpa only [List.append_nil] using reads_rebase typed prefixPath []
  rw [same] at present
  obtain ⟨relative,member,equal⟩ := List.mem_map.mp present
  exact ⟨relative,member,equal.symm⟩

theorem mem_arguments_rebase {F X n E terms arity}
    (typed : @ArgsD F X n E terms arity) (prefixPath : Path) (entry : Path × ReadLeaf E)
    (present : entry ∈ arguments typed prefixPath) :
    ∃ relative ∈ arguments typed [], entry = (prefixPath++relative.1,relative.2) := by
  have same : arguments typed prefixPath = rebase prefixPath (arguments typed []) := by
    simpa only [List.append_nil] using arguments_rebase typed prefixPath []
  rw [same] at present
  obtain ⟨relative,member,equal⟩ := List.mem_map.mp present
  exact ⟨relative,member,equal.symm⟩

/-- Exact spelling under the SAME actual environment fixes the full intrinsic
leaf certificate, including its real local/external binding. -/
theorem ReadLeaf.spelling_unique {F X n E} (one two : @ReadLeaf F X n E)
    (sameName : one.name = two.name) (sameParts : one.parts = two.parts) : one = two := by
  cases one with
  | mk name parts first =>
      cases two with
      | mk otherName otherParts second =>
          dsimp only at sameName sameParts
          cases sameName
          cases sameParts
          have pairEq := Option.some.inj (first.complete.symm.trans second.complete)
          have typedEq : first = second := eq_of_heq (Sigma.mk.inj pairEq).2
          cases typedEq
          rfl

end Solidity.Yul.TypingLeaves
