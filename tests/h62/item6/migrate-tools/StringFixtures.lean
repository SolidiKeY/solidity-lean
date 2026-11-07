import Lean
import Init.Data.String.Lemmas.TakeDrop

/-! Candidate String materialization at the two Tools sites affected by the
4.35 Slice return-type change. Isolated fixtures; originals remain unchanged.
The character-list specifications are universal for these new candidates.
They do not prove equality to the old-version implementations or original functions.
-/
namespace H62.ToolsMigrationStringFixtures

def definitionKey (plain : String) : Option String :=
  if plain.startsWith "\\mathit{" && plain.endsWith "}" then
    some ((plain.drop 8).dropEnd 1).toString
  else none

def ruleLabel (name : String) : String :=
  if name.startsWith "~[" && name.endsWith "]~>" then
    ((name.drop 2).dropEnd 3).toString
  else if name == "~*>" then "~*>" else ""

/-- Character-level specification for both wrapper-removal operations, for
all input strings and all prefix/suffix lengths, including oversized cuts. -/
theorem slice_chars (s : String) (front back : Nat) :
    ((s.drop front).dropEnd back).toString.toList =
      (s.toList.drop front).take ((s.toList.drop front).length - back) := by
  simp only [String.Slice.toString, String.Slice.toList_copy_dropEnd,
    String.toList_copy_drop]

/-- All conditional branches of the definition-key materialization. -/
theorem definitionKey_chars (plain : String) :
    (definitionKey plain).map String.toList =
      if plain.startsWith "\\mathit{" && plain.endsWith "}" then
        some ((plain.toList.drop 8).take ((plain.toList.drop 8).length - 1))
      else none := by
  unfold definitionKey
  split
  · simp only [Option.map_some, slice_chars]
  · rfl

/-- All conditional branches of the chain-rule label materialization. -/
theorem ruleLabel_chars (name : String) :
    (ruleLabel name).toList =
      if name.startsWith "~[" && name.endsWith "]~>" then
        (name.toList.drop 2).take ((name.toList.drop 2).length - 3)
      else if name == "~*>" then "~*>".toList else [] := by
  unfold ruleLabel
  split
  · exact slice_chars name 2 3
  · split <;> rfl

#guard definitionKey "\\mathit{alpha}" == some "alpha"
#guard definitionKey "\\mathit{αβ}" == some "αβ"
#guard definitionKey "\\mathit{}" == some ""
#guard definitionKey "alpha" == none
#guard definitionKey "\\mathit{alpha" == none
#guard ruleLabel "~[step]~>" == "step"
#guard ruleLabel "~[αβ]~>" == "αβ"
#guard ruleLabel "~[]~>" == ""
#guard ruleLabel "~*>" == "~*>"
#guard ruleLabel "step" == ""
#guard ruleLabel "~[step]" == ""

#print axioms slice_chars
#print axioms definitionKey_chars
#print axioms ruleLabel_chars

end H62.ToolsMigrationStringFixtures
