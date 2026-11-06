import Lean

/-! Candidate String materialization at the two Tools sites affected by the
4.35 Slice return-type change. Isolated fixtures; originals remain unchanged.
Theorem/guard coverage here is not an equivalence proof for original functions.
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

end H62.ToolsMigrationStringFixtures
