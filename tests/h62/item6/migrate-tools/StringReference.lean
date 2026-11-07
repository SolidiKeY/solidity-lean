import Lean

/-! Old v4.24 String operations copied from the two Tools sites.
Reference fixture only; originals remain unchanged.
Theorem/guard coverage here is not an equivalence proof for original functions.
-/
namespace H62.ToolsMigrationStringReference

def definitionKey (plain : String) : Option String :=
  if plain.startsWith "\\mathit{" && plain.endsWith "}" then
    some ((plain.drop 8).dropRight 1)
  else none

def ruleLabel (name : String) : String :=
  if name.startsWith "~[" && name.endsWith "]~>" then
    ((name.drop 2).dropRight 3)
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

end H62.ToolsMigrationStringReference
