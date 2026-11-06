import Lean

/-! Isolated String API controls for the migration blocker; no production file edits.
These test concrete standard-library behavior, not full Calculus preservation. -/
namespace H62.MigrateCalculus.StringApiCases

-- Old String.substrEq uses a private well-founded loop. Unfold its checked
-- equations at most four times (the fixture suffixes have at most two characters).
-- This tactic only rewrites the goal; the resulting proof is checked by Lean.
elab "unfoldLegacySuffix" : tactic => do
  let env ← Lean.getEnv
  let some (name, _) := env.constants.toList.find? (fun pair =>
      pair.1.toString.endsWith "String.substrEq.loop")
    | throwError "Pinned legacy suffix loop not found"
  let mut goal ← Lean.Elab.Tactic.getMainGoal
  for _ in [:4] do
    try
      goal ← Lean.Meta.unfoldTarget goal name
    catch _ => pure ()
  Lean.Elab.Tactic.replaceMainGoal [goal]

def dropAsString (s : String) (n : Nat) : String := toString (s.drop n)

def droppedChars (s : String) (n : Nat) : List Char := (toString (s.drop n)).toList

def findSuffix (s : String) (suffixes : List String) : Option String :=
  suffixes.find? (fun suffix : String => s.endsWith suffix)

theorem asciiDrop : dropAsString "abcdef" 2 = "cdef" := by decide
theorem unicodeDrop : dropAsString "λ☃a" 1 = "☃a" := by decide
theorem unicodeDropNegative : dropAsString "λ☃a" 1 ≠ "λ☃a" := by decide
theorem zeroDrop : dropAsString "λ☃a" 0 = "λ☃a" := by decide
theorem pastEnd : dropAsString "λ☃a" 9 = "" := by decide
theorem unicodeChars : droppedChars "λ☃a" 1 = ['☃', 'a'] := by decide
theorem suffixMatch : findSuffix "λ☃a" ["no", "☃a"] = some "☃a" := by
  have hno : "λ☃a".endsWith ("no" : String) = false := by
    first
    | exact String.Slice.endsWith_string_eq_false_iff.mpr (by decide)
    | simp only [String.endsWith, Substring.hasBeq, Substring.beq, String.substrEq]
      unfoldLegacySuffix
      decide +kernel
  have hyes : "λ☃a".endsWith ("☃a" : String) = true := by
    first
    | exact String.Slice.endsWith_string_iff.mpr (by decide)
    | simp only [String.endsWith, Substring.hasBeq, Substring.beq, String.substrEq]
      unfoldLegacySuffix
      decide +kernel
  simp only [findSuffix, List.find?, hno, hyes]
theorem suffixNegative : findSuffix "λ☃a" ["λ", "b"] = none := by
  have hfirst : "λ☃a".endsWith ("λ" : String) = false := by
    first
    | exact String.Slice.endsWith_string_eq_false_iff.mpr (by decide)
    | simp only [String.endsWith, Substring.hasBeq, Substring.beq, String.substrEq]
      unfoldLegacySuffix
      decide +kernel
  have hlast : "λ☃a".endsWith ("b" : String) = false := by
    first
    | exact String.Slice.endsWith_string_eq_false_iff.mpr (by decide)
    | simp only [String.endsWith, Substring.hasBeq, Substring.beq, String.substrEq]
      unfoldLegacySuffix
      decide +kernel
  simp only [findSuffix, List.find?, hfirst, hlast]

#print axioms asciiDrop
#print axioms unicodeDrop
#print axioms unicodeDropNegative
#print axioms zeroDrop
#print axioms pastEnd
#print axioms unicodeChars
#print axioms suffixMatch
#print axioms suffixNegative
end H62.MigrateCalculus.StringApiCases
