import Lean
import Init.Data.String.Lemmas.TakeDrop
import Init.Data.String.Lemmas.Pattern.TakeDrop.String

/-! Isolated v4.35.0 String API witnesses for the five Raw.lean dependency errors.
These are candidate adapters only: no Syntax source was edited, and no producer
migration or global semantic equivalence is asserted. -/
namespace H62.MigrateTyping

-- Raw.lean:597 and :665 require String where drop/dropEnd now produce a slice.
def droppedString (s : String) (n : Nat) : String := (s.drop n).toString
def trimmedString (s : String) : String := ((s.drop 8).dropEnd 1).toString
-- Raw.lean:650 requires a list after dropping a prefix.
def droppedChars (s : String) : List Char := (s.drop 9).toString.toList
-- Raw.lean:682 must eta-expand the now-polymorphic endsWith method.
def findSuffix (s : String) (suffixes : List String) : Option String :=
  suffixes.find? (fun suffix : String => s.endsWith suffix)
-- Raw.lean:684 uses the replacement for the removed String.dropRight.
def trimEnd (s : String) (n : Nat) : String := (s.dropEnd n).toString

example : droppedString "abcdef" 2 = "cdef" := by decide
example : droppedString "" 1 = "" := by decide
example : droppedString "éλ🙂" 1 = "λ🙂" := by decide
example : droppedChars "123456789éλ" = ['é', 'λ'] := by decide
example : trimmedString "12345678λ)" = "λ" := by
  apply String.toList_injective
  simp only [trimmedString, String.Slice.toString_eq, String.Slice.toList_copy_dropEnd,
    String.toList_copy_drop]
  decide
example : findSuffix "transfer(address)" ["(bytes)", "(address)"] = some "(address)" := by
  have hno : "transfer(address)".endsWith "(bytes)" = false := by
    rw [String.endsWith, String.Slice.endsWith_string_eq_false_iff, String.copy_toSlice]
    decide
  have hyes : "transfer(address)".endsWith "(address)" = true := by
    rw [String.endsWith, String.Slice.endsWith_string_iff, String.copy_toSlice]
    decide
  simp only [findSuffix, List.find?_cons, hno, hyes]
example : trimEnd "abcλ" 1 = "abc" := by
  apply String.toList_injective
  simp only [trimEnd, String.Slice.toString_eq, String.toList_copy_dropEnd]
  decide
example : trimEnd "" 5 = "" := by decide

end H62.MigrateTyping
