import Solidity.Syntax.StringLaws

/-! Consumer checks for the core character-count laws. -/
namespace Solidity.Examples.StringLaws
open Solidity.StringLaws

example (s : String) (b e : String.Pos) :
    (s.extract b e).length ≤ s.length := length_extract_le s b e
example (ss : Substring) : ss.toString.length ≤ ss.str.length := length_toString_le ss
example (s : String) (n : Nat) : (s.drop n).length ≤ s.length := length_drop_le s n
example (s : String) (n : Nat) : (s.dropRight n).length ≤ s.length := length_dropRight_le s n
example (s : String) (n : Nat) : (s.take n).length ≤ s.length := length_take_le s n
example (s : String) (n : Nat) : (s.takeRight n).length ≤ s.length := length_takeRight_le s n
example (s : String) : s.trim.length ≤ s.length := length_trim_le s
example (s : String) : s.trimLeft.length ≤ s.length := length_trimLeft_le s
example (s : String) : s.trimRight.length ≤ s.length := length_trimRight_le s
example (s sep x : String) (hx : x ∈ s.splitOn sep) :
    x.length ≤ s.length := length_splitOn_le s sep x hx
example (s : String) (b e : String.Pos) (hb : b ≠ 0) (hs : 0 < s.length) :
    (s.extract b e).length < s.length := length_extract_lt_of_start_ne_zero s b e hb hs
example (s : String) (n : Nat) (hn : 0 < n) (hs : 0 < s.length) :
    (s.drop n).length < s.length := length_drop_lt s n hn hs

example (s : String) (n : Nat) (hn : 0 < n) (hs : 0 < s.length) :
    (s.dropRight n).length < s.length := length_dropRight_lt s n hn hs
example (s sep x : String) (h : 1 < (s.splitOn sep).length) (hx : x ∈ s.splitOn sep) :
    x.length < s.length := length_splitOn_lt s sep x h hx

example (s sep base a : String) (rest : List String)
    (h : s.splitOn sep = base :: a :: rest) : base.length < s.length := by
  apply length_splitOn_lt s sep base
  · rw [h]; exact Nat.succ_lt_succ (Nat.zero_lt_succ _)
  · rw [h]; exact List.mem_cons_self

-- Code points, rather than UTF-8 bytes, are the measure.
example : ("α😀z".drop 1).length = 2 := by decide
example : ("α😀z".take 2).length = 2 := by decide
example : ("α😀z".dropRight 1).length = 2 := by decide
example : ("α😀z".extract ⟨2⟩ ⟨6⟩).length = 1 := by decide
example : "  α😀  ".trim.length = 2 := by
  simp +decide [String.trim, Substring.trim, Substring.takeWhileAux,
    Substring.takeRightWhileAux, String.toSubstring, String.next, String.prev,
    String.get, String.utf8GetAux, String.utf8PrevAux, Substring.toString]
example : "α😀α".splitOn "α" = ["", "😀", ""] := by
  simp +decide [String.splitOn, String.splitOnAux, String.next,
    String.get, String.utf8GetAux]
example : "α😀".splitOn "" = ["α😀"] := by decide
example : ("α😀".drop 5).length = 0 := by decide
example : ("α😀".take 5).length = 2 := by decide

end Solidity.Examples.StringLaws
