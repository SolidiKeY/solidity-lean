import Solidity.Correctness.Lowering.Total.FunctionTypeParserLaws.Strings

/-!
# Function-signature round trip: `String.toNat?` on character lists

Core has no lemmas for `String.any`, `String.foldl` or `String.toNat?`, and
their well-founded position loops do not reduce in the kernel. Each is proved
here, from its definition, equal to a `List Char` operation on `String.mk l`
(`any_mk`, `foldl_mk`, `toNat?_mk` with `natL`), by the position lemmas of
`FunctionTypeParserLaws/Strings`.
-/

namespace Solidity.Correctness.Lowering.Total.FunctionTypeRoundTrip

open Solidity.Correctness.Lowering.Total.FunctionTypeParserLaws.Str

theorem endPos_mk (l : List Char) : (String.mk l).endPos = ⟨ulen l⟩ := by
  simp [String.endPos, utf8ByteSize_mk]

theorem next_at (pre : List Char) (c : Char) (suf : List Char) :
    (String.mk (pre ++ c :: suf)).next ⟨ulen pre⟩ = ⟨ulen (pre ++ [c])⟩ := by
  simp [String.next, get_at, ulen_append, String.Pos.ext_iff]

theorem anyAux_mk (p : Char → Bool) : ∀ (suf pre : List Char),
    String.anyAux ⟨pre ++ suf⟩ ⟨ulen (pre ++ suf)⟩ p ⟨ulen pre⟩ = suf.any p
  | [], pre => by
    rw [String.anyAux]
    simp
  | c :: s, pre => by
    have hc := c.utf8Size_pos
    rw [String.anyAux, dif_pos (by simp [ulen_append]; omega), get_at]
    simp only [next_at]
    have ih := anyAux_mk p s (pre ++ [c])
    simp only [List.append_assoc, List.singleton_append] at ih
    rw [ih]
    cases h : p c <;> simp [h]

theorem foldlAux_mk {α : Type} (f : α → Char → α) : ∀ (suf pre : List Char) (a : α),
    String.foldlAux f ⟨pre ++ suf⟩ ⟨ulen (pre ++ suf)⟩ ⟨ulen pre⟩ a = suf.foldl f a
  | [], pre, a => by
    rw [String.foldlAux]
    simp
  | c :: s, pre, a => by
    have hc := c.utf8Size_pos
    rw [String.foldlAux, dif_pos (by simp [ulen_append]; omega), get_at]
    simp only [next_at]
    have ih := foldlAux_mk f s (pre ++ [c]) (f a c)
    simp only [List.append_assoc, List.singleton_append] at ih
    rw [ih]
    rfl

theorem any_mk (l : List Char) (p : Char → Bool) : (String.mk l).any p = l.any p := by
  have := anyAux_mk p l []
  simpa [String.any, endPos_mk] using this

theorem foldl_mk {α : Type} (f : α → Char → α) (a : α) (l : List Char) :
    (String.mk l).foldl f a = l.foldl f a := by
  have := foldlAux_mk f l [] a
  simpa [String.foldl, endPos_mk] using this

/-- `String.toNat?` on a character list. -/
def natL (l : List Char) : Option Nat :=
  if l ≠ [] ∧ l.all Char.isDigit = true then
    some (l.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0)
  else none

theorem toNat?_mk (l : List Char) : (String.mk l).toNat? = natL l := by
  unfold String.toNat? String.isNat String.all natL
  simp only [isEmpty_mk, any_mk, foldl_mk]
  cases l with
  | nil => rfl
  | cons c s =>
    simp only [List.isEmpty_cons, Bool.not_false, Bool.true_and, ne_eq, reduceCtorEq,
      not_false_eq_true, true_and]
    have : (!(c :: s).any fun c => !c.isDigit) = (c :: s).all Char.isDigit := by
      simp [List.all_eq_not_any_not]
    rw [this]

end Solidity.Correctness.Lowering.Total.FunctionTypeRoundTrip
