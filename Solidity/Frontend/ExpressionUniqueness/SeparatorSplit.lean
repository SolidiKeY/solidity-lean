import Solidity.Frontend.ExpressionUniqueness.TokenSplit
import Solidity.Frontend.Checked.Print

/-!
# Comma-separated token span reconstruction

The result allows empty component words, as intrinsic tuple holes require.
Its nonempty component-vector boundary is explicit: the empty vector and one
empty component have identical comma-separated words. Expression-derived
comma freedom remains open; this module does not assume a desired root split.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def isComma (t : Tok) : Bool := decide (t = .punct .comma)

def CommaFree (ts : List Tok) : Prop := skip isComma [] ts = some []

def CommaFreeItems (items : List (List Tok)) : Prop := ∀ ts, ts ∈ items → CommaFree ts

theorem firstTop_none_of_skip (p : Tok → Bool) (ts : List Tok)
    (h : skip p [] ts = some []) : firstTop p [] ts = none := by
  have hf := firstTop_append_of_skip p ts [] [] [] h
  simpa only [List.append_nil, firstTop, Option.map_none] using hf

theorem commaFree_nil : CommaFree [] := rfl

theorem commaFreeItems_tail (xs : List Tok) (xss : List (List Tok))
    (h : CommaFreeItems (xs :: xss)) : CommaFreeItems xss := by
  intro ts ht
  exact h ts (List.mem_cons.mpr (Or.inr ht))

theorem commaSep_single (xs : List Tok) : commaSep [xs] = xs := by
  simp only [commaSep, List.intersperse_single, List.flatten_cons,
    List.flatten_nil, List.append_nil]

theorem commaSep_cons_cons (xs ys : List Tok) (rest : List (List Tok)) :
    commaSep (xs :: ys :: rest) = xs ++ .punct .comma :: commaSep (ys :: rest) := rfl

theorem commaFree_not_marker_word (xs ys tail : List Tok) (hx : CommaFree xs)
    (hy : CommaFree ys) : xs ≠ ys ++ .punct .comma :: tail := by
  intro he
  have left := firstTop_none_of_skip isComma xs hx
  have right := firstTop_marker isComma ys tail (.punct .comma) hy rfl
  rw [he, right] at left
  cases left

/-- The actual commaSep operation is injective on nonempty vectors of
comma-free words, including arbitrarily many empty tuple holes. -/
theorem commaSep_nonempty_unique (xs ys : List Tok) (xss yss : List (List Tok))
    (hx : CommaFreeItems (xs :: xss)) (hy : CommaFreeItems (ys :: yss))
    (he : commaSep (xs :: xss) = commaSep (ys :: yss)) : xs :: xss = ys :: yss := by
  induction xss generalizing xs ys yss with
  | nil =>
    cases yss with
    | nil =>
      simp only [commaSep_single] at he
      exact congrArg (fun x => [x]) he
    | cons y yss =>
      simp only [commaSep_single, commaSep_cons_cons] at he
      exact False.elim (commaFree_not_marker_word xs ys _
        (hx xs (List.mem_cons.mpr (Or.inl rfl)))
        (hy ys (List.mem_cons.mpr (Or.inl rfl))) he)
  | cons x xss ih =>
    cases yss with
    | nil =>
      simp only [commaSep_single, commaSep_cons_cons] at he
      exact False.elim (commaFree_not_marker_word ys xs _
        (hy ys (List.mem_cons.mpr (Or.inl rfl)))
        (hx xs (List.mem_cons.mpr (Or.inl rfl))) he.symm)
    | cons y yss =>
      simp only [commaSep_cons_cons] at he
      obtain ⟨head, _, tail⟩ := firstTop_cut_unique isComma xs (commaSep (x :: xss))
        ys (commaSep (y :: yss)) (.punct .comma) (.punct .comma)
        (hx xs (List.mem_cons.mpr (Or.inl rfl)))
        (hy ys (List.mem_cons.mpr (Or.inl rfl))) rfl rfl he
      have rest := ih x y yss (commaFreeItems_tail xs _ hx) (commaFreeItems_tail ys _ hy) tail
      exact head ▸ congrArg (List.cons ys) rest

/-- This exact boundary forbids silently extending the preceding theorem to
all vectors; intrinsic tuples carry a first slot even when that slot is absent. -/
theorem commaSep_empty_single_empty : commaSep [] = commaSep [[]] := rfl

theorem empty_holes_comma_free (n : Nat) : CommaFreeItems (List.replicate n []) := by
  intro ts ht
  have he : ts = [] := List.eq_of_mem_replicate ht
  subst ts
  exact commaFree_nil

theorem arbitrary_holes_reconstructed (n m : Nat)
    (h : commaSep ([] :: List.replicate n []) = commaSep ([] :: List.replicate m [])) : n = m := by
  have hn : CommaFreeItems ([] :: List.replicate n []) := by
    change CommaFreeItems (List.replicate (n + 1) [])
    exact empty_holes_comma_free (n + 1)
  have hm : CommaFreeItems ([] :: List.replicate m []) := by
    change CommaFreeItems (List.replicate (m + 1) [])
    exact empty_holes_comma_free (m + 1)
  have equal := commaSep_nonempty_unique [] [] _ _ hn hm h
  have lengths := congrArg List.length equal
  simpa only [List.length_cons, List.length_replicate, Nat.add_right_cancel_iff] using lengths

end Solidity.Frontend.ExpressionUniqueness
