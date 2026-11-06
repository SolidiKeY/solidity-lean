import Solidity.Frontend.ExpressionUniqueness.BinarySpans
import Solidity.Frontend.ExpressionUniqueness.AddControls

/-!
# Arbitrary-family controls for recovered operand spans

The additive certificate may contain arbitrarily many unary-minus tokens in its
right child. Shared successful yields reconstruct both the operator and depth,
with independently chosen unconsumed layouts. This is a family theorem, not the
still-open uniqueness theorem for every intrinsic expression.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem mixedAddPrefix_partial_unique (op op' : AddOp) (n m : Nat)
    (initial rest initial' rest' : List Choice) (items items' : List (List Tok))
    (hy : (mixedAddPrefix op n).yield initial = some (items, rest))
    (hy' : (mixedAddPrefix op' m).yield initial' = some (items', rest'))
    (heq : items.flatten = items'.flatten) : op = op' ∧ n = m := by
  obtain ⟨operator, spans⟩ := add_child_spans op op' (.ident "a") (negFamily (n + 1) "b")
    (.ident "a") (negFamily (m + 1) "b") initial rest initial' rest' items items'
    (mixedAddPrefix_prec op n) (mixedAddPrefix_prec op' m) hy hy' heq
  obtain ⟨xs, ys, xs', ys', middle, middle', hx, hright, hx', hright', left, right⟩ := spans
  have words : ys = [negTokens (n + 1) "b"] :=
    (Prod.mk.inj (Option.some.inj (hright.symm.trans (negFamily_yield (n + 1) "b" middle)))).1
  have words' : ys' = [negTokens (m + 1) "b"] :=
    (Prod.mk.inj (Option.some.inj (hright'.symm.trans (negFamily_yield (m + 1) "b" middle')))).1
  rw [words, words'] at right
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at right
  have lengths : (n + 1) + 1 = (m + 1) + 1 := by
    simpa only [negTokens_length] using congrArg List.length right
  exact ⟨operator, Nat.add_right_cancel (Nat.add_right_cancel lengths)⟩

theorem mixedAddPrefix_same_yield_unique (op op' : AddOp) (n m : Nat) (ts : List Tok)
    (hy : (mixedAddPrefix op n).Derives ts) (hy' : (mixedAddPrefix op' m).Derives ts) :
    mixedAddPrefix op n = mixedAddPrefix op' m := by
  obtain ⟨initial, h⟩ := hy
  obtain ⟨initial', h'⟩ := hy'
  obtain ⟨operator, depth⟩ := mixedAddPrefix_partial_unique op op' n m initial [] initial' []
    [ts] [ts] ((expr_toks_iff _ initial ts).mp h) ((expr_toks_iff _ initial' ts).mp h') rfl
  rw [operator, depth]

end Solidity.Frontend.ExpressionUniqueness
