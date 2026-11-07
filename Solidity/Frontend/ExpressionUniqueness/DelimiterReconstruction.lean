import Solidity.Frontend.ExpressionUniqueness.ExpressionBalance

/-!
# Reconstruct enclosing delimiter boundaries from certified expression tokens

The closing delimiter scanner's skip facts are derived from successful balanced
execution. They are not supplied as a premise by a caller of the expression
corollary. Payloads and continuations have arbitrary lengths.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem skip_of_run_forbidden_at_empty (p : Tok → Bool)
    (blocked : ∀ t, p t = true → step [] t = none)
    (ts : List Tok) (stack next : List Bracket) (h : run stack ts = some next) :
    skip p stack ts = some next := by
  induction ts generalizing stack with
  | nil => cases h; rfl
  | cons t ts ih =>
    cases hit : stack.isEmpty && p t with
    | true =>
      cases stack with
      | nil =>
        have hp : p t = true := by simpa only [List.isEmpty_nil, Bool.true_and] using hit
        simp only [run, blocked t hp, Option.bind_none] at h
        cases h
      | cons first rest =>
        have bad : false = true := by simpa only [List.isEmpty_cons, Bool.false_and] using hit
        cases bad
    | false =>
      cases hs : step stack t with
      | none => simp only [run, hs, Option.bind_none] at h; cases h
      | some middle =>
        simp only [run, hs, Option.bind_some] at h
        simp only [skip, hit, Bool.false_eq_true, ↓reduceIte, hs, Option.bind_some]
        exact ih middle h

theorem skip_close_of_balanced (k : Bracket) (ts : List Tok) (h : Balanced ts) :
    skip (fun t => decide (t = closeTok k)) [] ts = some [] := by
  apply skip_of_run_forbidden_at_empty _ _ ts [] [] (h [])
  intro t ht
  have he : t = closeTok k := of_decide_eq_true ht
  subst t
  cases k <;> rfl

theorem enclosed_payload_unique (k : Bracket) (xs ys tail tail' : List Tok)
    (hx : Balanced xs) (hy : Balanced ys)
    (heq : openTok k :: (xs ++ closeTok k :: tail) =
      openTok k :: (ys ++ closeTok k :: tail')) : xs = ys ∧ tail = tail' := by
  have hp : decide (closeTok k = closeTok k) = true := decide_eq_true rfl
  obtain ⟨payload, _, suffix⟩ := firstTop_cut_unique (fun t => decide (t = closeTok k))
    xs tail ys tail' (closeTok k) (closeTok k)
    (skip_close_of_balanced k xs hx) (skip_close_of_balanced k ys hy)
    hp hp (List.cons.inj heq).2
  exact ⟨payload, suffix⟩

theorem parens_prefix_unique (xs ys tail tail' : List Tok) (hx : Balanced xs) (hy : Balanced ys)
    (heq : parens xs ++ tail = parens ys ++ tail') : xs = ys ∧ tail = tail' := by
  apply enclosed_payload_unique .round xs ys tail tail' hx hy
  simpa only [parens, pu, openTok, closeTok, List.cons_append,
    List.nil_append, List.append_assoc] using heq

/-- No balancedness or desired split premise: both payload invariants follow
from the original expression token certificates. -/
theorem expression_parens_prefix_unique (a b : Syn .expr) (xs ys tail tail' : List Tok)
    (ha : a.Derives xs) (hb : b.Derives ys)
    (heq : parens xs ++ tail = parens ys ++ tail') : xs = ys ∧ tail = tail' :=
  parens_prefix_unique xs ys tail tail' (expr_derives_balanced a xs ha)
    (expr_derives_balanced b ys hb) heq

end Solidity.Frontend.ExpressionUniqueness
