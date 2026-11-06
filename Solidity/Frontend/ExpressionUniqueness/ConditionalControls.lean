import Solidity.Frontend.ExpressionUniqueness.ConditionalSpans
import Solidity.Frontend.ExpressionUniqueness.LowControls

/-!
# Arbitrarily nested conditional middle controls

Nested true branches contain earlier top-level colons. The conditional counter
selects the outer colon after the complete branch, while a raw colon selector
selects an inner one. Every size has an inhabited original certificate.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def middleConditional : Nat → Syn .expr
  | 0 => .ident "a"
  | n + 1 => .cond (.ident "c") (middleConditional n) (.ident "b")

def middleConditionalTokens : Nat → List Tok
  | 0 => [.ident "a"]
  | n + 1 => [.ident "c", .punct .question] ++ middleConditionalTokens n ++ [.punct .colon, .ident "b"]

theorem middleConditional_prec (n : Nat) : (middleConditional n).prec = true := by
  induction n with
  | zero => rfl
  | succ n ih => exact conditional_prec_join _ _ _ rfl ih rfl (by decide) (by decide)

theorem middleConditional_yield (n : Nat) (rest : List Choice) :
    (middleConditional n).yield rest = some ([middleConditionalTokens n], rest) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [middleConditional, middleConditionalTokens, List.flatten_cons, List.flatten_nil,
      List.append_nil, pu, List.append_assoc, List.cons_append, List.nil_append] using
      conditional_yield_join (.ident "c") (middleConditional n) (.ident "b")
        rest rest rest rest [[.ident "c"]] [middleConditionalTokens n] [[.ident "b"]] rfl ih rfl

theorem middleConditional_certified (n : Nat) :
    (middleConditional n).Derives (middleConditionalTokens n) ∧ (middleConditional n).prec = true :=
  ⟨⟨[], (expr_toks_iff _ [] _).mpr (middleConditional_yield n [])⟩, middleConditional_prec n⟩

theorem middleConditional_paired (n : Nat) : QBalanced (middleConditionalTokens n) :=
  expr_derives_qBalanced _ _ (middleConditional_certified n).1

theorem middleConditionalTokens_length (n : Nat) : (middleConditionalTokens n).length = 4 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [middleConditionalTokens, List.length_append, List.length_cons, List.length_nil, ih]
    omega

theorem middleConditional_outer_colon (n : Nat) (tail : List Tok) :
    qFailure ([], 0) (middleConditionalTokens n ++ .punct .colon :: tail) = some (4 * n + 1) := by
  rw [← middleConditionalTokens_length n]
  exact qFailure_marker _ tail ([], 0) ([], 0) (.punct .colon) (middleConditional_paired n 0) rfl

def rawColon : Tok → Bool
  | .punct .colon => true
  | _ => false

theorem middleConditional_raw_colon (n : Nat) (tail : List Tok) :
    firstTop rawColon [] (middleConditionalTokens n ++ .punct .colon :: tail) =
      some (2 * n + 1, .punct .colon) := by
  induction n generalizing tail with
  | zero => rfl
  | succ n ih =>
    simp only [middleConditionalTokens, List.append_assoc, List.cons_append, List.nil_append]
    change ((firstTop rawColon [] (middleConditionalTokens n ++
      .punct .colon :: .ident "b" :: .punct .colon :: tail)).map (offset 1)).map (offset 1) = _
    rw [ih]
    simp only [Option.map_some, offset]
    congr 2

theorem middleConditional_raw_colon_wrong (n : Nat) (tail : List Tok) :
    firstTop rawColon [] (middleConditionalTokens (n + 1) ++ .punct .colon :: tail) ≠
      some (4 * (n + 1) + 1, .punct .colon) := by
  rw [middleConditional_raw_colon]
  intro equality
  have positions : 2 * (n + 1) + 1 = 4 * (n + 1) + 1 :=
    (Prod.mk.inj (Option.some.inj equality)).1
  omega

theorem bracketed_colons_hidden (k : Bracket) (n : Nat) (tail : List Tok) :
    qFailure ([], 0) ((openTok k :: (List.replicate n (.punct .colon) ++ [closeTok k])) ++
      .punct .colon :: tail) = some (n + 2) := by
  have balanced : Balanced (List.replicate n (.punct .colon)) := by
    induction n with
    | zero => exact balanced_nil
    | succ n ih => exact balanced_append (balanced_atom rfl) ih
  have paired : QBalanced (openTok k :: (List.replicate n (.punct .colon) ++ [closeTok k])) :=
    qBalanced_enclose k _ balanced
  have marker := qFailure_marker _ tail ([], 0) ([], 0) (.punct .colon) (paired 0) rfl
  simpa only [List.length_cons, List.length_append, List.length_replicate,
    List.length_nil, Nat.zero_add, Nat.add_assoc] using marker

end Solidity.Frontend.ExpressionUniqueness
