import Solidity.Frontend.ExpressionUniqueness.Certified
import Solidity.Frontend.Checked.Check

/-!
# Accepted expression trees equal every certified tree of their actual tokens

The original parseCat_sound certificate supplies the lexical tokens, complete
layout witness and precedence. Equality follows from certified yield uniqueness,
not parser determinism. The parser and certificate implementations are unchanged.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem parseCat_expression_accepted_unique {p : Nat → P (Syn .expr)} {src : Bytes}
    {tree : Syn .expr} {layout : List Choice} (accepted : parseCat p src = .ok (tree, layout)) :
    ∃ ps, lex src = .ok ps ∧ tree.toks layout = some (tokensOf ps) ∧ tree.prec = true ∧
      ∀ other : Syn .expr, other.Derives (tokensOf ps) → other.prec = true → tree = other := by
  obtain ⟨ps, lexical, tokens, prec⟩ := parseCat_sound accepted
  exact ⟨ps, lexical, tokens, prec, fun other derived otherPrec =>
    certified_expression_yield_unique tree other (tokensOf ps) ⟨layout, tokens⟩ prec derived otherPrec⟩

theorem parseCat_expression_same_source {p q : Nat → P (Syn .expr)} {src : Bytes}
    {a b : Syn .expr} {la lb : List Choice}
    (accepted : parseCat p src = .ok (a, la)) (accepted' : parseCat q src = .ok (b, lb)) : a = b := by
  obtain ⟨ps, lexical, tokens, prec⟩ := parseCat_sound accepted
  obtain ⟨ps', lexical', tokens', prec'⟩ := parseCat_sound accepted'
  have sameTokens : ps = ps' := Except.ok.inj (lexical.symm.trans lexical')
  cases sameTokens
  exact certified_expression_yield_unique a b (tokensOf ps) ⟨la, tokens⟩ prec ⟨lb, tokens'⟩ prec'

end Solidity.Frontend.ExpressionUniqueness
