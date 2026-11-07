import Solidity.Frontend.ExpressionUniqueness.AllRootLevels
import Solidity.Frontend.ExpressionUniqueness.PostfixControls
import Solidity.Frontend.ExpressionUniqueness.TypePrefixControls

/-!
# Arbitrary primary/postfix boundary controls

These inhabited families use the original certificates. The raw type/index
collision remains refused; direct-new square/member followers remain forbidden,
whereas call/options followers remain available for every type-array depth.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem postfixTower_root_reconstructed (n : Nat) (other : Syn .expr)
    (hp : other.prec = true) (hy : other.Derives (postfixTowerTokens n)) :
    other.level = (postfixTower n).level :=
  certified_root_levels_equal other (postfixTower n) (postfixTowerTokens n)
    hp (postfixTower_prec n) hy (postfixTower_certified n).1

theorem new_array_root_reconstructed (n : Nat) (other : Syn .expr)
    (hp : other.prec = true) (hy : other.Derives (tk .new ++ arrayTypeTokens n)) :
    other.level = 16 :=
  certified_root_levels_equal other (.new (arrayTypeFamily n)) (tk .new ++ arrayTypeTokens n)
    hp (new_arrayTypeFamily_certified n).2 hy (new_arrayTypeFamily_certified n).1

theorem direct_new_square_follower_refuted (tail : List Tok) :
    ¬ PostfixFollower true (.punct .lbrack :: tail) := by
  intro h
  rcases h with empty | paren | brace | ⟨notNew, squareOrPeriod⟩
  · cases empty
  · obtain ⟨rest, h⟩ := paren
    cases h
  · obtain ⟨rest, h⟩ := brace
    cases h
  · cases notNew

theorem direct_new_period_follower_refuted (tail : List Tok) :
    ¬ PostfixFollower true (.punct .period :: tail) := by
  intro h
  rcases h with empty | paren | brace | ⟨notNew, squareOrPeriod⟩
  · cases empty
  · obtain ⟨rest, h⟩ := paren
    cases h
  · obtain ⟨rest, h⟩ := brace
    cases h
  · cases notNew

theorem new_array_call_follower (n : Nat) (tail : List Tok) :
    (Syn.new (arrayTypeFamily n)).prec = true ∧
      PostfixFollower true (.punct .lparen :: tail) :=
  ⟨(new_arrayTypeFamily_certified n).2, Or.inr (Or.inl ⟨tail, rfl⟩)⟩

theorem new_array_options_follower (n : Nat) (tail : List Tok) :
    (Syn.new (arrayTypeFamily n)).prec = true ∧
      PostfixFollower true (.punct .lbrace :: tail) :=
  ⟨(new_arrayTypeFamily_certified n).2, Or.inr (Or.inr (Or.inl ⟨tail, rfl⟩))⟩

end Solidity.Frontend.ExpressionUniqueness
