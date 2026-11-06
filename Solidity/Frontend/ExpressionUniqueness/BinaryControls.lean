import Solidity.Frontend.ExpressionUniqueness.BinaryRank
import Solidity.Frontend.ExpressionUniqueness.Families

/-!
# Rank-ten raw-marker limitation is an inhabited arbitrary-family control

This is a countercontrol to applying the raw-marker helper at prefix minus,
not an ambiguity of certified expression trees. The original rank-ten uniqueness
obligation remains unchanged. Grouping shields every prefix marker as expected.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem successor_prefix_not_binary_ten_free (n : Nat) (name : String) :
    ¬ BinaryFree 10 (negTokens (n + 1) name) := by
  intro h
  change none = some [] at h
  cases h

theorem rank_ten_prefix_countercontrol (n : Nat) (name : String) :
    (negFamily (n + 1) name).Derives (negTokens (n + 1) name) ∧
    (negFamily (n + 1) name).prec = true ∧ ¬ BinaryFree 10 (negTokens (n + 1) name) :=
  ⟨(negFamily_certified (n + 1) name).1, (negFamily_certified (n + 1) name).2,
    successor_prefix_not_binary_ten_free n name⟩

theorem grouped_prefix_binary_ten_free (n : Nat) (name : String) :
    BinaryFree 10 (parens (negTokens n name)) :=
  binaryFree_parens (expr_derives_balanced (negFamily n name) (negTokens n name)
    (negFamily_certified n name).1)

end Solidity.Frontend.ExpressionUniqueness
