import Solidity.Frontend.ExpressionUniqueness.PrimaryPrefix
import Solidity.Frontend.ExpressionUniqueness.PrimarySpine
import Solidity.Frontend.ExpressionUniqueness.RootLevels

/-!
# Reconstruct every certified expression precedence level

The final level-15/16 boundary follows from the primary spine and the actual
primary prefix cut. No root split or uniqueness premise is introduced.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem expression_level_bound (e : Syn .expr) : e.level ≤ 16 := by
  cases e with
  | index => exact (by decide : 15 ≤ 16)
  | slice => exact (by decide : 15 ≤ 16)
  | member => exact (by decide : 15 ≤ 16)
  | callOptions => exact (by decide : 15 ≤ 16)
  | call => exact (by decide : 15 ≤ 16)
  | unaryPrefix => exact (by decide : 13 ≤ 16)
  | unarySuffix => exact (by decide : 14 ≤ 16)
  | exp => exact (by decide : 12 ≤ 16)
  | mulDivMod => exact (by decide : 11 ≤ 16)
  | addSub => exact (by decide : 10 ≤ 16)
  | shift => exact (by decide : 9 ≤ 16)
  | bitAnd => exact (by decide : 8 ≤ 16)
  | bitXor => exact (by decide : 7 ≤ 16)
  | bitOr => exact (by decide : 6 ≤ 16)
  | order => exact (by decide : 5 ≤ 16)
  | equality => exact (by decide : 4 ≤ 16)
  | and => exact (by decide : 3 ≤ 16)
  | or => exact (by decide : 2 ≤ 16)
  | cond => exact (by decide : 1 ≤ 16)
  | assign => exact (by decide : 0 ≤ 16)
  | new => exact (by decide : 16 ≤ 16)
  | metaType => exact (by decide : 16 ≤ 16)
  | payableConv => exact (by decide : 16 ≤ 16)
  | tuple => exact (by decide : 16 ≤ 16)
  | inlineArray => exact (by decide : 16 ≤ 16)
  | ident => exact (by decide : 16 ≤ 16)
  | lit => exact (by decide : 16 ≤ 16)
  | litUnit => exact (by decide : 16 ≤ 16)
  | elemType => exact (by decide : 16 ≤ 16)

theorem postfix_primary_yield_disjoint (a b : Syn .expr)
    (initial final initial' final' : List Choice) (items items' : List (List Tok))
    (ha : a.prec = true) (_hb : b.prec = true) (la : a.level = 15) (lb : b.level = 16)
    (hy : a.yield initial = some (items, final)) (hy' : b.yield initial' = some (items', final')) :
    items.flatten ≠ items'.flatten := by
  intro words
  obtain ⟨primary, ps, pf, suffix, lp, hp, hyp, shape, follower, noFrames⟩ :=
    high_expr_primary_spine a initial final items ha (by omega) hy
  have prefixWords : ps.flatten ++ suffix = items'.flatten ++ [] := by
    rw [List.append_nil, ← shape, words]
  have cuts : ps.flatten = items'.flatten ∧ suffix = [] :=
    primary_yield_prefix_unique primary b initial pf initial' final' ps items' suffix []
      lp lb follower (postfixFollower_nil _) hyp hy' prefixWords
  have tree : a = primary := noFrames cuts.2
  have levels : a.level = 16 := tree ▸ lp
  omega

theorem partial_root_levels_equal (a b : Syn .expr)
    (initial final initial' final' : List Choice) (items items' : List (List Tok))
    (ha : a.prec = true) (hb : b.prec = true)
    (hy : a.yield initial = some (items, final)) (hy' : b.yield initial' = some (items', final'))
    (words : items.flatten = items'.flatten) : a.level = b.level := by
  by_cases low : a.level ≤ 14 ∨ b.level ≤ 14
  · exact partial_root_levels_equal_through_unary a b initial final initial' final' items items' low ha hb hy hy' words
  · have ba : a.level ≤ 16 := expression_level_bound a
    have bb : b.level ≤ 16 := expression_level_bound b
    have aa : a.level = 15 ∨ a.level = 16 := by omega
    have ab : b.level = 15 ∨ b.level = 16 := by omega
    rcases aa with aa | aa <;> rcases ab with ab | ab
    · exact aa.trans ab.symm
    · exact (postfix_primary_yield_disjoint a b initial final initial' final' items items' ha hb aa ab hy hy' words).elim
    · exact (postfix_primary_yield_disjoint b a initial' final' initial final items' items hb ha ab aa hy' hy words.symm).elim
    · exact aa.trans ab.symm

theorem certified_root_levels_equal (a b : Syn .expr) (ts : List Tok)
    (ha : a.prec = true) (hb : b.prec = true) (da : a.Derives ts) (db : b.Derives ts) :
    a.level = b.level := by
  obtain ⟨initial, h⟩ := da
  obtain ⟨initial', h'⟩ := db
  exact partial_root_levels_equal a b initial [] initial' [] [ts] [ts] ha hb
    ((expr_toks_iff _ initial ts).mp h) ((expr_toks_iff _ initial' ts).mp h') rfl

end Solidity.Frontend.ExpressionUniqueness
