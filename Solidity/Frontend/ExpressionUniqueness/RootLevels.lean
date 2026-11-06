import Solidity.Frontend.ExpressionUniqueness.UnaryRoot
import Solidity.Frontend.ExpressionUniqueness.LayoutBoundary
import Solidity.Frontend.ExpressionUniqueness.AddRoot
import Solidity.Frontend.ExpressionUniqueness.LowRoot

/-!
# Original certified root levels agree through unary precedence

This combines loose, binary and unary root reconstruction. Successful partial
printer executions acquire genuine fully consumed Derives witnesses from the
layout theorem, so all existing certified root facts apply without a premise
that a child is separately printable. Only postfix15 versus primary16 remains
outside this root-level theorem; the original global target remains unchanged.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem expr_level_thirteen_cases (e : Syn .expr) (hl : e.level = 13) :
    ∃ op a, e = Syn.unaryPrefix op a := by
  cases e with
  | unaryPrefix op a => exact ⟨op, a, rfl⟩
  | index => exact ((by decide : 15 ≠ 13) hl).elim
  | slice => exact ((by decide : 15 ≠ 13) hl).elim
  | member => exact ((by decide : 15 ≠ 13) hl).elim
  | callOptions => exact ((by decide : 15 ≠ 13) hl).elim
  | call => exact ((by decide : 15 ≠ 13) hl).elim
  | payableConv => exact ((by decide : 16 ≠ 13) hl).elim
  | metaType => exact ((by decide : 16 ≠ 13) hl).elim
  | unarySuffix => exact ((by decide : 14 ≠ 13) hl).elim
  | exp => exact ((by decide : 12 ≠ 13) hl).elim
  | mulDivMod => exact ((by decide : 11 ≠ 13) hl).elim
  | addSub => exact ((by decide : 10 ≠ 13) hl).elim
  | shift => exact ((by decide : 9 ≠ 13) hl).elim
  | bitAnd => exact ((by decide : 8 ≠ 13) hl).elim
  | bitXor => exact ((by decide : 7 ≠ 13) hl).elim
  | bitOr => exact ((by decide : 6 ≠ 13) hl).elim
  | order => exact ((by decide : 5 ≠ 13) hl).elim
  | equality => exact ((by decide : 4 ≠ 13) hl).elim
  | and => exact ((by decide : 3 ≠ 13) hl).elim
  | or => exact ((by decide : 2 ≠ 13) hl).elim
  | cond => exact ((by decide : 1 ≠ 13) hl).elim
  | assign => exact ((by decide : 0 ≠ 13) hl).elim
  | new => exact ((by decide : 16 ≠ 13) hl).elim
  | tuple => exact ((by decide : 16 ≠ 13) hl).elim
  | inlineArray => exact ((by decide : 16 ≠ 13) hl).elim
  | ident => exact ((by decide : 16 ≠ 13) hl).elim
  | lit => exact ((by decide : 16 ≠ 13) hl).elim
  | litUnit => exact ((by decide : 16 ≠ 13) hl).elim
  | elemType => exact ((by decide : 16 ≠ 13) hl).elim

theorem loose_higher_root_disjoint (a b : Syn .expr) (ts : List Tok)
    (low : a.level < 2) (higher : a.level < b.level)
    (ha : a.prec = true) (hb : b.prec = true) (da : a.Derives ts) (db : b.Derives ts) : False := by
  by_cases high : 2 ≤ b.level
  · have absent : firstTop lowMarker [] ts = none := (certified_firstLow_none_iff b ts hb db).mpr high
    have impossible : 2 ≤ a.level := (certified_firstLow_none_iff a ts ha da).mp absent
    exact (Nat.not_le_of_lt low) impossible
  · rcases expr_level_below_two_cases a low with ⟨op, x, y, rfl⟩ | ⟨c, x, y, rfl⟩
    · rcases expr_level_below_two_cases b (Nat.lt_of_not_ge high) with
        ⟨op', u, v, rfl⟩ | ⟨c', u, v, rfl⟩
      · exact (Nat.lt_irrefl 0) higher
      · exact assignment_conditional_disjoint op x y c' u v ts ha hb da db
    · have lower : 1 < b.level := higher
      have upper : b.level < 2 := Nat.lt_of_not_ge high
      omega

theorem through_unary_higher_root_disjoint (a b : Syn .expr) (ts : List Tok)
    (bounded : a.level ≤ 14) (higher : a.level < b.level)
    (ha : a.prec = true) (hb : b.prec = true) (da : a.Derives ts) (db : b.Derives ts) : False := by
  by_cases low : a.level < 2
  · exact loose_higher_root_disjoint a b ts low higher ha hb da db
  by_cases binary : a.level ≤ 12
  · exact binary_higher_root_disjoint a b ts (Nat.le_of_not_gt low) binary higher ha hb da db
  by_cases thirteen : a.level = 13
  · obtain ⟨op, child, rfl⟩ := expr_level_thirteen_cases a thirteen
    obtain ⟨L, ht⟩ := da
    obtain ⟨L', ht'⟩ := db
    have atLeast : 14 ≤ b.level := higher
    exact prefix_higher_root_disjoint op child b L [] L' [] [ts] [ts] hb atLeast
      ((expr_toks_iff _ L ts).mp ht) ((expr_toks_iff _ L' ts).mp ht') rfl
  · have fourteen : a.level = 14 := by omega
    obtain ⟨op, child, rfl⟩ := expr_level_fourteen_cases a fourteen
    obtain ⟨L, ht⟩ := da
    obtain ⟨L', ht'⟩ := db
    have atLeast : 15 ≤ b.level := higher
    exact suffix_higher_root_disjoint op child b L [] L' [] [ts] [ts] ha hb atLeast
      ((expr_toks_iff _ L ts).mp ht) ((expr_toks_iff _ L' ts).mp ht') rfl

theorem certified_root_levels_equal_through_unary (a b : Syn .expr) (ts : List Tok)
    (bounded : a.level ≤ 14 ∨ b.level ≤ 14)
    (ha : a.prec = true) (hb : b.prec = true) (da : a.Derives ts) (db : b.Derives ts) :
    a.level = b.level := by
  rcases Nat.lt_trichotomy a.level b.level with less | equal | greater
  · have bound : a.level ≤ 14 := by rcases bounded with bound | bound <;> omega
    exact False.elim (through_unary_higher_root_disjoint a b ts bound less ha hb da db)
  · exact equal
  · have bound : b.level ≤ 14 := by rcases bounded with bound | bound <;> omega
    exact False.elim (through_unary_higher_root_disjoint b a ts bound greater hb ha db da)

theorem partial_root_levels_equal_through_unary (a b : Syn .expr)
    (initial rest initial' rest' : List Choice) (items items' : List (List Tok))
    (bounded : a.level ≤ 14 ∨ b.level ≤ 14) (ha : a.prec = true) (hb : b.prec = true)
    (hy : a.yield initial = some (items, rest)) (hy' : b.yield initial' = some (items', rest'))
    (words : items.flatten = items'.flatten) : a.level = b.level := by
  have da : a.Derives items.flatten := expression_partial_derives a initial rest items hy
  have db : b.Derives items.flatten := words ▸ expression_partial_derives b initial' rest' items' hy'
  exact certified_root_levels_equal_through_unary a b items.flatten bounded ha hb da db

end Solidity.Frontend.ExpressionUniqueness
