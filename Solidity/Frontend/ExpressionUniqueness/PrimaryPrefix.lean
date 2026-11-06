import Solidity.Frontend.ExpressionUniqueness.PrimaryStart

/-!
# Reconstruct the complete primary token prefix

The certificate supplies the follower through PrimarySpine. Every primary
constructor is covered, including literal/unit overlap at the first token.
This proves word cuts, not recursive tree identity.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem expr_level_sixteen_cases (e : Syn .expr) (hl : e.level = 16) :
    (∃ ty, e = Syn.new ty) ∨
    (∃ ty, e = Syn.metaType ty) ∨
    (∃ args, e = Syn.payableConv args) ∨
    (∃ first rest, e = Syn.tuple first rest) ∨
    (∃ first rest, e = Syn.inlineArray first rest) ∨
    (∃ name, e = Syn.ident name) ∨
    (∃ ty allowed, e = Syn.elemType ty allowed) ∨
    (∃ l, e = Syn.lit l) ∨
    (∃ n u, e = Syn.litUnit n u) := by
  cases e with
  | new ty => exact Or.inl ⟨ty, rfl⟩
  | metaType ty => exact Or.inr (Or.inl ⟨ty, rfl⟩)
  | payableConv args => exact Or.inr (Or.inr (Or.inl ⟨args, rfl⟩))
  | tuple first rest => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨first, rest, rfl⟩)))
  | inlineArray first rest => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨first, rest, rfl⟩))))
  | ident name => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨name, rfl⟩)))))
  | elemType ty allowed => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ty, allowed, rfl⟩))))))
  | lit l => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨l, rfl⟩)))))))
  | litUnit n u => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨n, u, rfl⟩))))))))
  | index => exact ((by decide : 15 ≠ 16) hl).elim
  | slice => exact ((by decide : 15 ≠ 16) hl).elim
  | member => exact ((by decide : 15 ≠ 16) hl).elim
  | callOptions => exact ((by decide : 15 ≠ 16) hl).elim
  | call => exact ((by decide : 15 ≠ 16) hl).elim
  | unaryPrefix => exact ((by decide : 13 ≠ 16) hl).elim
  | unarySuffix => exact ((by decide : 14 ≠ 16) hl).elim
  | exp => exact ((by decide : 12 ≠ 16) hl).elim
  | mulDivMod => exact ((by decide : 11 ≠ 16) hl).elim
  | addSub => exact ((by decide : 10 ≠ 16) hl).elim
  | shift => exact ((by decide : 9 ≠ 16) hl).elim
  | bitAnd => exact ((by decide : 8 ≠ 16) hl).elim
  | bitXor => exact ((by decide : 7 ≠ 16) hl).elim
  | bitOr => exact ((by decide : 6 ≠ 16) hl).elim
  | order => exact ((by decide : 5 ≠ 16) hl).elim
  | equality => exact ((by decide : 4 ≠ 16) hl).elim
  | and => exact ((by decide : 3 ≠ 16) hl).elim
  | or => exact ((by decide : 2 ≠ 16) hl).elim
  | cond => exact ((by decide : 1 ≠ 16) hl).elim
  | assign => exact ((by decide : 0 ≠ 16) hl).elim

theorem primary_yield_prefix_unique (a b : Syn .expr)
    (initial final initial' final' : List Choice) (items items' : List (List Tok)) (tail tail' : List Tok)
    (ha : a.level = 16) (hb : b.level = 16)
    (fa : PostfixFollower a.isNew tail) (fb : PostfixFollower b.isNew tail')
    (hy : a.yield initial = some (items, final)) (hy' : b.yield initial' = some (items', final'))
    (words : items.flatten ++ tail = items'.flatten ++ tail') :
    items.flatten = items'.flatten ∧ tail = tail' := by
  have kinds : primaryRootKind a = primaryRootKind b :=
    primary_prefix_kinds_equal a b initial final initial' final' items items' tail tail' ha hb hy hy' words
  rcases expr_level_sixteen_cases a ha with
    ⟨tya, rfl⟩ | ⟨tya, rfl⟩ | ⟨argsa, rfl⟩ | ⟨firsta, resta, rfl⟩ | ⟨firsta, resta, rfl⟩ | ⟨namea, rfl⟩ | ⟨tya, alloweda, rfl⟩ | ⟨la, rfl⟩ | ⟨na, ua, rfl⟩
    <;> rcases expr_level_sixteen_cases b hb with
    ⟨tyb, rfl⟩ | ⟨tyb, rfl⟩ | ⟨argsb, rfl⟩ | ⟨firstb, restb, rfl⟩ | ⟨firstb, restb, rfl⟩ | ⟨nameb, rfl⟩ | ⟨tyb, allowedb, rfl⟩ | ⟨lb, rfl⟩ | ⟨nb, ub, rfl⟩
    <;> simp only [primaryRootKind, Syn.ctor] at kinds
    <;> try cases kinds
  all_goals first
    | exact new_yield_prefix_unique _ _ initial final initial' final' items items' tail tail' fa fb hy hy' words
    | exact meta_yield_prefix_unique _ _ initial final initial' final' items items' tail tail' hy hy' words
    | exact payable_yield_prefix_unique _ _ initial final initial' final' items items' tail tail' hy hy' words
    | exact tuple_yield_prefix_unique _ _ _ _ initial final initial' final' items items' tail tail' hy hy' words
    | exact inline_yield_prefix_unique _ _ _ _ initial final initial' final' items items' tail tail' hy hy' words
    | exact ident_yield_prefix_unique _ _ initial final initial' final' items items' tail tail' hy hy' words
    | exact elem_expr_yield_prefix_unique _ _ _ _ initial final initial' final' items items' tail tail' hy hy' words
    | exact literal_yield_prefix_unique _ _ initial final initial' final' items items' tail tail' fa fb hy hy' words
    | exact unit_yield_prefix_unique _ _ _ _ initial final initial' final' items items' tail tail' hy hy' words
    | exact (literal_unit_prefix_disjoint _ _ _ initial final initial' final' items items' tail tail' fa hy hy' words).elim
    | exact (literal_unit_prefix_disjoint _ _ _ initial' final' initial final items' items tail' tail fb hy' hy words.symm).elim

end Solidity.Frontend.ExpressionUniqueness
