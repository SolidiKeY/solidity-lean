import Solidity.Frontend.ExpressionUniqueness.ExpressionUnaryFree
import Solidity.Frontend.ExpressionUniqueness.YieldSplit

/-!
# Unary root reconstruction and actual child spans

Prefix tokens select position zero. A certified suffix selects its final token
after a nonempty, high-root child word with no outer unary markers. Higher roots
have no such markers. All child words/layout executions come from actual yields.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def prefixToken : PrefixOp → Tok
  | .inc => .punct .inc | .dec => .punct .dec | .not => .punct .not
  | .bitNot => .punct .bitNot | .delete => .kw .delete | .neg => .punct .sub

theorem prefix_word_single (op : PrefixOp) : op.punct = [prefixToken op] := by
  cases op <;> rfl

theorem prefixToken_injective (op op' : PrefixOp) (h : prefixToken op = prefixToken op') : op = op' := by
  cases op <;> cases op' <;> cases h <;> rfl

theorem suffix_punct_injective (op op' : SuffixOp) (h : op.punct = op'.punct) : op = op' := by
  cases op <;> cases op' <;> cases h <;> rfl

def UnaryChildSpans (a b : Syn .expr) (initial rest initial' rest' : List Choice) : Prop :=
  ∃ xs ys, a.yield initial = some (xs, rest) ∧ b.yield initial' = some (ys, rest') ∧
    xs.flatten = ys.flatten

theorem prefix_child_spans (op op' : PrefixOp) (a b : Syn .expr)
    (initial rest initial' rest' : List Choice) (items items' : List (List Tok))
    (hy : (Syn.unaryPrefix op a).yield initial = some (items, rest))
    (hy' : (Syn.unaryPrefix op' b).yield initial' = some (items', rest'))
    (he : items.flatten = items'.flatten) :
    op = op' ∧ UnaryChildSpans a b initial rest initial' rest' := by
  obtain ⟨xs, hx, hi⟩ := prefix_yield_parts op a initial rest items hy
  obtain ⟨ys, hyb, hi'⟩ := prefix_yield_parts op' b initial' rest' items' hy'
  rw [hi, hi'] at he
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, prefix_word_single,
    List.singleton_append] at he
  obtain ⟨token, child⟩ := List.cons.inj he
  exact ⟨prefixToken_injective op op' token, xs, ys, hx, hyb, child⟩

theorem suffix_child_spans (op op' : SuffixOp) (a b : Syn .expr)
    (initial rest initial' rest' : List Choice) (items items' : List (List Tok))
    (hy : (Syn.unarySuffix op a).yield initial = some (items, rest))
    (hy' : (Syn.unarySuffix op' b).yield initial' = some (items', rest'))
    (he : items.flatten = items'.flatten) :
    op = op' ∧ UnaryChildSpans a b initial rest initial' rest' := by
  obtain ⟨xs, hx, hi⟩ := suffix_yield_parts op a initial rest items hy
  obtain ⟨ys, hyb, hi'⟩ := suffix_yield_parts op' b initial' rest' items' hy'
  rw [hi, hi'] at he
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, pu] at he
  have lengths : xs.flatten.length = ys.flatten.length := by
    have total := congrArg List.length he
    simp only [List.length_append, List.length_cons, List.length_nil] at total
    exact Nat.add_right_cancel total
  obtain ⟨child, token⟩ := List.append_inj he lengths
  exact ⟨suffix_punct_injective op op' (Tok.punct.inj (List.cons.inj token).1), xs, ys, hx, hyb, child⟩

theorem prefix_yield_firstUnary (op : PrefixOp) (a : Syn .expr)
    (initial rest : List Choice) (items : List (List Tok))
    (hy : (Syn.unaryPrefix op a).yield initial = some (items, rest)) :
    firstTop unaryMarker [] items.flatten = some (0, prefixToken op) := by
  obtain ⟨xs, hx, hi⟩ := prefix_yield_parts op a initial rest items hy
  rw [hi]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, prefix_word_single, List.singleton_append]
  cases op <;> rfl

theorem suffix_yield_firstUnary (op : SuffixOp) (a : Syn .expr)
    (initial rest : List Choice) (items : List (List Tok))
    (hp : (Syn.unarySuffix op a).prec = true)
    (hy : (Syn.unarySuffix op a).yield initial = some (items, rest)) :
    ∃ n, 0 < n ∧ firstTop unaryMarker [] items.flatten = some (n, .punct op.punct) := by
  have prec_a : a.prec = true := by
    apply all_prec_implies_prec a
    have hall : (Syn.unarySuffix op a).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have level_a : 15 ≤ a.level := of_decide_eq_true (Syn.prec_root hp)
  obtain ⟨xs, hx, hi⟩ := suffix_yield_parts op a initial rest items hy
  have free_a : UnaryFree xs.flatten := unaryFreeItems_flatten
    (high_expr_yield_unaryFree a prec_a level_a initial xs rest hx)
  have nonempty : xs.flatten ≠ [] := nonemptyItem_flatten (expr_yield_nonempty a initial xs rest hx)
  have marker : unaryMarker (.punct op.punct) = true := by cases op <;> rfl
  refine ⟨xs.flatten.length, List.length_pos_iff.mpr nonempty, ?_⟩
  rw [hi]
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, pu] using
    firstTop_marker unaryMarker xs.flatten [] (.punct op.punct) free_a marker

theorem high_yield_firstUnary_none (e : Syn .expr) (initial rest : List Choice) (items : List (List Tok))
    (hp : e.prec = true) (hl : 15 ≤ e.level) (hy : e.yield initial = some (items, rest)) :
    firstTop unaryMarker [] items.flatten = none :=
  firstTop_none_of_skip unaryMarker _
    (unaryFreeItems_flatten (high_expr_yield_unaryFree e hp hl initial items rest hy))

theorem suffix_higher_root_disjoint (op : SuffixOp) (a e : Syn .expr)
    (initial rest initial' rest' : List Choice) (items items' : List (List Tok))
    (hp : (Syn.unarySuffix op a).prec = true) (hp' : e.prec = true) (hl : 15 ≤ e.level)
    (hy : (Syn.unarySuffix op a).yield initial = some (items, rest))
    (hy' : e.yield initial' = some (items', rest')) : items.flatten ≠ items'.flatten := by
  intro words
  obtain ⟨n, positive, marker⟩ := suffix_yield_firstUnary op a initial rest items hp hy
  have absent := high_yield_firstUnary_none e initial' rest' items' hp' hl hy'
  rw [words, absent] at marker
  cases marker

theorem expr_level_fourteen_cases (e : Syn .expr) (hl : e.level = 14) :
    ∃ op a, e = Syn.unarySuffix op a := by
  cases e with
  | unarySuffix op a => exact ⟨op, a, rfl⟩
  | index => exact ((by decide : 15 ≠ 14) hl).elim
  | slice => exact ((by decide : 15 ≠ 14) hl).elim
  | member => exact ((by decide : 15 ≠ 14) hl).elim
  | callOptions => exact ((by decide : 15 ≠ 14) hl).elim
  | call => exact ((by decide : 15 ≠ 14) hl).elim
  | payableConv => exact ((by decide : 16 ≠ 14) hl).elim
  | metaType => exact ((by decide : 16 ≠ 14) hl).elim
  | unaryPrefix => exact ((by decide : 13 ≠ 14) hl).elim
  | exp => exact ((by decide : 12 ≠ 14) hl).elim
  | mulDivMod => exact ((by decide : 11 ≠ 14) hl).elim
  | addSub => exact ((by decide : 10 ≠ 14) hl).elim
  | shift => exact ((by decide : 9 ≠ 14) hl).elim
  | bitAnd => exact ((by decide : 8 ≠ 14) hl).elim
  | bitXor => exact ((by decide : 7 ≠ 14) hl).elim
  | bitOr => exact ((by decide : 6 ≠ 14) hl).elim
  | order => exact ((by decide : 5 ≠ 14) hl).elim
  | equality => exact ((by decide : 4 ≠ 14) hl).elim
  | and => exact ((by decide : 3 ≠ 14) hl).elim
  | or => exact ((by decide : 2 ≠ 14) hl).elim
  | cond => exact ((by decide : 1 ≠ 14) hl).elim
  | assign => exact ((by decide : 0 ≠ 14) hl).elim
  | new => exact ((by decide : 16 ≠ 14) hl).elim
  | tuple => exact ((by decide : 16 ≠ 14) hl).elim
  | inlineArray => exact ((by decide : 16 ≠ 14) hl).elim
  | ident => exact ((by decide : 16 ≠ 14) hl).elim
  | lit => exact ((by decide : 16 ≠ 14) hl).elim
  | litUnit => exact ((by decide : 16 ≠ 14) hl).elim
  | elemType => exact ((by decide : 16 ≠ 14) hl).elim

theorem prefix_higher_root_disjoint (op : PrefixOp) (a e : Syn .expr)
    (initial rest initial' rest' : List Choice) (items items' : List (List Tok))
    (hp' : e.prec = true) (hl : 14 ≤ e.level)
    (hy : (Syn.unaryPrefix op a).yield initial = some (items, rest))
    (hy' : e.yield initial' = some (items', rest')) : items.flatten ≠ items'.flatten := by
  intro words
  have marker := prefix_yield_firstUnary op a initial rest items hy
  rw [words] at marker
  by_cases equal : e.level = 14
  · obtain ⟨suffix, child, rfl⟩ := expr_level_fourteen_cases e equal
    obtain ⟨n, positive, selected⟩ := suffix_yield_firstUnary suffix child initial' rest' items' hp' hy'
    have zero : n = 0 := (Prod.mk.inj (Option.some.inj (selected.symm.trans marker))).1
    exact (Nat.ne_of_gt positive) zero
  · have higher : 15 ≤ e.level := by omega
    rw [high_yield_firstUnary_none e initial' rest' items' hp' higher hy'] at marker
    cases marker

end Solidity.Frontend.ExpressionUniqueness
