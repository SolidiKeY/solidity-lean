import Solidity.Frontend.ExpressionUniqueness.YieldSplit
import Solidity.Frontend.ExpressionUniqueness.AddRoot
import Solidity.Frontend.ExpressionUniqueness.LowRoot

/-!
# Recover binary child words from actual certified printer executions

Layouts may differ independently, and may have unconsumed suffixes. The child
executions and both token spans are conclusions derived from the original
printer and recursive precedence certificate. No desired root cut is assumed.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def BinaryChildSpans (a b c d : Syn .expr)
    (initial rest initial' rest' : List Choice) : Prop :=
  ∃ xs ys xs' ys' middle middle',
    a.yield initial = some (xs, middle) ∧ b.yield middle = some (ys, rest) ∧
    c.yield initial' = some (xs', middle') ∧ d.yield middle' = some (ys', rest') ∧
    xs.flatten = xs'.flatten ∧ ys.flatten = ys'.flatten

theorem mul_child_spans (op op' : MulOp) (a b c d : Syn .expr)
    (initial rest initial' rest' : List Choice) (items items' : List (List Tok))
    (hp : (Syn.mulDivMod op a b).prec = true) (hp' : (Syn.mulDivMod op' c d).prec = true)
    (hy : (Syn.mulDivMod op a b).yield initial = some (items, rest))
    (hy' : (Syn.mulDivMod op' c d).yield initial' = some (items', rest'))
    (heq : items.flatten = items'.flatten) :
    op = op' ∧ BinaryChildSpans a b c d initial rest initial' rest' := by
  have prec_b : b.prec = true := by
    apply all_prec_implies_prec b
    have hall : (Syn.mulDivMod op a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have level_b : 11 < b.level := by
    have hr : (Syn.mulDivMod op a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 11 < 12) hr.2
  have prec_d : d.prec = true := by
    apply all_prec_implies_prec d
    have hall : (Syn.mulDivMod op' c d).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp').2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have level_d : 11 < d.level := by
    have hr : (Syn.mulDivMod op' c d).precNode = true := Syn.prec_root hp'
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 11 < 12) hr.2
  obtain ⟨xs, ys, middle, hx, hyb, hi⟩ := mul_yield_parts op a b initial rest items hy
  obtain ⟨xs', ys', middle', hx', hyd, hi'⟩ := mul_yield_parts op' c d initial' rest' items' hy'
  have free_b : BinaryFree 11 ys.flatten := binaryFreeItems_flatten
    (high_expr_yield_binaryFree 11 (by decide) (by decide) b prec_b level_b middle ys rest hyb)
  have free_d : BinaryFree 11 ys'.flatten := binaryFreeItems_flatten
    (high_expr_yield_binaryFree 11 (by decide) (by decide) d prec_d level_d middle' ys' rest' hyd)
  have token : binaryMarker 11 (.punct op.punct) = true := by cases op <;> rfl
  have token' : binaryMarker 11 (.punct op'.punct) = true := by cases op' <;> rfl
  rw [hi, hi'] at heq
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] at heq
  obtain ⟨left, operator, right⟩ := lastTop_cut_unique (binaryMarker 11) (binaryMarker_atomic 11)
    xs.flatten ys.flatten xs'.flatten ys'.flatten (.punct op.punct) (.punct op'.punct)
    free_b free_d token token' heq
  refine ⟨mul_punct_injective op op' (Tok.punct.inj operator), ?_⟩
  exact ⟨xs, ys, xs', ys', middle, middle', hx, hyb, hx', hyd, left, right⟩

theorem shift_child_spans (op op' : ShiftOp) (a b c d : Syn .expr)
    (initial rest initial' rest' : List Choice) (items items' : List (List Tok))
    (hp : (Syn.shift op a b).prec = true) (hp' : (Syn.shift op' c d).prec = true)
    (hy : (Syn.shift op a b).yield initial = some (items, rest))
    (hy' : (Syn.shift op' c d).yield initial' = some (items', rest'))
    (heq : items.flatten = items'.flatten) :
    op = op' ∧ BinaryChildSpans a b c d initial rest initial' rest' := by
  have prec_b : b.prec = true := by
    apply all_prec_implies_prec b
    have hall : (Syn.shift op a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have level_b : 9 < b.level := by
    have hr : (Syn.shift op a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 9 < 10) hr.2
  have prec_d : d.prec = true := by
    apply all_prec_implies_prec d
    have hall : (Syn.shift op' c d).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp').2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have level_d : 9 < d.level := by
    have hr : (Syn.shift op' c d).precNode = true := Syn.prec_root hp'
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 9 < 10) hr.2
  obtain ⟨xs, ys, middle, hx, hyb, hi⟩ := shift_yield_parts op a b initial rest items hy
  obtain ⟨xs', ys', middle', hx', hyd, hi'⟩ := shift_yield_parts op' c d initial' rest' items' hy'
  have free_b : BinaryFree 9 ys.flatten := binaryFreeItems_flatten
    (high_expr_yield_binaryFree 9 (by decide) (by decide) b prec_b level_b middle ys rest hyb)
  have free_d : BinaryFree 9 ys'.flatten := binaryFreeItems_flatten
    (high_expr_yield_binaryFree 9 (by decide) (by decide) d prec_d level_d middle' ys' rest' hyd)
  have token : binaryMarker 9 (.punct op.punct) = true := by cases op <;> rfl
  have token' : binaryMarker 9 (.punct op'.punct) = true := by cases op' <;> rfl
  rw [hi, hi'] at heq
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] at heq
  obtain ⟨left, operator, right⟩ := lastTop_cut_unique (binaryMarker 9) (binaryMarker_atomic 9)
    xs.flatten ys.flatten xs'.flatten ys'.flatten (.punct op.punct) (.punct op'.punct)
    free_b free_d token token' heq
  refine ⟨shift_punct_injective op op' (Tok.punct.inj operator), ?_⟩
  exact ⟨xs, ys, xs', ys', middle, middle', hx, hyb, hx', hyd, left, right⟩

theorem order_child_spans (op op' : OrderOp) (a b c d : Syn .expr)
    (initial rest initial' rest' : List Choice) (items items' : List (List Tok))
    (hp : (Syn.order op a b).prec = true) (hp' : (Syn.order op' c d).prec = true)
    (hy : (Syn.order op a b).yield initial = some (items, rest))
    (hy' : (Syn.order op' c d).yield initial' = some (items', rest'))
    (heq : items.flatten = items'.flatten) :
    op = op' ∧ BinaryChildSpans a b c d initial rest initial' rest' := by
  have prec_b : b.prec = true := by
    apply all_prec_implies_prec b
    have hall : (Syn.order op a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have level_b : 5 < b.level := by
    have hr : (Syn.order op a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 5 < 6) hr.2
  have prec_d : d.prec = true := by
    apply all_prec_implies_prec d
    have hall : (Syn.order op' c d).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp').2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have level_d : 5 < d.level := by
    have hr : (Syn.order op' c d).precNode = true := Syn.prec_root hp'
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 5 < 6) hr.2
  obtain ⟨xs, ys, middle, hx, hyb, hi⟩ := order_yield_parts op a b initial rest items hy
  obtain ⟨xs', ys', middle', hx', hyd, hi'⟩ := order_yield_parts op' c d initial' rest' items' hy'
  have free_b : BinaryFree 5 ys.flatten := binaryFreeItems_flatten
    (high_expr_yield_binaryFree 5 (by decide) (by decide) b prec_b level_b middle ys rest hyb)
  have free_d : BinaryFree 5 ys'.flatten := binaryFreeItems_flatten
    (high_expr_yield_binaryFree 5 (by decide) (by decide) d prec_d level_d middle' ys' rest' hyd)
  have token : binaryMarker 5 (.punct op.punct) = true := by cases op <;> rfl
  have token' : binaryMarker 5 (.punct op'.punct) = true := by cases op' <;> rfl
  rw [hi, hi'] at heq
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] at heq
  obtain ⟨left, operator, right⟩ := lastTop_cut_unique (binaryMarker 5) (binaryMarker_atomic 5)
    xs.flatten ys.flatten xs'.flatten ys'.flatten (.punct op.punct) (.punct op'.punct)
    free_b free_d token token' heq
  refine ⟨order_punct_injective op op' (Tok.punct.inj operator), ?_⟩
  exact ⟨xs, ys, xs', ys', middle, middle', hx, hyb, hx', hyd, left, right⟩

theorem equality_child_spans (op op' : EqOp) (a b c d : Syn .expr)
    (initial rest initial' rest' : List Choice) (items items' : List (List Tok))
    (hp : (Syn.equality op a b).prec = true) (hp' : (Syn.equality op' c d).prec = true)
    (hy : (Syn.equality op a b).yield initial = some (items, rest))
    (hy' : (Syn.equality op' c d).yield initial' = some (items', rest'))
    (heq : items.flatten = items'.flatten) :
    op = op' ∧ BinaryChildSpans a b c d initial rest initial' rest' := by
  have prec_b : b.prec = true := by
    apply all_prec_implies_prec b
    have hall : (Syn.equality op a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have level_b : 4 < b.level := by
    have hr : (Syn.equality op a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 4 < 5) hr.2
  have prec_d : d.prec = true := by
    apply all_prec_implies_prec d
    have hall : (Syn.equality op' c d).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp').2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have level_d : 4 < d.level := by
    have hr : (Syn.equality op' c d).precNode = true := Syn.prec_root hp'
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 4 < 5) hr.2
  obtain ⟨xs, ys, middle, hx, hyb, hi⟩ := equality_yield_parts op a b initial rest items hy
  obtain ⟨xs', ys', middle', hx', hyd, hi'⟩ := equality_yield_parts op' c d initial' rest' items' hy'
  have free_b : BinaryFree 4 ys.flatten := binaryFreeItems_flatten
    (high_expr_yield_binaryFree 4 (by decide) (by decide) b prec_b level_b middle ys rest hyb)
  have free_d : BinaryFree 4 ys'.flatten := binaryFreeItems_flatten
    (high_expr_yield_binaryFree 4 (by decide) (by decide) d prec_d level_d middle' ys' rest' hyd)
  have token : binaryMarker 4 (.punct op.punct) = true := by cases op <;> rfl
  have token' : binaryMarker 4 (.punct op'.punct) = true := by cases op' <;> rfl
  rw [hi, hi'] at heq
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] at heq
  obtain ⟨left, operator, right⟩ := lastTop_cut_unique (binaryMarker 4) (binaryMarker_atomic 4)
    xs.flatten ys.flatten xs'.flatten ys'.flatten (.punct op.punct) (.punct op'.punct)
    free_b free_d token token' heq
  refine ⟨equality_punct_injective op op' (Tok.punct.inj operator), ?_⟩
  exact ⟨xs, ys, xs', ys', middle, middle', hx, hyb, hx', hyd, left, right⟩

theorem bitAnd_child_spans (a b c d : Syn .expr)
    (initial rest initial' rest' : List Choice) (items items' : List (List Tok))
    (hp : (Syn.bitAnd a b).prec = true) (hp' : (Syn.bitAnd c d).prec = true)
    (hy : (Syn.bitAnd a b).yield initial = some (items, rest))
    (hy' : (Syn.bitAnd c d).yield initial' = some (items', rest'))
    (heq : items.flatten = items'.flatten) :
    BinaryChildSpans a b c d initial rest initial' rest' := by
  have prec_b : b.prec = true := by
    apply all_prec_implies_prec b
    have hall : (Syn.bitAnd a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have level_b : 8 < b.level := by
    have hr : (Syn.bitAnd a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 8 < 9) hr.2
  have prec_d : d.prec = true := by
    apply all_prec_implies_prec d
    have hall : (Syn.bitAnd c d).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp').2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have level_d : 8 < d.level := by
    have hr : (Syn.bitAnd c d).precNode = true := Syn.prec_root hp'
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 8 < 9) hr.2
  obtain ⟨xs, ys, middle, hx, hyb, hi⟩ := bitAnd_yield_parts a b initial rest items hy
  obtain ⟨xs', ys', middle', hx', hyd, hi'⟩ := bitAnd_yield_parts c d initial' rest' items' hy'
  have free_b : BinaryFree 8 ys.flatten := binaryFreeItems_flatten
    (high_expr_yield_binaryFree 8 (by decide) (by decide) b prec_b level_b middle ys rest hyb)
  have free_d : BinaryFree 8 ys'.flatten := binaryFreeItems_flatten
    (high_expr_yield_binaryFree 8 (by decide) (by decide) d prec_d level_d middle' ys' rest' hyd)
  have token : binaryMarker 8 (.punct .bitAnd) = true := by rfl
  have token' : binaryMarker 8 (.punct .bitAnd) = true := by rfl
  rw [hi, hi'] at heq
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] at heq
  obtain ⟨left, operator, right⟩ := lastTop_cut_unique (binaryMarker 8) (binaryMarker_atomic 8)
    xs.flatten ys.flatten xs'.flatten ys'.flatten (.punct .bitAnd) (.punct .bitAnd)
    free_b free_d token token' heq
  exact ⟨xs, ys, xs', ys', middle, middle', hx, hyb, hx', hyd, left, right⟩

theorem bitXor_child_spans (a b c d : Syn .expr)
    (initial rest initial' rest' : List Choice) (items items' : List (List Tok))
    (hp : (Syn.bitXor a b).prec = true) (hp' : (Syn.bitXor c d).prec = true)
    (hy : (Syn.bitXor a b).yield initial = some (items, rest))
    (hy' : (Syn.bitXor c d).yield initial' = some (items', rest'))
    (heq : items.flatten = items'.flatten) :
    BinaryChildSpans a b c d initial rest initial' rest' := by
  have prec_b : b.prec = true := by
    apply all_prec_implies_prec b
    have hall : (Syn.bitXor a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have level_b : 7 < b.level := by
    have hr : (Syn.bitXor a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 7 < 8) hr.2
  have prec_d : d.prec = true := by
    apply all_prec_implies_prec d
    have hall : (Syn.bitXor c d).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp').2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have level_d : 7 < d.level := by
    have hr : (Syn.bitXor c d).precNode = true := Syn.prec_root hp'
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 7 < 8) hr.2
  obtain ⟨xs, ys, middle, hx, hyb, hi⟩ := bitXor_yield_parts a b initial rest items hy
  obtain ⟨xs', ys', middle', hx', hyd, hi'⟩ := bitXor_yield_parts c d initial' rest' items' hy'
  have free_b : BinaryFree 7 ys.flatten := binaryFreeItems_flatten
    (high_expr_yield_binaryFree 7 (by decide) (by decide) b prec_b level_b middle ys rest hyb)
  have free_d : BinaryFree 7 ys'.flatten := binaryFreeItems_flatten
    (high_expr_yield_binaryFree 7 (by decide) (by decide) d prec_d level_d middle' ys' rest' hyd)
  have token : binaryMarker 7 (.punct .bitXor) = true := by rfl
  have token' : binaryMarker 7 (.punct .bitXor) = true := by rfl
  rw [hi, hi'] at heq
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] at heq
  obtain ⟨left, operator, right⟩ := lastTop_cut_unique (binaryMarker 7) (binaryMarker_atomic 7)
    xs.flatten ys.flatten xs'.flatten ys'.flatten (.punct .bitXor) (.punct .bitXor)
    free_b free_d token token' heq
  exact ⟨xs, ys, xs', ys', middle, middle', hx, hyb, hx', hyd, left, right⟩

theorem bitOr_child_spans (a b c d : Syn .expr)
    (initial rest initial' rest' : List Choice) (items items' : List (List Tok))
    (hp : (Syn.bitOr a b).prec = true) (hp' : (Syn.bitOr c d).prec = true)
    (hy : (Syn.bitOr a b).yield initial = some (items, rest))
    (hy' : (Syn.bitOr c d).yield initial' = some (items', rest'))
    (heq : items.flatten = items'.flatten) :
    BinaryChildSpans a b c d initial rest initial' rest' := by
  have prec_b : b.prec = true := by
    apply all_prec_implies_prec b
    have hall : (Syn.bitOr a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have level_b : 6 < b.level := by
    have hr : (Syn.bitOr a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 6 < 7) hr.2
  have prec_d : d.prec = true := by
    apply all_prec_implies_prec d
    have hall : (Syn.bitOr c d).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp').2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have level_d : 6 < d.level := by
    have hr : (Syn.bitOr c d).precNode = true := Syn.prec_root hp'
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 6 < 7) hr.2
  obtain ⟨xs, ys, middle, hx, hyb, hi⟩ := bitOr_yield_parts a b initial rest items hy
  obtain ⟨xs', ys', middle', hx', hyd, hi'⟩ := bitOr_yield_parts c d initial' rest' items' hy'
  have free_b : BinaryFree 6 ys.flatten := binaryFreeItems_flatten
    (high_expr_yield_binaryFree 6 (by decide) (by decide) b prec_b level_b middle ys rest hyb)
  have free_d : BinaryFree 6 ys'.flatten := binaryFreeItems_flatten
    (high_expr_yield_binaryFree 6 (by decide) (by decide) d prec_d level_d middle' ys' rest' hyd)
  have token : binaryMarker 6 (.punct .bitOr) = true := by rfl
  have token' : binaryMarker 6 (.punct .bitOr) = true := by rfl
  rw [hi, hi'] at heq
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] at heq
  obtain ⟨left, operator, right⟩ := lastTop_cut_unique (binaryMarker 6) (binaryMarker_atomic 6)
    xs.flatten ys.flatten xs'.flatten ys'.flatten (.punct .bitOr) (.punct .bitOr)
    free_b free_d token token' heq
  exact ⟨xs, ys, xs', ys', middle, middle', hx, hyb, hx', hyd, left, right⟩

theorem and_child_spans (a b c d : Syn .expr)
    (initial rest initial' rest' : List Choice) (items items' : List (List Tok))
    (hp : (Syn.and a b).prec = true) (hp' : (Syn.and c d).prec = true)
    (hy : (Syn.and a b).yield initial = some (items, rest))
    (hy' : (Syn.and c d).yield initial' = some (items', rest'))
    (heq : items.flatten = items'.flatten) :
    BinaryChildSpans a b c d initial rest initial' rest' := by
  have prec_b : b.prec = true := by
    apply all_prec_implies_prec b
    have hall : (Syn.and a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have level_b : 3 < b.level := by
    have hr : (Syn.and a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 3 < 4) hr.2
  have prec_d : d.prec = true := by
    apply all_prec_implies_prec d
    have hall : (Syn.and c d).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp').2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have level_d : 3 < d.level := by
    have hr : (Syn.and c d).precNode = true := Syn.prec_root hp'
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 3 < 4) hr.2
  obtain ⟨xs, ys, middle, hx, hyb, hi⟩ := and_yield_parts a b initial rest items hy
  obtain ⟨xs', ys', middle', hx', hyd, hi'⟩ := and_yield_parts c d initial' rest' items' hy'
  have free_b : BinaryFree 3 ys.flatten := binaryFreeItems_flatten
    (high_expr_yield_binaryFree 3 (by decide) (by decide) b prec_b level_b middle ys rest hyb)
  have free_d : BinaryFree 3 ys'.flatten := binaryFreeItems_flatten
    (high_expr_yield_binaryFree 3 (by decide) (by decide) d prec_d level_d middle' ys' rest' hyd)
  have token : binaryMarker 3 (.punct .and) = true := by rfl
  have token' : binaryMarker 3 (.punct .and) = true := by rfl
  rw [hi, hi'] at heq
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] at heq
  obtain ⟨left, operator, right⟩ := lastTop_cut_unique (binaryMarker 3) (binaryMarker_atomic 3)
    xs.flatten ys.flatten xs'.flatten ys'.flatten (.punct .and) (.punct .and)
    free_b free_d token token' heq
  exact ⟨xs, ys, xs', ys', middle, middle', hx, hyb, hx', hyd, left, right⟩

theorem or_child_spans (a b c d : Syn .expr)
    (initial rest initial' rest' : List Choice) (items items' : List (List Tok))
    (hp : (Syn.or a b).prec = true) (hp' : (Syn.or c d).prec = true)
    (hy : (Syn.or a b).yield initial = some (items, rest))
    (hy' : (Syn.or c d).yield initial' = some (items', rest'))
    (heq : items.flatten = items'.flatten) :
    BinaryChildSpans a b c d initial rest initial' rest' := by
  have prec_b : b.prec = true := by
    apply all_prec_implies_prec b
    have hall : (Syn.or a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have level_b : 2 < b.level := by
    have hr : (Syn.or a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 2 < 3) hr.2
  have prec_d : d.prec = true := by
    apply all_prec_implies_prec d
    have hall : (Syn.or c d).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp').2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have level_d : 2 < d.level := by
    have hr : (Syn.or c d).precNode = true := Syn.prec_root hp'
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 2 < 3) hr.2
  obtain ⟨xs, ys, middle, hx, hyb, hi⟩ := or_yield_parts a b initial rest items hy
  obtain ⟨xs', ys', middle', hx', hyd, hi'⟩ := or_yield_parts c d initial' rest' items' hy'
  have free_b : BinaryFree 2 ys.flatten := binaryFreeItems_flatten
    (high_expr_yield_binaryFree 2 (by decide) (by decide) b prec_b level_b middle ys rest hyb)
  have free_d : BinaryFree 2 ys'.flatten := binaryFreeItems_flatten
    (high_expr_yield_binaryFree 2 (by decide) (by decide) d prec_d level_d middle' ys' rest' hyd)
  have token : binaryMarker 2 (.punct .or) = true := by rfl
  have token' : binaryMarker 2 (.punct .or) = true := by rfl
  rw [hi, hi'] at heq
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] at heq
  obtain ⟨left, operator, right⟩ := lastTop_cut_unique (binaryMarker 2) (binaryMarker_atomic 2)
    xs.flatten ys.flatten xs'.flatten ys'.flatten (.punct .or) (.punct .or)
    free_b free_d token token' heq
  exact ⟨xs, ys, xs', ys', middle, middle', hx, hyb, hx', hyd, left, right⟩

theorem add_child_spans (op op' : AddOp) (a b c d : Syn .expr)
    (initial rest initial' rest' : List Choice) (items items' : List (List Tok))
    (hp : (Syn.addSub op a b).prec = true) (hp' : (Syn.addSub op' c d).prec = true)
    (hy : (Syn.addSub op a b).yield initial = some (items, rest))
    (hy' : (Syn.addSub op' c d).yield initial' = some (items', rest'))
    (heq : items.flatten = items'.flatten) :
    op = op' ∧ BinaryChildSpans a b c d initial rest initial' rest' := by
  have prec_b : b.prec = true := by
    apply all_prec_implies_prec b
    have hall : (Syn.addSub op a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have level_b : 10 < b.level := by
    have hr : (Syn.addSub op a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 10 < 11) hr.2
  have prec_d : d.prec = true := by
    apply all_prec_implies_prec d
    have hall : (Syn.addSub op' c d).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp').2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have level_d : 10 < d.level := by
    have hr : (Syn.addSub op' c d).precNode = true := Syn.prec_root hp'
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 10 < 11) hr.2
  obtain ⟨xs, ys, middle, hx, hyb, hi⟩ := add_yield_parts op a b initial rest items hy
  obtain ⟨xs', ys', middle', hx', hyd, hi'⟩ := add_yield_parts op' c d initial' rest' items' hy'
  have done_a : ModeDone xs.flatten := expr_yield_modeDone a initial xs middle hx
  have done_c : ModeDone xs'.flatten := expr_yield_modeDone c initial' xs' middle' hx'
  have free_b : AddFree ys.flatten := high_expr_yield_addFree b prec_b level_b middle ys rest hyb
  have free_d : AddFree ys'.flatten := high_expr_yield_addFree d prec_d level_d middle' ys' rest' hyd
  have step_op : modeStep ([], true) (.punct op.punct) = some ([], false) := by cases op <;> rfl
  have step_op' : modeStep ([], true) (.punct op'.punct) = some ([], false) := by cases op' <;> rfl
  have hit : addHit ([], true) (.punct op.punct) = true := by cases op <;> rfl
  have hit' : addHit ([], true) (.punct op'.punct) = true := by cases op' <;> rfl
  rw [hi, hi'] at heq
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] at heq
  obtain ⟨left, operator, right⟩ := lastAdd_cut_unique
    xs.flatten ys.flatten xs'.flatten ys'.flatten (.punct op.punct) (.punct op'.punct)
    done_a done_c free_b free_d step_op step_op' hit hit' heq
  refine ⟨add_punct_injective op op' (Tok.punct.inj operator), ?_⟩
  exact ⟨xs, ys, xs', ys', middle, middle', hx, hyb, hx', hyd, left, right⟩

theorem exp_child_spans (a b c d : Syn .expr)
    (initial rest initial' rest' : List Choice) (items items' : List (List Tok))
    (hp : (Syn.exp a b).prec = true) (hp' : (Syn.exp c d).prec = true)
    (hy : (Syn.exp a b).yield initial = some (items, rest))
    (hy' : (Syn.exp c d).yield initial' = some (items', rest'))
    (heq : items.flatten = items'.flatten) :
    BinaryChildSpans a b c d initial rest initial' rest' := by
  have prec_a : a.prec = true := by
    apply all_prec_implies_prec a
    have hall : (Syn.exp a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.1.2
  have level_a : 12 < a.level := by
    have hr : (Syn.exp a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 12 < 13) hr.1
  have prec_c : c.prec = true := by
    apply all_prec_implies_prec c
    have hall : (Syn.exp c d).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp').2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.1.2
  have level_c : 12 < c.level := by
    have hr : (Syn.exp c d).precNode = true := Syn.prec_root hp'
    simp only [Syn.precNode, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 12 < 13) hr.1
  obtain ⟨xs, ys, middle, hx, hyb, hi⟩ := exp_yield_parts a b initial rest items hy
  obtain ⟨xs', ys', middle', hx', hyd, hi'⟩ := exp_yield_parts c d initial' rest' items' hy'
  have free_a : BinaryFree 12 xs.flatten := binaryFreeItems_flatten
    (high_expr_yield_binaryFree 12 (by decide) (by decide) a prec_a level_a initial xs middle hx)
  have free_c : BinaryFree 12 xs'.flatten := binaryFreeItems_flatten
    (high_expr_yield_binaryFree 12 (by decide) (by decide) c prec_c level_c initial' xs' middle' hx')
  rw [hi, hi'] at heq
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] at heq
  obtain ⟨left, operator, right⟩ := firstTop_cut_unique (binaryMarker 12)
    xs.flatten ys.flatten xs'.flatten ys'.flatten (.punct .exp) (.punct .exp)
    free_a free_c (by rfl) (by rfl) heq
  exact ⟨xs, ys, xs', ys', middle, middle', hx, hyb, hx', hyd, left, right⟩

theorem assignment_child_spans (op op' : AssignOp) (a b c d : Syn .expr)
    (initial rest initial' rest' : List Choice) (items items' : List (List Tok))
    (hp : (Syn.assign op a b).prec = true) (hp' : (Syn.assign op' c d).prec = true)
    (hy : (Syn.assign op a b).yield initial = some (items, rest))
    (hy' : (Syn.assign op' c d).yield initial' = some (items', rest'))
    (heq : items.flatten = items'.flatten) :
    op = op' ∧ BinaryChildSpans a b c d initial rest initial' rest' := by
  have prec_a : a.prec = true := by
    apply all_prec_implies_prec a
    have hall : (Syn.assign op a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.1.2
  have level_a : 2 ≤ a.level := of_decide_eq_true (Syn.prec_root hp)
  have prec_c : c.prec = true := by
    apply all_prec_implies_prec c
    have hall : (Syn.assign op' c d).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp').2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.1.2
  have level_c : 2 ≤ c.level := of_decide_eq_true (Syn.prec_root hp')
  obtain ⟨xs, ys, middle, hx, hyb, hi⟩ := assignment_yield_parts op a b initial rest items hy
  obtain ⟨xs', ys', middle', hx', hyd, hi'⟩ := assignment_yield_parts op' c d initial' rest' items' hy'
  have free_a : LowFree xs.flatten := lowFreeItems_flatten
    (high_expr_yield_lowFree a prec_a level_a initial xs middle hx)
  have free_c : LowFree xs'.flatten := lowFreeItems_flatten
    (high_expr_yield_lowFree c prec_c level_c initial' xs' middle' hx')
  rw [hi, hi'] at heq
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] at heq
  obtain ⟨left, operator, right⟩ := firstTop_cut_unique lowMarker
    xs.flatten ys.flatten xs'.flatten ys'.flatten (.punct op.punct) (.punct op'.punct)
    free_a free_c (assignment_lowMarker op) (assignment_lowMarker op') heq
  refine ⟨assignment_punct_injective op op' (Tok.punct.inj operator), ?_⟩
  exact ⟨xs, ys, xs', ys', middle, middle', hx, hyb, hx', hyd, left, right⟩

end Solidity.Frontend.ExpressionUniqueness
