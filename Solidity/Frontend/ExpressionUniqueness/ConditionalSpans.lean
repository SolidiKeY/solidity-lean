import Solidity.Frontend.ExpressionUniqueness.ExpressionConditional
import Solidity.Frontend.ExpressionUniqueness.YieldSplit
import Solidity.Frontend.ExpressionUniqueness.LowRoot

/-!
# Recover all three conditional child words from original certificates

The first joint low marker reconstructs the condition boundary. Actual true
branch execution establishes paired conditional punctuation, so the first
failing conditional-counter transition reconstructs the outer colon. No desired
colon split, parsing completeness or uniqueness is a premise.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def ConditionalChildSpans (c a b c' a' b' : Syn .expr)
    (initial rest initial' rest' : List Choice) : Prop :=
  ∃ cs xs ys cs' xs' ys' middle next middle' next',
    c.yield initial = some (cs, middle) ∧ a.yield middle = some (xs, next) ∧
    b.yield next = some (ys, rest) ∧ c'.yield initial' = some (cs', middle') ∧
    a'.yield middle' = some (xs', next') ∧ b'.yield next' = some (ys', rest') ∧
    cs.flatten = cs'.flatten ∧ xs.flatten = xs'.flatten ∧ ys.flatten = ys'.flatten

theorem conditional_child_spans (c a b c' a' b' : Syn .expr)
    (initial rest initial' rest' : List Choice) (items items' : List (List Tok))
    (hp : (Syn.cond c a b).prec = true) (hp' : (Syn.cond c' a' b').prec = true)
    (hy : (Syn.cond c a b).yield initial = some (items, rest))
    (hy' : (Syn.cond c' a' b').yield initial' = some (items', rest'))
    (heq : items.flatten = items'.flatten) :
    ConditionalChildSpans c a b c' a' b' initial rest initial' rest' := by
  have prec_c : c.prec = true := by
    apply all_prec_implies_prec c
    have hall : (Syn.cond c a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.1.1.2
  have prec_c' : c'.prec = true := by
    apply all_prec_implies_prec c'
    have hall : (Syn.cond c' a' b').all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp').2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.1.1.2
  have level_c : 2 ≤ c.level := by
    have hr : (Syn.cond c a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact hr.1
  have level_c' : 2 ≤ c'.level := by
    have hr : (Syn.cond c' a' b').precNode = true := Syn.prec_root hp'
    simp only [Syn.precNode, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact hr.1
  obtain ⟨cs, xs, ys, middle, next, hc, ha, hb, hi⟩ := conditional_yield_parts c a b initial rest items hy
  obtain ⟨cs', xs', ys', middle', next', hc', ha', hb', hi'⟩ :=
    conditional_yield_parts c' a' b' initial' rest' items' hy'
  have free_c : LowFree cs.flatten := lowFreeItems_flatten
    (high_expr_yield_lowFree c prec_c level_c initial cs middle hc)
  have free_c' : LowFree cs'.flatten := lowFreeItems_flatten
    (high_expr_yield_lowFree c' prec_c' level_c' initial' cs' middle' hc')
  have paired_a : QBalanced xs.flatten := qBalancedItems_flatten
    (expr_yield_qBalanced a middle xs next ha)
  have paired_a' : QBalanced xs'.flatten := qBalancedItems_flatten
    (expr_yield_qBalanced a' middle' xs' next' ha')
  rw [hi, hi'] at heq
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] at heq
  obtain ⟨condition, question, branches⟩ := firstTop_cut_unique lowMarker cs.flatten
    (xs.flatten ++ .punct .colon :: ys.flatten) cs'.flatten
    (xs'.flatten ++ .punct .colon :: ys'.flatten) (.punct .question) (.punct .question)
    free_c free_c' rfl rfl heq
  obtain ⟨trueBranch, falseBranch⟩ := qBalanced_colon_cut_unique xs.flatten ys.flatten
    xs'.flatten ys'.flatten paired_a paired_a' branches
  exact ⟨cs, xs, ys, cs', xs', ys', middle, next, middle', next',
    hc, ha, hb, hc', ha', hb', condition, trueBranch, falseBranch⟩

theorem qBalanced_not_unpaired_colon (xs ys : List Tok) (hx : QBalanced xs) :
    ¬ QBalanced (xs ++ .punct .colon :: ys) := by
  intro h
  have bad : qRun ([], 0) (xs ++ .punct .colon :: ys) = some ([], 0) := h 0
  rw [qRun_append, hx 0, Option.bind_some, qRun] at bad
  change (none : Option QState).bind (fun next => qRun next ys) = some ([], 0) at bad
  cases bad

theorem optional_expr_yield_qBalanced (e : Syn (.opt .expr)) : Produces e.yield QBalancedItems :=
  expressionCategory_yield_qBalanced e rfl

theorem slice_payload_colon_unique (i i' : Syn (.opt .expr))
    (initial rest initial' rest' : List Choice) (xs xs' : List (List Tok)) (ys ys' : List Tok)
    (hi : i.yield initial = some (xs, rest)) (hi' : i'.yield initial' = some (xs', rest'))
    (he : xs.flatten ++ .punct .colon :: ys = xs'.flatten ++ .punct .colon :: ys') :
    xs.flatten = xs'.flatten ∧ ys = ys' :=
  qBalanced_colon_cut_unique _ _ _ _
    (qBalancedItems_flatten (optional_expr_yield_qBalanced i initial xs rest hi))
    (qBalancedItems_flatten (optional_expr_yield_qBalanced i' initial' xs' rest' hi')) he

theorem index_slice_payload_disjoint (index start : Syn (.opt .expr))
    (initial rest initial' rest' : List Choice) (xs ys : List (List Tok)) (tail : List Tok)
    (hi : index.yield initial = some (xs, rest))
    (hs : start.yield initial' = some (ys, rest')) :
    xs.flatten ≠ ys.flatten ++ .punct .colon :: tail := by
  intro words
  have whole : QBalanced xs.flatten :=
    qBalancedItems_flatten (optional_expr_yield_qBalanced index initial xs rest hi)
  have pairedStart : QBalanced ys.flatten :=
    qBalancedItems_flatten (optional_expr_yield_qBalanced start initial' ys rest' hs)
  rw [words] at whole
  exact qBalanced_not_unpaired_colon _ _ pairedStart whole

end Solidity.Frontend.ExpressionUniqueness
