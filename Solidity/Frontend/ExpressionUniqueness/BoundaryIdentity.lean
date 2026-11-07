import Solidity.Frontend.ExpressionUniqueness.RecursiveProperty
import Solidity.Frontend.ExpressionUniqueness.ConditionalSpans

/-!
# Unary and conditional expression identity steps

Certified root levels and actual child-word cuts identify the original
constructors/operators. Recursive premises are structural child facts only.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem unaryPrefix_prec_child (op : PrefixOp) (child : Syn .expr)
    (hp : (Syn.unaryPrefix op child).prec = true) : child.prec = true := by
  have hall : (Syn.unaryPrefix op child).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.unaryPrefix op child).precNode && child.all Syn.precNode) = true at hall
  exact all_prec_implies_prec child (Bool.and_eq_true_iff.mp hall).2

theorem unaryPrefix_word_unique (op : PrefixOp) (child : Syn .expr) (ih : WordUnique child) :
    WordUnique (Syn.unaryPrefix op child) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  have levels : other.level = 13 := (partial_root_levels_equal (Syn.unaryPrefix op child) other
    initial final initial' final' items items' hp hp' hy hy' words).symm
  cases other with
  | unaryPrefix op' child' =>
    obtain ⟨operators, xs, ys, hx, hyb, childWords⟩ := prefix_child_spans op op' child child'
      initial final initial' final' items items' hy hy' words
    have childEq : child = child' := ih child' initial final initial' final' xs ys
      (unaryPrefix_prec_child op child hp) (unaryPrefix_prec_child op' child' hp') hx hyb childWords
    rw [operators, childEq]
  | index => exact ((by decide : 15 ≠ 13) levels).elim
  | slice => exact ((by decide : 15 ≠ 13) levels).elim
  | member => exact ((by decide : 15 ≠ 13) levels).elim
  | callOptions => exact ((by decide : 15 ≠ 13) levels).elim
  | call => exact ((by decide : 15 ≠ 13) levels).elim
  | payableConv => exact ((by decide : 16 ≠ 13) levels).elim
  | metaType => exact ((by decide : 16 ≠ 13) levels).elim
  | unarySuffix => exact ((by decide : 14 ≠ 13) levels).elim
  | exp => exact ((by decide : 12 ≠ 13) levels).elim
  | mulDivMod => exact ((by decide : 11 ≠ 13) levels).elim
  | addSub => exact ((by decide : 10 ≠ 13) levels).elim
  | shift => exact ((by decide : 9 ≠ 13) levels).elim
  | bitAnd => exact ((by decide : 8 ≠ 13) levels).elim
  | bitXor => exact ((by decide : 7 ≠ 13) levels).elim
  | bitOr => exact ((by decide : 6 ≠ 13) levels).elim
  | order => exact ((by decide : 5 ≠ 13) levels).elim
  | equality => exact ((by decide : 4 ≠ 13) levels).elim
  | and => exact ((by decide : 3 ≠ 13) levels).elim
  | or => exact ((by decide : 2 ≠ 13) levels).elim
  | cond => exact ((by decide : 1 ≠ 13) levels).elim
  | assign => exact ((by decide : 0 ≠ 13) levels).elim
  | new => exact ((by decide : 16 ≠ 13) levels).elim
  | tuple => exact ((by decide : 16 ≠ 13) levels).elim
  | inlineArray => exact ((by decide : 16 ≠ 13) levels).elim
  | ident => exact ((by decide : 16 ≠ 13) levels).elim
  | lit => exact ((by decide : 16 ≠ 13) levels).elim
  | litUnit => exact ((by decide : 16 ≠ 13) levels).elim
  | elemType => exact ((by decide : 16 ≠ 13) levels).elim

theorem unarySuffix_prec_child (op : SuffixOp) (child : Syn .expr)
    (hp : (Syn.unarySuffix op child).prec = true) : child.prec = true := by
  have hall : (Syn.unarySuffix op child).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.unarySuffix op child).precNode && child.all Syn.precNode) = true at hall
  exact all_prec_implies_prec child (Bool.and_eq_true_iff.mp hall).2

theorem unarySuffix_word_unique (op : SuffixOp) (child : Syn .expr) (ih : WordUnique child) :
    WordUnique (Syn.unarySuffix op child) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  have levels : other.level = 14 := (partial_root_levels_equal (Syn.unarySuffix op child) other
    initial final initial' final' items items' hp hp' hy hy' words).symm
  cases other with
  | unarySuffix op' child' =>
    obtain ⟨operators, xs, ys, hx, hyb, childWords⟩ := suffix_child_spans op op' child child'
      initial final initial' final' items items' hy hy' words
    have childEq : child = child' := ih child' initial final initial' final' xs ys
      (unarySuffix_prec_child op child hp) (unarySuffix_prec_child op' child' hp') hx hyb childWords
    rw [operators, childEq]
  | index => exact ((by decide : 15 ≠ 14) levels).elim
  | slice => exact ((by decide : 15 ≠ 14) levels).elim
  | member => exact ((by decide : 15 ≠ 14) levels).elim
  | callOptions => exact ((by decide : 15 ≠ 14) levels).elim
  | call => exact ((by decide : 15 ≠ 14) levels).elim
  | payableConv => exact ((by decide : 16 ≠ 14) levels).elim
  | metaType => exact ((by decide : 16 ≠ 14) levels).elim
  | unaryPrefix => exact ((by decide : 13 ≠ 14) levels).elim
  | exp => exact ((by decide : 12 ≠ 14) levels).elim
  | mulDivMod => exact ((by decide : 11 ≠ 14) levels).elim
  | addSub => exact ((by decide : 10 ≠ 14) levels).elim
  | shift => exact ((by decide : 9 ≠ 14) levels).elim
  | bitAnd => exact ((by decide : 8 ≠ 14) levels).elim
  | bitXor => exact ((by decide : 7 ≠ 14) levels).elim
  | bitOr => exact ((by decide : 6 ≠ 14) levels).elim
  | order => exact ((by decide : 5 ≠ 14) levels).elim
  | equality => exact ((by decide : 4 ≠ 14) levels).elim
  | and => exact ((by decide : 3 ≠ 14) levels).elim
  | or => exact ((by decide : 2 ≠ 14) levels).elim
  | cond => exact ((by decide : 1 ≠ 14) levels).elim
  | assign => exact ((by decide : 0 ≠ 14) levels).elim
  | new => exact ((by decide : 16 ≠ 14) levels).elim
  | tuple => exact ((by decide : 16 ≠ 14) levels).elim
  | inlineArray => exact ((by decide : 16 ≠ 14) levels).elim
  | ident => exact ((by decide : 16 ≠ 14) levels).elim
  | lit => exact ((by decide : 16 ≠ 14) levels).elim
  | litUnit => exact ((by decide : 16 ≠ 14) levels).elim
  | elemType => exact ((by decide : 16 ≠ 14) levels).elim

theorem cond_prec_children (condition yes no : Syn .expr)
    (hp : (Syn.cond condition yes no).prec = true) :
    condition.prec = true ∧ yes.prec = true ∧ no.prec = true := by
  have hall : (Syn.cond condition yes no).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.cond condition yes no).precNode && condition.all Syn.precNode && yes.all Syn.precNode && no.all Syn.precNode) = true at hall
  exact ⟨all_prec_implies_prec condition (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hall).1).1).2,
    all_prec_implies_prec yes (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hall).1).2,
    all_prec_implies_prec no (Bool.and_eq_true_iff.mp hall).2⟩

theorem cond_word_unique (condition yes no : Syn .expr)
    (ihCondition : WordUnique condition) (ihYes : WordUnique yes) (ihNo : WordUnique no) :
    WordUnique (Syn.cond condition yes no) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  have levels : other.level = 1 := (partial_root_levels_equal (Syn.cond condition yes no) other
    initial final initial' final' items items' hp hp' hy hy' words).symm
  cases other with
  | cond condition' yes' no' =>
    obtain ⟨cs, xs, ys, cs', xs', ys', middle, next, middle', next', hc, hx, hyr, hc', hx', hyr', cw, xw, yw⟩ :=
      conditional_child_spans condition yes no condition' yes' no' initial final initial' final' items items' hp hp' hy hy' words
    obtain ⟨hpc, hpy, hpn⟩ := cond_prec_children condition yes no hp
    obtain ⟨hpc', hpy', hpn'⟩ := cond_prec_children condition' yes' no' hp'
    have cEq : condition = condition' := ihCondition condition' initial middle initial' middle' cs cs' hpc hpc' hc hc' cw
    have yEq : yes = yes' := ihYes yes' middle next middle' next' xs xs' hpy hpy' hx hx' xw
    have nEq : no = no' := ihNo no' next final next' final' ys ys' hpn hpn' hyr hyr' yw
    rw [cEq, yEq, nEq]
  | index => exact ((by decide : 15 ≠ 1) levels).elim
  | slice => exact ((by decide : 15 ≠ 1) levels).elim
  | member => exact ((by decide : 15 ≠ 1) levels).elim
  | callOptions => exact ((by decide : 15 ≠ 1) levels).elim
  | call => exact ((by decide : 15 ≠ 1) levels).elim
  | payableConv => exact ((by decide : 16 ≠ 1) levels).elim
  | metaType => exact ((by decide : 16 ≠ 1) levels).elim
  | unaryPrefix => exact ((by decide : 13 ≠ 1) levels).elim
  | unarySuffix => exact ((by decide : 14 ≠ 1) levels).elim
  | exp => exact ((by decide : 12 ≠ 1) levels).elim
  | mulDivMod => exact ((by decide : 11 ≠ 1) levels).elim
  | addSub => exact ((by decide : 10 ≠ 1) levels).elim
  | shift => exact ((by decide : 9 ≠ 1) levels).elim
  | bitAnd => exact ((by decide : 8 ≠ 1) levels).elim
  | bitXor => exact ((by decide : 7 ≠ 1) levels).elim
  | bitOr => exact ((by decide : 6 ≠ 1) levels).elim
  | order => exact ((by decide : 5 ≠ 1) levels).elim
  | equality => exact ((by decide : 4 ≠ 1) levels).elim
  | and => exact ((by decide : 3 ≠ 1) levels).elim
  | or => exact ((by decide : 2 ≠ 1) levels).elim
  | assign => exact ((by decide : 0 ≠ 1) levels).elim
  | new => exact ((by decide : 16 ≠ 1) levels).elim
  | tuple => exact ((by decide : 16 ≠ 1) levels).elim
  | inlineArray => exact ((by decide : 16 ≠ 1) levels).elim
  | ident => exact ((by decide : 16 ≠ 1) levels).elim
  | lit => exact ((by decide : 16 ≠ 1) levels).elim
  | litUnit => exact ((by decide : 16 ≠ 1) levels).elim
  | elemType => exact ((by decide : 16 ≠ 1) levels).elim

end Solidity.Frontend.ExpressionUniqueness
