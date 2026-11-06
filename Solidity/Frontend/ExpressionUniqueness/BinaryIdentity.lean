import Solidity.Frontend.ExpressionUniqueness.RecursiveProperty
import Solidity.Frontend.ExpressionUniqueness.BinarySpans

/-!
# Binary expression identity structural steps

Actual certificates determine the root level, constructor and operator. Existing
child span theorems derive both word cuts internally. The only recursive facts
are induction hypotheses for the actual left and right intrinsic children.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem exp_prec_children (left right : Syn .expr)
    (hp : (Syn.exp left right).prec = true) : left.prec = true ∧ right.prec = true := by
  have hall : (Syn.exp left right).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.exp left right).precNode && left.all Syn.precNode && right.all Syn.precNode) = true at hall
  exact ⟨all_prec_implies_prec left (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hall).1).2,
    all_prec_implies_prec right (Bool.and_eq_true_iff.mp hall).2⟩

theorem exp_word_unique (left right : Syn .expr)
    (ihLeft : WordUnique left) (ihRight : WordUnique right) : WordUnique (Syn.exp left right) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  have levels : other.level = 12 := (partial_root_levels_equal (Syn.exp left right) other
    initial final initial' final' items items' hp hp' hy hy' words).symm
  cases other with
  | exp left' right' =>
    obtain ⟨xs, ys, xs', ys', middle, middle', hx, hyr, hx', hyr', leftWords, rightWords⟩ :=
      exp_child_spans left right left' right' initial final initial' final' items items' hp hp' hy hy' words
    obtain ⟨hpl, hpr⟩ := exp_prec_children left right hp
    obtain ⟨hpl', hpr'⟩ := exp_prec_children left' right' hp'
    have leftEq : left = left' := ihLeft left' initial middle initial' middle' xs xs' hpl hpl' hx hx' leftWords
    have rightEq : right = right' := ihRight right' middle final middle' final' ys ys' hpr hpr' hyr hyr' rightWords
    rw [leftEq, rightEq]
  | index => exact ((by decide : 15 ≠ 12) levels).elim
  | slice => exact ((by decide : 15 ≠ 12) levels).elim
  | member => exact ((by decide : 15 ≠ 12) levels).elim
  | callOptions => exact ((by decide : 15 ≠ 12) levels).elim
  | call => exact ((by decide : 15 ≠ 12) levels).elim
  | payableConv => exact ((by decide : 16 ≠ 12) levels).elim
  | metaType => exact ((by decide : 16 ≠ 12) levels).elim
  | unaryPrefix => exact ((by decide : 13 ≠ 12) levels).elim
  | unarySuffix => exact ((by decide : 14 ≠ 12) levels).elim
  | mulDivMod => exact ((by decide : 11 ≠ 12) levels).elim
  | addSub => exact ((by decide : 10 ≠ 12) levels).elim
  | shift => exact ((by decide : 9 ≠ 12) levels).elim
  | bitAnd => exact ((by decide : 8 ≠ 12) levels).elim
  | bitXor => exact ((by decide : 7 ≠ 12) levels).elim
  | bitOr => exact ((by decide : 6 ≠ 12) levels).elim
  | order => exact ((by decide : 5 ≠ 12) levels).elim
  | equality => exact ((by decide : 4 ≠ 12) levels).elim
  | and => exact ((by decide : 3 ≠ 12) levels).elim
  | or => exact ((by decide : 2 ≠ 12) levels).elim
  | cond => exact ((by decide : 1 ≠ 12) levels).elim
  | assign => exact ((by decide : 0 ≠ 12) levels).elim
  | new => exact ((by decide : 16 ≠ 12) levels).elim
  | tuple => exact ((by decide : 16 ≠ 12) levels).elim
  | inlineArray => exact ((by decide : 16 ≠ 12) levels).elim
  | ident => exact ((by decide : 16 ≠ 12) levels).elim
  | lit => exact ((by decide : 16 ≠ 12) levels).elim
  | litUnit => exact ((by decide : 16 ≠ 12) levels).elim
  | elemType => exact ((by decide : 16 ≠ 12) levels).elim

theorem mulDivMod_prec_children (op : MulOp) (left right : Syn .expr)
    (hp : (Syn.mulDivMod op left right).prec = true) : left.prec = true ∧ right.prec = true := by
  have hall : (Syn.mulDivMod op left right).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.mulDivMod op left right).precNode && left.all Syn.precNode && right.all Syn.precNode) = true at hall
  exact ⟨all_prec_implies_prec left (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hall).1).2,
    all_prec_implies_prec right (Bool.and_eq_true_iff.mp hall).2⟩

theorem mulDivMod_word_unique (op : MulOp) (left right : Syn .expr)
    (ihLeft : WordUnique left) (ihRight : WordUnique right) : WordUnique (Syn.mulDivMod op left right) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  have levels : other.level = 11 := (partial_root_levels_equal (Syn.mulDivMod op left right) other
    initial final initial' final' items items' hp hp' hy hy' words).symm
  cases other with
  | mulDivMod op' left' right' =>
    obtain ⟨operators, xs, ys, xs', ys', middle, middle', hx, hyr, hx', hyr', leftWords, rightWords⟩ :=
      mul_child_spans op op' left right left' right' initial final initial' final' items items' hp hp' hy hy' words
    obtain ⟨hpl, hpr⟩ := mulDivMod_prec_children op left right hp
    obtain ⟨hpl', hpr'⟩ := mulDivMod_prec_children op' left' right' hp'
    have leftEq : left = left' := ihLeft left' initial middle initial' middle' xs xs' hpl hpl' hx hx' leftWords
    have rightEq : right = right' := ihRight right' middle final middle' final' ys ys' hpr hpr' hyr hyr' rightWords
    rw [operators, leftEq, rightEq]
  | index => exact ((by decide : 15 ≠ 11) levels).elim
  | slice => exact ((by decide : 15 ≠ 11) levels).elim
  | member => exact ((by decide : 15 ≠ 11) levels).elim
  | callOptions => exact ((by decide : 15 ≠ 11) levels).elim
  | call => exact ((by decide : 15 ≠ 11) levels).elim
  | payableConv => exact ((by decide : 16 ≠ 11) levels).elim
  | metaType => exact ((by decide : 16 ≠ 11) levels).elim
  | unaryPrefix => exact ((by decide : 13 ≠ 11) levels).elim
  | unarySuffix => exact ((by decide : 14 ≠ 11) levels).elim
  | exp => exact ((by decide : 12 ≠ 11) levels).elim
  | addSub => exact ((by decide : 10 ≠ 11) levels).elim
  | shift => exact ((by decide : 9 ≠ 11) levels).elim
  | bitAnd => exact ((by decide : 8 ≠ 11) levels).elim
  | bitXor => exact ((by decide : 7 ≠ 11) levels).elim
  | bitOr => exact ((by decide : 6 ≠ 11) levels).elim
  | order => exact ((by decide : 5 ≠ 11) levels).elim
  | equality => exact ((by decide : 4 ≠ 11) levels).elim
  | and => exact ((by decide : 3 ≠ 11) levels).elim
  | or => exact ((by decide : 2 ≠ 11) levels).elim
  | cond => exact ((by decide : 1 ≠ 11) levels).elim
  | assign => exact ((by decide : 0 ≠ 11) levels).elim
  | new => exact ((by decide : 16 ≠ 11) levels).elim
  | tuple => exact ((by decide : 16 ≠ 11) levels).elim
  | inlineArray => exact ((by decide : 16 ≠ 11) levels).elim
  | ident => exact ((by decide : 16 ≠ 11) levels).elim
  | lit => exact ((by decide : 16 ≠ 11) levels).elim
  | litUnit => exact ((by decide : 16 ≠ 11) levels).elim
  | elemType => exact ((by decide : 16 ≠ 11) levels).elim

theorem addSub_prec_children (op : AddOp) (left right : Syn .expr)
    (hp : (Syn.addSub op left right).prec = true) : left.prec = true ∧ right.prec = true := by
  have hall : (Syn.addSub op left right).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.addSub op left right).precNode && left.all Syn.precNode && right.all Syn.precNode) = true at hall
  exact ⟨all_prec_implies_prec left (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hall).1).2,
    all_prec_implies_prec right (Bool.and_eq_true_iff.mp hall).2⟩

theorem addSub_word_unique (op : AddOp) (left right : Syn .expr)
    (ihLeft : WordUnique left) (ihRight : WordUnique right) : WordUnique (Syn.addSub op left right) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  have levels : other.level = 10 := (partial_root_levels_equal (Syn.addSub op left right) other
    initial final initial' final' items items' hp hp' hy hy' words).symm
  cases other with
  | addSub op' left' right' =>
    obtain ⟨operators, xs, ys, xs', ys', middle, middle', hx, hyr, hx', hyr', leftWords, rightWords⟩ :=
      add_child_spans op op' left right left' right' initial final initial' final' items items' hp hp' hy hy' words
    obtain ⟨hpl, hpr⟩ := addSub_prec_children op left right hp
    obtain ⟨hpl', hpr'⟩ := addSub_prec_children op' left' right' hp'
    have leftEq : left = left' := ihLeft left' initial middle initial' middle' xs xs' hpl hpl' hx hx' leftWords
    have rightEq : right = right' := ihRight right' middle final middle' final' ys ys' hpr hpr' hyr hyr' rightWords
    rw [operators, leftEq, rightEq]
  | index => exact ((by decide : 15 ≠ 10) levels).elim
  | slice => exact ((by decide : 15 ≠ 10) levels).elim
  | member => exact ((by decide : 15 ≠ 10) levels).elim
  | callOptions => exact ((by decide : 15 ≠ 10) levels).elim
  | call => exact ((by decide : 15 ≠ 10) levels).elim
  | payableConv => exact ((by decide : 16 ≠ 10) levels).elim
  | metaType => exact ((by decide : 16 ≠ 10) levels).elim
  | unaryPrefix => exact ((by decide : 13 ≠ 10) levels).elim
  | unarySuffix => exact ((by decide : 14 ≠ 10) levels).elim
  | exp => exact ((by decide : 12 ≠ 10) levels).elim
  | mulDivMod => exact ((by decide : 11 ≠ 10) levels).elim
  | shift => exact ((by decide : 9 ≠ 10) levels).elim
  | bitAnd => exact ((by decide : 8 ≠ 10) levels).elim
  | bitXor => exact ((by decide : 7 ≠ 10) levels).elim
  | bitOr => exact ((by decide : 6 ≠ 10) levels).elim
  | order => exact ((by decide : 5 ≠ 10) levels).elim
  | equality => exact ((by decide : 4 ≠ 10) levels).elim
  | and => exact ((by decide : 3 ≠ 10) levels).elim
  | or => exact ((by decide : 2 ≠ 10) levels).elim
  | cond => exact ((by decide : 1 ≠ 10) levels).elim
  | assign => exact ((by decide : 0 ≠ 10) levels).elim
  | new => exact ((by decide : 16 ≠ 10) levels).elim
  | tuple => exact ((by decide : 16 ≠ 10) levels).elim
  | inlineArray => exact ((by decide : 16 ≠ 10) levels).elim
  | ident => exact ((by decide : 16 ≠ 10) levels).elim
  | lit => exact ((by decide : 16 ≠ 10) levels).elim
  | litUnit => exact ((by decide : 16 ≠ 10) levels).elim
  | elemType => exact ((by decide : 16 ≠ 10) levels).elim

theorem shift_prec_children (op : ShiftOp) (left right : Syn .expr)
    (hp : (Syn.shift op left right).prec = true) : left.prec = true ∧ right.prec = true := by
  have hall : (Syn.shift op left right).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.shift op left right).precNode && left.all Syn.precNode && right.all Syn.precNode) = true at hall
  exact ⟨all_prec_implies_prec left (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hall).1).2,
    all_prec_implies_prec right (Bool.and_eq_true_iff.mp hall).2⟩

theorem shift_word_unique (op : ShiftOp) (left right : Syn .expr)
    (ihLeft : WordUnique left) (ihRight : WordUnique right) : WordUnique (Syn.shift op left right) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  have levels : other.level = 9 := (partial_root_levels_equal (Syn.shift op left right) other
    initial final initial' final' items items' hp hp' hy hy' words).symm
  cases other with
  | shift op' left' right' =>
    obtain ⟨operators, xs, ys, xs', ys', middle, middle', hx, hyr, hx', hyr', leftWords, rightWords⟩ :=
      shift_child_spans op op' left right left' right' initial final initial' final' items items' hp hp' hy hy' words
    obtain ⟨hpl, hpr⟩ := shift_prec_children op left right hp
    obtain ⟨hpl', hpr'⟩ := shift_prec_children op' left' right' hp'
    have leftEq : left = left' := ihLeft left' initial middle initial' middle' xs xs' hpl hpl' hx hx' leftWords
    have rightEq : right = right' := ihRight right' middle final middle' final' ys ys' hpr hpr' hyr hyr' rightWords
    rw [operators, leftEq, rightEq]
  | index => exact ((by decide : 15 ≠ 9) levels).elim
  | slice => exact ((by decide : 15 ≠ 9) levels).elim
  | member => exact ((by decide : 15 ≠ 9) levels).elim
  | callOptions => exact ((by decide : 15 ≠ 9) levels).elim
  | call => exact ((by decide : 15 ≠ 9) levels).elim
  | payableConv => exact ((by decide : 16 ≠ 9) levels).elim
  | metaType => exact ((by decide : 16 ≠ 9) levels).elim
  | unaryPrefix => exact ((by decide : 13 ≠ 9) levels).elim
  | unarySuffix => exact ((by decide : 14 ≠ 9) levels).elim
  | exp => exact ((by decide : 12 ≠ 9) levels).elim
  | mulDivMod => exact ((by decide : 11 ≠ 9) levels).elim
  | addSub => exact ((by decide : 10 ≠ 9) levels).elim
  | bitAnd => exact ((by decide : 8 ≠ 9) levels).elim
  | bitXor => exact ((by decide : 7 ≠ 9) levels).elim
  | bitOr => exact ((by decide : 6 ≠ 9) levels).elim
  | order => exact ((by decide : 5 ≠ 9) levels).elim
  | equality => exact ((by decide : 4 ≠ 9) levels).elim
  | and => exact ((by decide : 3 ≠ 9) levels).elim
  | or => exact ((by decide : 2 ≠ 9) levels).elim
  | cond => exact ((by decide : 1 ≠ 9) levels).elim
  | assign => exact ((by decide : 0 ≠ 9) levels).elim
  | new => exact ((by decide : 16 ≠ 9) levels).elim
  | tuple => exact ((by decide : 16 ≠ 9) levels).elim
  | inlineArray => exact ((by decide : 16 ≠ 9) levels).elim
  | ident => exact ((by decide : 16 ≠ 9) levels).elim
  | lit => exact ((by decide : 16 ≠ 9) levels).elim
  | litUnit => exact ((by decide : 16 ≠ 9) levels).elim
  | elemType => exact ((by decide : 16 ≠ 9) levels).elim

theorem bitAnd_prec_children (left right : Syn .expr)
    (hp : (Syn.bitAnd left right).prec = true) : left.prec = true ∧ right.prec = true := by
  have hall : (Syn.bitAnd left right).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.bitAnd left right).precNode && left.all Syn.precNode && right.all Syn.precNode) = true at hall
  exact ⟨all_prec_implies_prec left (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hall).1).2,
    all_prec_implies_prec right (Bool.and_eq_true_iff.mp hall).2⟩

theorem bitAnd_word_unique (left right : Syn .expr)
    (ihLeft : WordUnique left) (ihRight : WordUnique right) : WordUnique (Syn.bitAnd left right) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  have levels : other.level = 8 := (partial_root_levels_equal (Syn.bitAnd left right) other
    initial final initial' final' items items' hp hp' hy hy' words).symm
  cases other with
  | bitAnd left' right' =>
    obtain ⟨xs, ys, xs', ys', middle, middle', hx, hyr, hx', hyr', leftWords, rightWords⟩ :=
      bitAnd_child_spans left right left' right' initial final initial' final' items items' hp hp' hy hy' words
    obtain ⟨hpl, hpr⟩ := bitAnd_prec_children left right hp
    obtain ⟨hpl', hpr'⟩ := bitAnd_prec_children left' right' hp'
    have leftEq : left = left' := ihLeft left' initial middle initial' middle' xs xs' hpl hpl' hx hx' leftWords
    have rightEq : right = right' := ihRight right' middle final middle' final' ys ys' hpr hpr' hyr hyr' rightWords
    rw [leftEq, rightEq]
  | index => exact ((by decide : 15 ≠ 8) levels).elim
  | slice => exact ((by decide : 15 ≠ 8) levels).elim
  | member => exact ((by decide : 15 ≠ 8) levels).elim
  | callOptions => exact ((by decide : 15 ≠ 8) levels).elim
  | call => exact ((by decide : 15 ≠ 8) levels).elim
  | payableConv => exact ((by decide : 16 ≠ 8) levels).elim
  | metaType => exact ((by decide : 16 ≠ 8) levels).elim
  | unaryPrefix => exact ((by decide : 13 ≠ 8) levels).elim
  | unarySuffix => exact ((by decide : 14 ≠ 8) levels).elim
  | exp => exact ((by decide : 12 ≠ 8) levels).elim
  | mulDivMod => exact ((by decide : 11 ≠ 8) levels).elim
  | addSub => exact ((by decide : 10 ≠ 8) levels).elim
  | shift => exact ((by decide : 9 ≠ 8) levels).elim
  | bitXor => exact ((by decide : 7 ≠ 8) levels).elim
  | bitOr => exact ((by decide : 6 ≠ 8) levels).elim
  | order => exact ((by decide : 5 ≠ 8) levels).elim
  | equality => exact ((by decide : 4 ≠ 8) levels).elim
  | and => exact ((by decide : 3 ≠ 8) levels).elim
  | or => exact ((by decide : 2 ≠ 8) levels).elim
  | cond => exact ((by decide : 1 ≠ 8) levels).elim
  | assign => exact ((by decide : 0 ≠ 8) levels).elim
  | new => exact ((by decide : 16 ≠ 8) levels).elim
  | tuple => exact ((by decide : 16 ≠ 8) levels).elim
  | inlineArray => exact ((by decide : 16 ≠ 8) levels).elim
  | ident => exact ((by decide : 16 ≠ 8) levels).elim
  | lit => exact ((by decide : 16 ≠ 8) levels).elim
  | litUnit => exact ((by decide : 16 ≠ 8) levels).elim
  | elemType => exact ((by decide : 16 ≠ 8) levels).elim

theorem bitXor_prec_children (left right : Syn .expr)
    (hp : (Syn.bitXor left right).prec = true) : left.prec = true ∧ right.prec = true := by
  have hall : (Syn.bitXor left right).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.bitXor left right).precNode && left.all Syn.precNode && right.all Syn.precNode) = true at hall
  exact ⟨all_prec_implies_prec left (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hall).1).2,
    all_prec_implies_prec right (Bool.and_eq_true_iff.mp hall).2⟩

theorem bitXor_word_unique (left right : Syn .expr)
    (ihLeft : WordUnique left) (ihRight : WordUnique right) : WordUnique (Syn.bitXor left right) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  have levels : other.level = 7 := (partial_root_levels_equal (Syn.bitXor left right) other
    initial final initial' final' items items' hp hp' hy hy' words).symm
  cases other with
  | bitXor left' right' =>
    obtain ⟨xs, ys, xs', ys', middle, middle', hx, hyr, hx', hyr', leftWords, rightWords⟩ :=
      bitXor_child_spans left right left' right' initial final initial' final' items items' hp hp' hy hy' words
    obtain ⟨hpl, hpr⟩ := bitXor_prec_children left right hp
    obtain ⟨hpl', hpr'⟩ := bitXor_prec_children left' right' hp'
    have leftEq : left = left' := ihLeft left' initial middle initial' middle' xs xs' hpl hpl' hx hx' leftWords
    have rightEq : right = right' := ihRight right' middle final middle' final' ys ys' hpr hpr' hyr hyr' rightWords
    rw [leftEq, rightEq]
  | index => exact ((by decide : 15 ≠ 7) levels).elim
  | slice => exact ((by decide : 15 ≠ 7) levels).elim
  | member => exact ((by decide : 15 ≠ 7) levels).elim
  | callOptions => exact ((by decide : 15 ≠ 7) levels).elim
  | call => exact ((by decide : 15 ≠ 7) levels).elim
  | payableConv => exact ((by decide : 16 ≠ 7) levels).elim
  | metaType => exact ((by decide : 16 ≠ 7) levels).elim
  | unaryPrefix => exact ((by decide : 13 ≠ 7) levels).elim
  | unarySuffix => exact ((by decide : 14 ≠ 7) levels).elim
  | exp => exact ((by decide : 12 ≠ 7) levels).elim
  | mulDivMod => exact ((by decide : 11 ≠ 7) levels).elim
  | addSub => exact ((by decide : 10 ≠ 7) levels).elim
  | shift => exact ((by decide : 9 ≠ 7) levels).elim
  | bitAnd => exact ((by decide : 8 ≠ 7) levels).elim
  | bitOr => exact ((by decide : 6 ≠ 7) levels).elim
  | order => exact ((by decide : 5 ≠ 7) levels).elim
  | equality => exact ((by decide : 4 ≠ 7) levels).elim
  | and => exact ((by decide : 3 ≠ 7) levels).elim
  | or => exact ((by decide : 2 ≠ 7) levels).elim
  | cond => exact ((by decide : 1 ≠ 7) levels).elim
  | assign => exact ((by decide : 0 ≠ 7) levels).elim
  | new => exact ((by decide : 16 ≠ 7) levels).elim
  | tuple => exact ((by decide : 16 ≠ 7) levels).elim
  | inlineArray => exact ((by decide : 16 ≠ 7) levels).elim
  | ident => exact ((by decide : 16 ≠ 7) levels).elim
  | lit => exact ((by decide : 16 ≠ 7) levels).elim
  | litUnit => exact ((by decide : 16 ≠ 7) levels).elim
  | elemType => exact ((by decide : 16 ≠ 7) levels).elim

theorem bitOr_prec_children (left right : Syn .expr)
    (hp : (Syn.bitOr left right).prec = true) : left.prec = true ∧ right.prec = true := by
  have hall : (Syn.bitOr left right).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.bitOr left right).precNode && left.all Syn.precNode && right.all Syn.precNode) = true at hall
  exact ⟨all_prec_implies_prec left (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hall).1).2,
    all_prec_implies_prec right (Bool.and_eq_true_iff.mp hall).2⟩

theorem bitOr_word_unique (left right : Syn .expr)
    (ihLeft : WordUnique left) (ihRight : WordUnique right) : WordUnique (Syn.bitOr left right) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  have levels : other.level = 6 := (partial_root_levels_equal (Syn.bitOr left right) other
    initial final initial' final' items items' hp hp' hy hy' words).symm
  cases other with
  | bitOr left' right' =>
    obtain ⟨xs, ys, xs', ys', middle, middle', hx, hyr, hx', hyr', leftWords, rightWords⟩ :=
      bitOr_child_spans left right left' right' initial final initial' final' items items' hp hp' hy hy' words
    obtain ⟨hpl, hpr⟩ := bitOr_prec_children left right hp
    obtain ⟨hpl', hpr'⟩ := bitOr_prec_children left' right' hp'
    have leftEq : left = left' := ihLeft left' initial middle initial' middle' xs xs' hpl hpl' hx hx' leftWords
    have rightEq : right = right' := ihRight right' middle final middle' final' ys ys' hpr hpr' hyr hyr' rightWords
    rw [leftEq, rightEq]
  | index => exact ((by decide : 15 ≠ 6) levels).elim
  | slice => exact ((by decide : 15 ≠ 6) levels).elim
  | member => exact ((by decide : 15 ≠ 6) levels).elim
  | callOptions => exact ((by decide : 15 ≠ 6) levels).elim
  | call => exact ((by decide : 15 ≠ 6) levels).elim
  | payableConv => exact ((by decide : 16 ≠ 6) levels).elim
  | metaType => exact ((by decide : 16 ≠ 6) levels).elim
  | unaryPrefix => exact ((by decide : 13 ≠ 6) levels).elim
  | unarySuffix => exact ((by decide : 14 ≠ 6) levels).elim
  | exp => exact ((by decide : 12 ≠ 6) levels).elim
  | mulDivMod => exact ((by decide : 11 ≠ 6) levels).elim
  | addSub => exact ((by decide : 10 ≠ 6) levels).elim
  | shift => exact ((by decide : 9 ≠ 6) levels).elim
  | bitAnd => exact ((by decide : 8 ≠ 6) levels).elim
  | bitXor => exact ((by decide : 7 ≠ 6) levels).elim
  | order => exact ((by decide : 5 ≠ 6) levels).elim
  | equality => exact ((by decide : 4 ≠ 6) levels).elim
  | and => exact ((by decide : 3 ≠ 6) levels).elim
  | or => exact ((by decide : 2 ≠ 6) levels).elim
  | cond => exact ((by decide : 1 ≠ 6) levels).elim
  | assign => exact ((by decide : 0 ≠ 6) levels).elim
  | new => exact ((by decide : 16 ≠ 6) levels).elim
  | tuple => exact ((by decide : 16 ≠ 6) levels).elim
  | inlineArray => exact ((by decide : 16 ≠ 6) levels).elim
  | ident => exact ((by decide : 16 ≠ 6) levels).elim
  | lit => exact ((by decide : 16 ≠ 6) levels).elim
  | litUnit => exact ((by decide : 16 ≠ 6) levels).elim
  | elemType => exact ((by decide : 16 ≠ 6) levels).elim

theorem order_prec_children (op : OrderOp) (left right : Syn .expr)
    (hp : (Syn.order op left right).prec = true) : left.prec = true ∧ right.prec = true := by
  have hall : (Syn.order op left right).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.order op left right).precNode && left.all Syn.precNode && right.all Syn.precNode) = true at hall
  exact ⟨all_prec_implies_prec left (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hall).1).2,
    all_prec_implies_prec right (Bool.and_eq_true_iff.mp hall).2⟩

theorem order_word_unique (op : OrderOp) (left right : Syn .expr)
    (ihLeft : WordUnique left) (ihRight : WordUnique right) : WordUnique (Syn.order op left right) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  have levels : other.level = 5 := (partial_root_levels_equal (Syn.order op left right) other
    initial final initial' final' items items' hp hp' hy hy' words).symm
  cases other with
  | order op' left' right' =>
    obtain ⟨operators, xs, ys, xs', ys', middle, middle', hx, hyr, hx', hyr', leftWords, rightWords⟩ :=
      order_child_spans op op' left right left' right' initial final initial' final' items items' hp hp' hy hy' words
    obtain ⟨hpl, hpr⟩ := order_prec_children op left right hp
    obtain ⟨hpl', hpr'⟩ := order_prec_children op' left' right' hp'
    have leftEq : left = left' := ihLeft left' initial middle initial' middle' xs xs' hpl hpl' hx hx' leftWords
    have rightEq : right = right' := ihRight right' middle final middle' final' ys ys' hpr hpr' hyr hyr' rightWords
    rw [operators, leftEq, rightEq]
  | index => exact ((by decide : 15 ≠ 5) levels).elim
  | slice => exact ((by decide : 15 ≠ 5) levels).elim
  | member => exact ((by decide : 15 ≠ 5) levels).elim
  | callOptions => exact ((by decide : 15 ≠ 5) levels).elim
  | call => exact ((by decide : 15 ≠ 5) levels).elim
  | payableConv => exact ((by decide : 16 ≠ 5) levels).elim
  | metaType => exact ((by decide : 16 ≠ 5) levels).elim
  | unaryPrefix => exact ((by decide : 13 ≠ 5) levels).elim
  | unarySuffix => exact ((by decide : 14 ≠ 5) levels).elim
  | exp => exact ((by decide : 12 ≠ 5) levels).elim
  | mulDivMod => exact ((by decide : 11 ≠ 5) levels).elim
  | addSub => exact ((by decide : 10 ≠ 5) levels).elim
  | shift => exact ((by decide : 9 ≠ 5) levels).elim
  | bitAnd => exact ((by decide : 8 ≠ 5) levels).elim
  | bitXor => exact ((by decide : 7 ≠ 5) levels).elim
  | bitOr => exact ((by decide : 6 ≠ 5) levels).elim
  | equality => exact ((by decide : 4 ≠ 5) levels).elim
  | and => exact ((by decide : 3 ≠ 5) levels).elim
  | or => exact ((by decide : 2 ≠ 5) levels).elim
  | cond => exact ((by decide : 1 ≠ 5) levels).elim
  | assign => exact ((by decide : 0 ≠ 5) levels).elim
  | new => exact ((by decide : 16 ≠ 5) levels).elim
  | tuple => exact ((by decide : 16 ≠ 5) levels).elim
  | inlineArray => exact ((by decide : 16 ≠ 5) levels).elim
  | ident => exact ((by decide : 16 ≠ 5) levels).elim
  | lit => exact ((by decide : 16 ≠ 5) levels).elim
  | litUnit => exact ((by decide : 16 ≠ 5) levels).elim
  | elemType => exact ((by decide : 16 ≠ 5) levels).elim

theorem equality_prec_children (op : EqOp) (left right : Syn .expr)
    (hp : (Syn.equality op left right).prec = true) : left.prec = true ∧ right.prec = true := by
  have hall : (Syn.equality op left right).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.equality op left right).precNode && left.all Syn.precNode && right.all Syn.precNode) = true at hall
  exact ⟨all_prec_implies_prec left (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hall).1).2,
    all_prec_implies_prec right (Bool.and_eq_true_iff.mp hall).2⟩

theorem equality_word_unique (op : EqOp) (left right : Syn .expr)
    (ihLeft : WordUnique left) (ihRight : WordUnique right) : WordUnique (Syn.equality op left right) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  have levels : other.level = 4 := (partial_root_levels_equal (Syn.equality op left right) other
    initial final initial' final' items items' hp hp' hy hy' words).symm
  cases other with
  | equality op' left' right' =>
    obtain ⟨operators, xs, ys, xs', ys', middle, middle', hx, hyr, hx', hyr', leftWords, rightWords⟩ :=
      equality_child_spans op op' left right left' right' initial final initial' final' items items' hp hp' hy hy' words
    obtain ⟨hpl, hpr⟩ := equality_prec_children op left right hp
    obtain ⟨hpl', hpr'⟩ := equality_prec_children op' left' right' hp'
    have leftEq : left = left' := ihLeft left' initial middle initial' middle' xs xs' hpl hpl' hx hx' leftWords
    have rightEq : right = right' := ihRight right' middle final middle' final' ys ys' hpr hpr' hyr hyr' rightWords
    rw [operators, leftEq, rightEq]
  | index => exact ((by decide : 15 ≠ 4) levels).elim
  | slice => exact ((by decide : 15 ≠ 4) levels).elim
  | member => exact ((by decide : 15 ≠ 4) levels).elim
  | callOptions => exact ((by decide : 15 ≠ 4) levels).elim
  | call => exact ((by decide : 15 ≠ 4) levels).elim
  | payableConv => exact ((by decide : 16 ≠ 4) levels).elim
  | metaType => exact ((by decide : 16 ≠ 4) levels).elim
  | unaryPrefix => exact ((by decide : 13 ≠ 4) levels).elim
  | unarySuffix => exact ((by decide : 14 ≠ 4) levels).elim
  | exp => exact ((by decide : 12 ≠ 4) levels).elim
  | mulDivMod => exact ((by decide : 11 ≠ 4) levels).elim
  | addSub => exact ((by decide : 10 ≠ 4) levels).elim
  | shift => exact ((by decide : 9 ≠ 4) levels).elim
  | bitAnd => exact ((by decide : 8 ≠ 4) levels).elim
  | bitXor => exact ((by decide : 7 ≠ 4) levels).elim
  | bitOr => exact ((by decide : 6 ≠ 4) levels).elim
  | order => exact ((by decide : 5 ≠ 4) levels).elim
  | and => exact ((by decide : 3 ≠ 4) levels).elim
  | or => exact ((by decide : 2 ≠ 4) levels).elim
  | cond => exact ((by decide : 1 ≠ 4) levels).elim
  | assign => exact ((by decide : 0 ≠ 4) levels).elim
  | new => exact ((by decide : 16 ≠ 4) levels).elim
  | tuple => exact ((by decide : 16 ≠ 4) levels).elim
  | inlineArray => exact ((by decide : 16 ≠ 4) levels).elim
  | ident => exact ((by decide : 16 ≠ 4) levels).elim
  | lit => exact ((by decide : 16 ≠ 4) levels).elim
  | litUnit => exact ((by decide : 16 ≠ 4) levels).elim
  | elemType => exact ((by decide : 16 ≠ 4) levels).elim

theorem and_prec_children (left right : Syn .expr)
    (hp : (Syn.and left right).prec = true) : left.prec = true ∧ right.prec = true := by
  have hall : (Syn.and left right).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.and left right).precNode && left.all Syn.precNode && right.all Syn.precNode) = true at hall
  exact ⟨all_prec_implies_prec left (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hall).1).2,
    all_prec_implies_prec right (Bool.and_eq_true_iff.mp hall).2⟩

theorem and_word_unique (left right : Syn .expr)
    (ihLeft : WordUnique left) (ihRight : WordUnique right) : WordUnique (Syn.and left right) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  have levels : other.level = 3 := (partial_root_levels_equal (Syn.and left right) other
    initial final initial' final' items items' hp hp' hy hy' words).symm
  cases other with
  | and left' right' =>
    obtain ⟨xs, ys, xs', ys', middle, middle', hx, hyr, hx', hyr', leftWords, rightWords⟩ :=
      and_child_spans left right left' right' initial final initial' final' items items' hp hp' hy hy' words
    obtain ⟨hpl, hpr⟩ := and_prec_children left right hp
    obtain ⟨hpl', hpr'⟩ := and_prec_children left' right' hp'
    have leftEq : left = left' := ihLeft left' initial middle initial' middle' xs xs' hpl hpl' hx hx' leftWords
    have rightEq : right = right' := ihRight right' middle final middle' final' ys ys' hpr hpr' hyr hyr' rightWords
    rw [leftEq, rightEq]
  | index => exact ((by decide : 15 ≠ 3) levels).elim
  | slice => exact ((by decide : 15 ≠ 3) levels).elim
  | member => exact ((by decide : 15 ≠ 3) levels).elim
  | callOptions => exact ((by decide : 15 ≠ 3) levels).elim
  | call => exact ((by decide : 15 ≠ 3) levels).elim
  | payableConv => exact ((by decide : 16 ≠ 3) levels).elim
  | metaType => exact ((by decide : 16 ≠ 3) levels).elim
  | unaryPrefix => exact ((by decide : 13 ≠ 3) levels).elim
  | unarySuffix => exact ((by decide : 14 ≠ 3) levels).elim
  | exp => exact ((by decide : 12 ≠ 3) levels).elim
  | mulDivMod => exact ((by decide : 11 ≠ 3) levels).elim
  | addSub => exact ((by decide : 10 ≠ 3) levels).elim
  | shift => exact ((by decide : 9 ≠ 3) levels).elim
  | bitAnd => exact ((by decide : 8 ≠ 3) levels).elim
  | bitXor => exact ((by decide : 7 ≠ 3) levels).elim
  | bitOr => exact ((by decide : 6 ≠ 3) levels).elim
  | order => exact ((by decide : 5 ≠ 3) levels).elim
  | equality => exact ((by decide : 4 ≠ 3) levels).elim
  | or => exact ((by decide : 2 ≠ 3) levels).elim
  | cond => exact ((by decide : 1 ≠ 3) levels).elim
  | assign => exact ((by decide : 0 ≠ 3) levels).elim
  | new => exact ((by decide : 16 ≠ 3) levels).elim
  | tuple => exact ((by decide : 16 ≠ 3) levels).elim
  | inlineArray => exact ((by decide : 16 ≠ 3) levels).elim
  | ident => exact ((by decide : 16 ≠ 3) levels).elim
  | lit => exact ((by decide : 16 ≠ 3) levels).elim
  | litUnit => exact ((by decide : 16 ≠ 3) levels).elim
  | elemType => exact ((by decide : 16 ≠ 3) levels).elim

theorem or_prec_children (left right : Syn .expr)
    (hp : (Syn.or left right).prec = true) : left.prec = true ∧ right.prec = true := by
  have hall : (Syn.or left right).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.or left right).precNode && left.all Syn.precNode && right.all Syn.precNode) = true at hall
  exact ⟨all_prec_implies_prec left (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hall).1).2,
    all_prec_implies_prec right (Bool.and_eq_true_iff.mp hall).2⟩

theorem or_word_unique (left right : Syn .expr)
    (ihLeft : WordUnique left) (ihRight : WordUnique right) : WordUnique (Syn.or left right) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  have levels : other.level = 2 := (partial_root_levels_equal (Syn.or left right) other
    initial final initial' final' items items' hp hp' hy hy' words).symm
  cases other with
  | or left' right' =>
    obtain ⟨xs, ys, xs', ys', middle, middle', hx, hyr, hx', hyr', leftWords, rightWords⟩ :=
      or_child_spans left right left' right' initial final initial' final' items items' hp hp' hy hy' words
    obtain ⟨hpl, hpr⟩ := or_prec_children left right hp
    obtain ⟨hpl', hpr'⟩ := or_prec_children left' right' hp'
    have leftEq : left = left' := ihLeft left' initial middle initial' middle' xs xs' hpl hpl' hx hx' leftWords
    have rightEq : right = right' := ihRight right' middle final middle' final' ys ys' hpr hpr' hyr hyr' rightWords
    rw [leftEq, rightEq]
  | index => exact ((by decide : 15 ≠ 2) levels).elim
  | slice => exact ((by decide : 15 ≠ 2) levels).elim
  | member => exact ((by decide : 15 ≠ 2) levels).elim
  | callOptions => exact ((by decide : 15 ≠ 2) levels).elim
  | call => exact ((by decide : 15 ≠ 2) levels).elim
  | payableConv => exact ((by decide : 16 ≠ 2) levels).elim
  | metaType => exact ((by decide : 16 ≠ 2) levels).elim
  | unaryPrefix => exact ((by decide : 13 ≠ 2) levels).elim
  | unarySuffix => exact ((by decide : 14 ≠ 2) levels).elim
  | exp => exact ((by decide : 12 ≠ 2) levels).elim
  | mulDivMod => exact ((by decide : 11 ≠ 2) levels).elim
  | addSub => exact ((by decide : 10 ≠ 2) levels).elim
  | shift => exact ((by decide : 9 ≠ 2) levels).elim
  | bitAnd => exact ((by decide : 8 ≠ 2) levels).elim
  | bitXor => exact ((by decide : 7 ≠ 2) levels).elim
  | bitOr => exact ((by decide : 6 ≠ 2) levels).elim
  | order => exact ((by decide : 5 ≠ 2) levels).elim
  | equality => exact ((by decide : 4 ≠ 2) levels).elim
  | and => exact ((by decide : 3 ≠ 2) levels).elim
  | cond => exact ((by decide : 1 ≠ 2) levels).elim
  | assign => exact ((by decide : 0 ≠ 2) levels).elim
  | new => exact ((by decide : 16 ≠ 2) levels).elim
  | tuple => exact ((by decide : 16 ≠ 2) levels).elim
  | inlineArray => exact ((by decide : 16 ≠ 2) levels).elim
  | ident => exact ((by decide : 16 ≠ 2) levels).elim
  | lit => exact ((by decide : 16 ≠ 2) levels).elim
  | litUnit => exact ((by decide : 16 ≠ 2) levels).elim
  | elemType => exact ((by decide : 16 ≠ 2) levels).elim

theorem assign_prec_children (op : AssignOp) (left right : Syn .expr)
    (hp : (Syn.assign op left right).prec = true) : left.prec = true ∧ right.prec = true := by
  have hall : (Syn.assign op left right).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.assign op left right).precNode && left.all Syn.precNode && right.all Syn.precNode) = true at hall
  exact ⟨all_prec_implies_prec left (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hall).1).2,
    all_prec_implies_prec right (Bool.and_eq_true_iff.mp hall).2⟩

theorem assign_word_unique (op : AssignOp) (left right : Syn .expr)
    (ihLeft : WordUnique left) (ihRight : WordUnique right) : WordUnique (Syn.assign op left right) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  have levels : other.level = 0 := (partial_root_levels_equal (Syn.assign op left right) other
    initial final initial' final' items items' hp hp' hy hy' words).symm
  cases other with
  | assign op' left' right' =>
    obtain ⟨operators, xs, ys, xs', ys', middle, middle', hx, hyr, hx', hyr', leftWords, rightWords⟩ :=
      assignment_child_spans op op' left right left' right' initial final initial' final' items items' hp hp' hy hy' words
    obtain ⟨hpl, hpr⟩ := assign_prec_children op left right hp
    obtain ⟨hpl', hpr'⟩ := assign_prec_children op' left' right' hp'
    have leftEq : left = left' := ihLeft left' initial middle initial' middle' xs xs' hpl hpl' hx hx' leftWords
    have rightEq : right = right' := ihRight right' middle final middle' final' ys ys' hpr hpr' hyr hyr' rightWords
    rw [operators, leftEq, rightEq]
  | index => exact ((by decide : 15 ≠ 0) levels).elim
  | slice => exact ((by decide : 15 ≠ 0) levels).elim
  | member => exact ((by decide : 15 ≠ 0) levels).elim
  | callOptions => exact ((by decide : 15 ≠ 0) levels).elim
  | call => exact ((by decide : 15 ≠ 0) levels).elim
  | payableConv => exact ((by decide : 16 ≠ 0) levels).elim
  | metaType => exact ((by decide : 16 ≠ 0) levels).elim
  | unaryPrefix => exact ((by decide : 13 ≠ 0) levels).elim
  | unarySuffix => exact ((by decide : 14 ≠ 0) levels).elim
  | exp => exact ((by decide : 12 ≠ 0) levels).elim
  | mulDivMod => exact ((by decide : 11 ≠ 0) levels).elim
  | addSub => exact ((by decide : 10 ≠ 0) levels).elim
  | shift => exact ((by decide : 9 ≠ 0) levels).elim
  | bitAnd => exact ((by decide : 8 ≠ 0) levels).elim
  | bitXor => exact ((by decide : 7 ≠ 0) levels).elim
  | bitOr => exact ((by decide : 6 ≠ 0) levels).elim
  | order => exact ((by decide : 5 ≠ 0) levels).elim
  | equality => exact ((by decide : 4 ≠ 0) levels).elim
  | and => exact ((by decide : 3 ≠ 0) levels).elim
  | or => exact ((by decide : 2 ≠ 0) levels).elim
  | cond => exact ((by decide : 1 ≠ 0) levels).elim
  | new => exact ((by decide : 16 ≠ 0) levels).elim
  | tuple => exact ((by decide : 16 ≠ 0) levels).elim
  | inlineArray => exact ((by decide : 16 ≠ 0) levels).elim
  | ident => exact ((by decide : 16 ≠ 0) levels).elim
  | lit => exact ((by decide : 16 ≠ 0) levels).elim
  | litUnit => exact ((by decide : 16 ≠ 0) levels).elim
  | elemType => exact ((by decide : 16 ≠ 0) levels).elim

end Solidity.Frontend.ExpressionUniqueness
