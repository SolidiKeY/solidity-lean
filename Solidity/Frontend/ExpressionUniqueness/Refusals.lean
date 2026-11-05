import Solidity.Frontend.Checked.Prec

/-!
# Whole-certificate refusal and precedence boundary families

All controls quantify arbitrary intrinsic subtrees and operator values. Refusal
is at `Syn.prec`, not merely the root predicate. These facts constrain accepted
trees but do not prove same-yield root reconstruction or global uniqueness.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source

theorem refused_of_node_false {c : Cat} {e : Syn c} (h : e.precNode = false) :
    e.prec = false := by
  simp only [Syn.prec, h, Bool.false_and]

theorem prefix_suffix_refused (o : PrefixOp) (q : SuffixOp) (a : Syn .expr) :
    (Syn.unaryPrefix o (.unarySuffix q a)).prec = false :=
  refused_of_node_false rfl

theorem suffix_prefix_refused (o : PrefixOp) (q : SuffixOp) (a : Syn .expr) :
    (Syn.unarySuffix q (.unaryPrefix o a)).prec = false :=
  refused_of_node_false rfl

theorem conditional_assignment_refused (o : AssignOp) (a b c d : Syn .expr) :
    (Syn.cond a b (.assign o c d)).prec = false ∧
    (Syn.assign o (.cond a b c) d).prec = false := by
  refine ⟨refused_of_node_false ?_, refused_of_node_false rfl⟩
  show (decide (2 ≤ a.level) && false) = false
  simp only [Bool.and_false]

theorem postfix_bases_refused (q r : SuffixOp) (a : Syn .expr)
    (i j : Syn (.opt .expr)) (name : String) (arg : Syn .namedArg)
    (args : Syn (.list .namedArg)) (callArgs : Syn .callArgs) :
    (Syn.index (.unarySuffix q a) i).prec = false ∧
    (Syn.slice (.unarySuffix q a) i j).prec = false ∧
    (Syn.member (.unarySuffix q a) name).prec = false ∧
    (Syn.callOptions (.unarySuffix q a) arg args).prec = false ∧
    (Syn.call (.unarySuffix q a) callArgs).prec = false ∧
    (Syn.unarySuffix r (.unarySuffix q a)).prec = false :=
  ⟨refused_of_node_false rfl, refused_of_node_false rfl,
    refused_of_node_false rfl, refused_of_node_false rfl,
    refused_of_node_false rfl, refused_of_node_false rfl⟩

theorem new_bases_refused (t : Syn .typeName) (i j : Syn (.opt .expr)) (name : String) :
    (Syn.index (.new t) i).prec = false ∧
    (Syn.slice (.new t) i j).prec = false ∧
    (Syn.member (.new t) name).prec = false :=
  ⟨refused_of_node_false rfl, refused_of_node_false rfl, refused_of_node_false rfl⟩

theorem or_right_nested_refused (a b c : Syn .expr) :
    (Syn.or a (.or b c)).prec = false := by
  apply refused_of_node_false
  show (decide (2 ≤ a.level) && false) = false
  simp only [Bool.and_false]

theorem and_right_nested_refused (a b c : Syn .expr) :
    (Syn.and a (.and b c)).prec = false := by
  apply refused_of_node_false
  show (decide (3 ≤ a.level) && false) = false
  simp only [Bool.and_false]

theorem equality_right_nested_refused (o q : EqOp) (a b c : Syn .expr) :
    (Syn.equality o a (.equality q b c)).prec = false := by
  apply refused_of_node_false
  show (decide (4 ≤ a.level) && false) = false
  simp only [Bool.and_false]

theorem order_right_nested_refused (o q : OrderOp) (a b c : Syn .expr) :
    (Syn.order o a (.order q b c)).prec = false := by
  apply refused_of_node_false
  show (decide (5 ≤ a.level) && false) = false
  simp only [Bool.and_false]

theorem bitOr_right_nested_refused (a b c : Syn .expr) :
    (Syn.bitOr a (.bitOr b c)).prec = false := by
  apply refused_of_node_false
  show (decide (6 ≤ a.level) && false) = false
  simp only [Bool.and_false]

theorem bitXor_right_nested_refused (a b c : Syn .expr) :
    (Syn.bitXor a (.bitXor b c)).prec = false := by
  apply refused_of_node_false
  show (decide (7 ≤ a.level) && false) = false
  simp only [Bool.and_false]

theorem bitAnd_right_nested_refused (a b c : Syn .expr) :
    (Syn.bitAnd a (.bitAnd b c)).prec = false := by
  apply refused_of_node_false
  show (decide (8 ≤ a.level) && false) = false
  simp only [Bool.and_false]

theorem shift_right_nested_refused (o q : ShiftOp) (a b c : Syn .expr) :
    (Syn.shift o a (.shift q b c)).prec = false := by
  apply refused_of_node_false
  show (decide (9 ≤ a.level) && false) = false
  simp only [Bool.and_false]

theorem addSub_right_nested_refused (o q : AddOp) (a b c : Syn .expr) :
    (Syn.addSub o a (.addSub q b c)).prec = false := by
  apply refused_of_node_false
  show (decide (10 ≤ a.level) && false) = false
  simp only [Bool.and_false]

theorem mulDivMod_right_nested_refused (o q : MulOp) (a b c : Syn .expr) :
    (Syn.mulDivMod o a (.mulDivMod q b c)).prec = false := by
  apply refused_of_node_false
  show (decide (11 ≤ a.level) && false) = false
  simp only [Bool.and_false]

theorem exp_left_nested_refused (a b c : Syn .expr) :
    (Syn.exp (.exp a b) c).prec = false := refused_of_node_false rfl

theorem conditional_left_nested_refused (a b c d e : Syn .expr) :
    (Syn.cond (.cond a b c) d e).prec = false := refused_of_node_false rfl

theorem assignment_left_nested_refused (o q : AssignOp) (a b c : Syn .expr) :
    (Syn.assign o (.assign q a b) c).prec = false := refused_of_node_false rfl

end Solidity.Frontend.ExpressionUniqueness
