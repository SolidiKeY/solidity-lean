import Solidity.Frontend.ExpressionUniqueness.BinaryFreeAlgebra
import Solidity.Frontend.ExpressionUniqueness.ExpressionLowFree

/-!
# Certified higher roots avoid each lower binary marker family

The invariant is uniform over binary ranks at least two other than ten. Rank
ten needs a separate operand-state invariant for prefix minus; that original
obligation is retained. All existing constructors and arbitrary expression/type/
argument descendants are covered under their existing precedence certificate.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def BinaryYieldProperty (rank : Nat) {c : Cat} (e : Syn c) : Prop :=
  match c with
  | .expr => e.prec = true → rank < e.level → Produces e.yield (BinaryFreeItems rank)
  | .typeName | .callArgs => Produces e.yield (BinaryFreeItems rank)
  | _ => True

theorem expression_binary_property (rank : Nat) (hmin : 2 ≤ rank) (hskip : rank ≠ 10)
    {c : Cat} (e : Syn c) : BinaryYieldProperty rank e := by
  induction e with
  | positional es ih =>
    apply produces_bind es.yield _ BalancedItems (BinaryFreeItems rank) (expressionCategory_yield_balanced es rfl)
    intro items hi
    exact produces_pure _ _ (binaryFreeItems_single (binaryFree_parens (balanced_commaSep hi)))
  | named args ih =>
    apply produces_bind args.yield _ BalancedItems (BinaryFreeItems rank) (expressionCategory_yield_balanced args rfl)
    intro items hi
    exact produces_pure _ _ (binaryFreeItems_single (binaryFree_parens (balanced_braces (balanced_commaSep hi))))
  | elem ty => exact produces_pure _ _ (binaryFreeItems_single (binaryFree_elem ty))
  | userType path => exact produces_pure _ _ (binaryFreeItems_single (binaryFree_path path))
  | array ty len ihTy ihLen =>
    apply produces_bind ty.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ihTy)
    intro types ht
    apply produces_bind len.yield _ BalancedItems (BinaryFreeItems rank) (expressionCategory_yield_balanced len rfl)
    intro lengths hl
    apply produces_pure
    apply binaryFreeItems_single
    simpa only [List.append_assoc] using binaryFree_append (binaryFreeItems_flatten ht)
      (binaryFree_square (balancedItems_flatten hl))
  | mapping key keyName value valueName ih =>
    apply produces_bind value.yield _ BalancedItems (BinaryFreeItems rank) (expressionCategory_yield_balanced value rfl)
    intro items hi
    apply produces_pure
    apply binaryFreeItems_single
    exact binaryFree_append (binaryFree_tk .mapping) (binaryFree_parens
      (balanced_append (balanced_append (balanced_append (balanced_append
        (balanced_mapping_key key) (balanced_optToks idt balanced_idt keyName))
        (balanced_atom rfl)) (balancedItems_flatten hi))
        (balanced_optToks idt balanced_idt valueName)))
  | fnType ps vis mu rets ihPs ihRets =>
    apply produces_bind_all popAttrs _ (BinaryFreeItems rank)
    intro order
    apply produces_bind ps.yield _ BalancedItems (BinaryFreeItems rank) (expressionCategory_yield_balanced ps rfl)
    intro params hp
    have hs : (BinaryFreeAttrs rank) (single .vis (optToks Visibility.toks vis) ++
        single .mutab (optToks Mutability.toks mu)) :=
      binaryFreeAttrs_append (binaryFree_single _ _ (binaryFree_optToks Visibility.toks binaryFree_visibility vis))
        (binaryFree_single _ _ (binaryFree_optToks Mutability.toks binaryFree_mutability mu))
    apply produces_bind (attrsP _ [] order) _ (BinaryFree rank) (BinaryFreeItems rank)
      (attrsP_binaryFree _ [] order hs binaryFreeItems_nil)
    intro attrs ha
    apply produces_bind rets.yield _ BalancedItems (BinaryFreeItems rank) (expressionCategory_yield_balanced rets rfl)
    intro returns hr
    apply produces_pure
    apply binaryFreeItems_single
    apply binaryFree_append (binaryFree_append (binaryFree_append (binaryFree_tk .function)
      (binaryFree_parens (balanced_commaSep hp))) ha)
    split
    · exact binaryFree_nil
    · exact binaryFree_append (binaryFree_tk .returns) (binaryFree_parens (balanced_commaSep hr))
  | index e i ih0 ih1 =>
    intro hp hl
    change rank < 15 at hl
    have hprece : e.prec = true := by
      apply all_prec_implies_prec e
      have hall : (Syn.index e i).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.2
    have hr : (Syn.index e i).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hlevele : rank < e.level := Nat.lt_of_lt_of_le hl hr.1
    apply produces_bind e.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih0 hprece hlevele)
    intro value0 h0
    apply produces_bind i.yield _ BalancedItems (BinaryFreeItems rank) (expressionCategory_yield_balanced i rfl)
    intro value1 h1
    apply produces_pure
    apply binaryFreeItems_single
    simpa only [List.append_assoc] using binaryFree_append (binaryFreeItems_flatten h0) (binaryFree_square (balancedItems_flatten h1))
  | slice e i j ih0 ih1 ih2 =>
    intro hp hl
    change rank < 15 at hl
    have hprece : e.prec = true := by
      apply all_prec_implies_prec e
      have hall : (Syn.slice e i j).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.1.2
    have hr : (Syn.slice e i j).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hlevele : rank < e.level := Nat.lt_of_lt_of_le hl hr.1
    apply produces_bind e.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih0 hprece hlevele)
    intro value0 h0
    apply produces_bind i.yield _ BalancedItems (BinaryFreeItems rank) (expressionCategory_yield_balanced i rfl)
    intro value1 h1
    apply produces_bind j.yield _ BalancedItems (BinaryFreeItems rank) (expressionCategory_yield_balanced j rfl)
    intro value2 h2
    apply produces_pure
    apply binaryFreeItems_single
    simpa only [List.append_assoc] using binaryFree_append (binaryFreeItems_flatten h0) (binaryFree_square (balanced_append (balanced_append (balancedItems_flatten h1) (balanced_atom rfl)) (balancedItems_flatten h2)))
  | member e name ih0 =>
    intro hp hl
    change rank < 15 at hl
    have hprece : e.prec = true := by
      apply all_prec_implies_prec e
      have hall : (Syn.member e name).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.2
    have hr : (Syn.member e name).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hlevele : rank < e.level := Nat.lt_of_lt_of_le hl hr.1
    apply produces_bind e.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih0 hprece hlevele)
    intro value0 h0
    apply produces_pure
    apply binaryFreeItems_single
    apply binaryFree_append (binaryFree_append (binaryFreeItems_flatten h0) (binaryFree_atom rfl rfl))
    split <;> exact binaryFree_atom rfl rfl
  | callOptions e first rest ih0 ih1 ih2 =>
    intro hp hl
    change rank < 15 at hl
    have hprece : e.prec = true := by
      apply all_prec_implies_prec e
      have hall : (Syn.callOptions e first rest).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.1.2
    have hr : (Syn.callOptions e first rest).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, decide_eq_true_eq] at hr
    have hlevele : rank < e.level := Nat.lt_of_lt_of_le hl hr
    apply produces_bind e.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih0 hprece hlevele)
    intro value0 h0
    apply produces_bind first.yield _ BalancedItems (BinaryFreeItems rank) (expressionCategory_yield_balanced first rfl)
    intro value1 h1
    apply produces_bind rest.yield _ BalancedItems (BinaryFreeItems rank) (expressionCategory_yield_balanced rest rfl)
    intro value2 h2
    apply produces_pure
    apply binaryFreeItems_single
    exact binaryFree_append (binaryFreeItems_flatten h0) (binaryFree_braces (balanced_commaSep (balancedItems_cons (balancedItems_flatten h1) h2)))
  | call e args ih0 ih1 =>
    intro hp hl
    change rank < 15 at hl
    have hprece : e.prec = true := by
      apply all_prec_implies_prec e
      have hall : (Syn.call e args).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.2
    have hr : (Syn.call e args).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, decide_eq_true_eq] at hr
    have hlevele : rank < e.level := Nat.lt_of_lt_of_le hl hr
    apply produces_bind e.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih0 hprece hlevele)
    intro value0 h0
    apply produces_bind args.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih1)
    intro value1 h1
    apply produces_pure
    apply binaryFreeItems_single
    exact binaryFree_append (binaryFreeItems_flatten h0) (binaryFreeItems_flatten h1)
  | payableConv args ih0 =>
    intro _ _
    apply produces_bind args.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih0)
    intro value0 h0
    apply produces_pure
    apply binaryFreeItems_single
    exact binaryFree_append (binaryFree_tk .payable) (binaryFreeItems_flatten h0)
  | metaType ty ih0 =>
    intro _ _
    apply produces_bind ty.yield _ BalancedItems (BinaryFreeItems rank) (expressionCategory_yield_balanced ty rfl)
    intro value0 h0
    apply produces_pure
    apply binaryFreeItems_single
    exact binaryFree_append (binaryFree_tk .type_) (binaryFree_parens (balancedItems_flatten h0))
  | unaryPrefix op e ih0 =>
    intro hp hl
    change rank < 13 at hl
    have hprece : e.prec = true := by
      apply all_prec_implies_prec e
      have hall : (Syn.unaryPrefix op e).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.2
    have hr : (Syn.unaryPrefix op e).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hlevele : rank < e.level := Nat.lt_of_lt_of_le hl hr.1
    apply produces_bind e.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih0 hprece hlevele)
    intro value0 h0
    apply produces_pure
    apply binaryFreeItems_single
    exact binaryFree_append (binaryFree_prefix op hskip) (binaryFreeItems_flatten h0)
  | unarySuffix op e ih0 =>
    intro hp hl
    change rank < 14 at hl
    have hprece : e.prec = true := by
      apply all_prec_implies_prec e
      have hall : (Syn.unarySuffix op e).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.2
    have hr : (Syn.unarySuffix op e).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, decide_eq_true_eq] at hr
    have hlevele : rank < e.level := Nat.lt_of_lt_of_le hl (Nat.le_trans (by decide : 14 ≤ 15) hr)
    apply produces_bind e.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih0 hprece hlevele)
    intro value0 h0
    apply produces_pure
    apply binaryFreeItems_single
    exact binaryFree_append (binaryFreeItems_flatten h0) (binaryFree_suffix op)
  | exp a b ih0 ih1 =>
    intro hp hl
    change rank < 12 at hl
    have hpreca : a.prec = true := by
      apply all_prec_implies_prec a
      have hall : (Syn.exp a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.2
    have hprecb : b.prec = true := by
      apply all_prec_implies_prec b
      have hall : (Syn.exp a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.2
    have hr : (Syn.exp a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hlevela : rank < a.level := Nat.lt_of_lt_of_le hl (Nat.le_trans (by decide : 12 ≤ 13) hr.1)
    have hlevelb : rank < b.level := Nat.lt_of_lt_of_le hl hr.2
    apply produces_bind a.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih0 hpreca hlevela)
    intro value0 h0
    apply produces_bind b.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih1 hprecb hlevelb)
    intro value1 h1
    apply produces_pure
    apply binaryFreeItems_single
    exact binaryFree_append (binaryFree_append (binaryFreeItems_flatten h0) (binaryFree_atom rfl (decide_eq_false (Nat.ne_of_lt hl)))) (binaryFreeItems_flatten h1)
  | cond c a b ih0 ih1 ih2  =>
    intro _ hl
    have impossible : False := by
      change rank < 1 at hl
      omega
    exact impossible.elim
  | new ty ih0 =>
    intro _ _
    apply produces_bind ty.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih0)
    intro value0 h0
    apply produces_pure
    apply binaryFreeItems_single
    exact binaryFree_append (binaryFree_tk .new) (binaryFreeItems_flatten h0)
  | tuple first rest ih0 ih1 =>
    intro _ _
    apply produces_bind first.yield _ BalancedItems (BinaryFreeItems rank) (expressionCategory_yield_balanced first rfl)
    intro value0 h0
    apply produces_bind rest.yield _ BalancedItems (BinaryFreeItems rank) (expressionCategory_yield_balanced rest rfl)
    intro value1 h1
    apply produces_pure
    apply binaryFreeItems_single
    exact binaryFree_parens (balanced_append (balancedItems_flatten h0) (balanced_flatMap value1 (fun ts => pu .comma ++ ts) (fun ts ht => balanced_append (balanced_atom rfl) (h1 ts ht))))
  | inlineArray first rest ih0 ih1 =>
    intro _ _
    apply produces_bind first.yield _ BalancedItems (BinaryFreeItems rank) (expressionCategory_yield_balanced first rfl)
    intro value0 h0
    apply produces_bind rest.yield _ BalancedItems (BinaryFreeItems rank) (expressionCategory_yield_balanced rest rfl)
    intro value1 h1
    apply produces_pure
    apply binaryFreeItems_single
    exact binaryFree_square (balanced_commaSep (balancedItems_cons (balancedItems_flatten h0) h1))
  | mulDivMod op a b ih0 ih1 =>
    intro hp hl
    change rank < 11 at hl
    have hpreca : a.prec = true := by
      apply all_prec_implies_prec a
      have hall : (Syn.mulDivMod op a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.2
    have hprecb : b.prec = true := by
      apply all_prec_implies_prec b
      have hall : (Syn.mulDivMod op a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.2
    have hr : (Syn.mulDivMod op a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hlevela : rank < a.level := Nat.lt_of_lt_of_le hl hr.1
    have hlevelb : rank < b.level := Nat.lt_of_lt_of_le hl (Nat.le_trans (by decide : 11 ≤ 12) hr.2)
    apply produces_bind a.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih0 hpreca hlevela)
    intro value0 h0
    apply produces_bind b.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih1 hprecb hlevelb)
    intro value1 h1
    apply produces_pure
    apply binaryFreeItems_single
    exact binaryFree_append (binaryFree_append (binaryFreeItems_flatten h0) (binaryFree_mul op (Nat.ne_of_lt hl))) (binaryFreeItems_flatten h1)
  | addSub op a b ih0 ih1 =>
    intro hp hl
    change rank < 10 at hl
    have hpreca : a.prec = true := by
      apply all_prec_implies_prec a
      have hall : (Syn.addSub op a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.2
    have hprecb : b.prec = true := by
      apply all_prec_implies_prec b
      have hall : (Syn.addSub op a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.2
    have hr : (Syn.addSub op a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hlevela : rank < a.level := Nat.lt_of_lt_of_le hl hr.1
    have hlevelb : rank < b.level := Nat.lt_of_lt_of_le hl (Nat.le_trans (by decide : 10 ≤ 11) hr.2)
    apply produces_bind a.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih0 hpreca hlevela)
    intro value0 h0
    apply produces_bind b.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih1 hprecb hlevelb)
    intro value1 h1
    apply produces_pure
    apply binaryFreeItems_single
    exact binaryFree_append (binaryFree_append (binaryFreeItems_flatten h0) (binaryFree_add op (Nat.ne_of_lt hl))) (binaryFreeItems_flatten h1)
  | shift op a b ih0 ih1 =>
    intro hp hl
    change rank < 9 at hl
    have hpreca : a.prec = true := by
      apply all_prec_implies_prec a
      have hall : (Syn.shift op a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.2
    have hprecb : b.prec = true := by
      apply all_prec_implies_prec b
      have hall : (Syn.shift op a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.2
    have hr : (Syn.shift op a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hlevela : rank < a.level := Nat.lt_of_lt_of_le hl hr.1
    have hlevelb : rank < b.level := Nat.lt_of_lt_of_le hl (Nat.le_trans (by decide : 9 ≤ 10) hr.2)
    apply produces_bind a.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih0 hpreca hlevela)
    intro value0 h0
    apply produces_bind b.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih1 hprecb hlevelb)
    intro value1 h1
    apply produces_pure
    apply binaryFreeItems_single
    exact binaryFree_append (binaryFree_append (binaryFreeItems_flatten h0) (binaryFree_shift op (Nat.ne_of_lt hl))) (binaryFreeItems_flatten h1)
  | bitAnd a b ih0 ih1 =>
    intro hp hl
    change rank < 8 at hl
    have hpreca : a.prec = true := by
      apply all_prec_implies_prec a
      have hall : (Syn.bitAnd a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.2
    have hprecb : b.prec = true := by
      apply all_prec_implies_prec b
      have hall : (Syn.bitAnd a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.2
    have hr : (Syn.bitAnd a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hlevela : rank < a.level := Nat.lt_of_lt_of_le hl hr.1
    have hlevelb : rank < b.level := Nat.lt_of_lt_of_le hl (Nat.le_trans (by decide : 8 ≤ 9) hr.2)
    apply produces_bind a.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih0 hpreca hlevela)
    intro value0 h0
    apply produces_bind b.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih1 hprecb hlevelb)
    intro value1 h1
    apply produces_pure
    apply binaryFreeItems_single
    exact binaryFree_append (binaryFree_append (binaryFreeItems_flatten h0) (binaryFree_atom rfl (decide_eq_false (Nat.ne_of_lt hl)))) (binaryFreeItems_flatten h1)
  | bitXor a b ih0 ih1 =>
    intro hp hl
    change rank < 7 at hl
    have hpreca : a.prec = true := by
      apply all_prec_implies_prec a
      have hall : (Syn.bitXor a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.2
    have hprecb : b.prec = true := by
      apply all_prec_implies_prec b
      have hall : (Syn.bitXor a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.2
    have hr : (Syn.bitXor a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hlevela : rank < a.level := Nat.lt_of_lt_of_le hl hr.1
    have hlevelb : rank < b.level := Nat.lt_of_lt_of_le hl (Nat.le_trans (by decide : 7 ≤ 8) hr.2)
    apply produces_bind a.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih0 hpreca hlevela)
    intro value0 h0
    apply produces_bind b.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih1 hprecb hlevelb)
    intro value1 h1
    apply produces_pure
    apply binaryFreeItems_single
    exact binaryFree_append (binaryFree_append (binaryFreeItems_flatten h0) (binaryFree_atom rfl (decide_eq_false (Nat.ne_of_lt hl)))) (binaryFreeItems_flatten h1)
  | bitOr a b ih0 ih1 =>
    intro hp hl
    change rank < 6 at hl
    have hpreca : a.prec = true := by
      apply all_prec_implies_prec a
      have hall : (Syn.bitOr a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.2
    have hprecb : b.prec = true := by
      apply all_prec_implies_prec b
      have hall : (Syn.bitOr a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.2
    have hr : (Syn.bitOr a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hlevela : rank < a.level := Nat.lt_of_lt_of_le hl hr.1
    have hlevelb : rank < b.level := Nat.lt_of_lt_of_le hl (Nat.le_trans (by decide : 6 ≤ 7) hr.2)
    apply produces_bind a.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih0 hpreca hlevela)
    intro value0 h0
    apply produces_bind b.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih1 hprecb hlevelb)
    intro value1 h1
    apply produces_pure
    apply binaryFreeItems_single
    exact binaryFree_append (binaryFree_append (binaryFreeItems_flatten h0) (binaryFree_atom rfl (decide_eq_false (Nat.ne_of_lt hl)))) (binaryFreeItems_flatten h1)
  | order op a b ih0 ih1 =>
    intro hp hl
    change rank < 5 at hl
    have hpreca : a.prec = true := by
      apply all_prec_implies_prec a
      have hall : (Syn.order op a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.2
    have hprecb : b.prec = true := by
      apply all_prec_implies_prec b
      have hall : (Syn.order op a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.2
    have hr : (Syn.order op a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hlevela : rank < a.level := Nat.lt_of_lt_of_le hl hr.1
    have hlevelb : rank < b.level := Nat.lt_of_lt_of_le hl (Nat.le_trans (by decide : 5 ≤ 6) hr.2)
    apply produces_bind a.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih0 hpreca hlevela)
    intro value0 h0
    apply produces_bind b.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih1 hprecb hlevelb)
    intro value1 h1
    apply produces_pure
    apply binaryFreeItems_single
    exact binaryFree_append (binaryFree_append (binaryFreeItems_flatten h0) (binaryFree_order op (Nat.ne_of_lt hl))) (binaryFreeItems_flatten h1)
  | equality op a b ih0 ih1 =>
    intro hp hl
    change rank < 4 at hl
    have hpreca : a.prec = true := by
      apply all_prec_implies_prec a
      have hall : (Syn.equality op a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.2
    have hprecb : b.prec = true := by
      apply all_prec_implies_prec b
      have hall : (Syn.equality op a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.2
    have hr : (Syn.equality op a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hlevela : rank < a.level := Nat.lt_of_lt_of_le hl hr.1
    have hlevelb : rank < b.level := Nat.lt_of_lt_of_le hl (Nat.le_trans (by decide : 4 ≤ 5) hr.2)
    apply produces_bind a.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih0 hpreca hlevela)
    intro value0 h0
    apply produces_bind b.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih1 hprecb hlevelb)
    intro value1 h1
    apply produces_pure
    apply binaryFreeItems_single
    exact binaryFree_append (binaryFree_append (binaryFreeItems_flatten h0) (binaryFree_equality op (Nat.ne_of_lt hl))) (binaryFreeItems_flatten h1)
  | and a b ih0 ih1 =>
    intro hp hl
    change rank < 3 at hl
    have hpreca : a.prec = true := by
      apply all_prec_implies_prec a
      have hall : (Syn.and a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.2
    have hprecb : b.prec = true := by
      apply all_prec_implies_prec b
      have hall : (Syn.and a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.2
    have hr : (Syn.and a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hlevela : rank < a.level := Nat.lt_of_lt_of_le hl hr.1
    have hlevelb : rank < b.level := Nat.lt_of_lt_of_le hl (Nat.le_trans (by decide : 3 ≤ 4) hr.2)
    apply produces_bind a.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih0 hpreca hlevela)
    intro value0 h0
    apply produces_bind b.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih1 hprecb hlevelb)
    intro value1 h1
    apply produces_pure
    apply binaryFreeItems_single
    exact binaryFree_append (binaryFree_append (binaryFreeItems_flatten h0) (binaryFree_atom rfl (decide_eq_false (Nat.ne_of_lt hl)))) (binaryFreeItems_flatten h1)
  | or a b ih0 ih1 =>
    intro hp hl
    change rank < 2 at hl
    have hpreca : a.prec = true := by
      apply all_prec_implies_prec a
      have hall : (Syn.or a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.2
    have hprecb : b.prec = true := by
      apply all_prec_implies_prec b
      have hall : (Syn.or a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.2
    have hr : (Syn.or a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hlevela : rank < a.level := Nat.lt_of_lt_of_le hl hr.1
    have hlevelb : rank < b.level := Nat.lt_of_lt_of_le hl (Nat.le_trans (by decide : 2 ≤ 3) hr.2)
    apply produces_bind a.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih0 hpreca hlevela)
    intro value0 h0
    apply produces_bind b.yield _ (BinaryFreeItems rank) (BinaryFreeItems rank) (ih1 hprecb hlevelb)
    intro value1 h1
    apply produces_pure
    apply binaryFreeItems_single
    exact binaryFree_append (binaryFree_append (binaryFreeItems_flatten h0) (binaryFree_atom rfl (decide_eq_false (Nat.ne_of_lt hl)))) (binaryFreeItems_flatten h1)
  | assign op a b ih0 ih1  =>
    intro _ hl
    have impossible : False := by
      change rank < 0 at hl
      omega
    exact impossible.elim
  | ident name => intro _ _; exact produces_pure _ _ (binaryFreeItems_single (binaryFree_idt name))
  | lit l =>
    intro _ _
    apply produces_bind (litP l) _ (BinaryFree rank) (BinaryFreeItems rank) (litP_binaryFree l)
    intro tokens ht
    exact produces_pure _ _ (binaryFreeItems_single ht)
  | litUnit n u =>
    intro _ _
    exact produces_pure _ _ (binaryFreeItems_single (binaryFree_append (binaryFree_atom rfl rfl) (binaryFree_atom rfl rfl)))
  | elemType ty ht => intro _ _; exact produces_pure _ _ (binaryFreeItems_single (binaryFree_atom rfl rfl))
  | _ => trivial

theorem high_expr_yield_binaryFree (rank : Nat) (hmin : 2 ≤ rank) (hskip : rank ≠ 10)
    (e : Syn .expr) (hp : e.prec = true) (hl : rank < e.level) :
    Produces e.yield (BinaryFreeItems rank) := expression_binary_property rank hmin hskip e hp hl

theorem type_yield_binaryFree (rank : Nat) (hmin : 2 ≤ rank) (hskip : rank ≠ 10)
    (ty : Syn .typeName) : Produces ty.yield (BinaryFreeItems rank) :=
  expression_binary_property rank hmin hskip ty

theorem high_expr_derives_binaryFree (rank : Nat) (hmin : 2 ≤ rank) (hskip : rank ≠ 10)
    (e : Syn .expr) (ts : List Tok) (hp : e.prec = true) (hl : rank < e.level)
    (hd : e.Derives ts) : BinaryFree rank ts := by
  obtain ⟨L, ht⟩ := hd
  have hy : e.yield L = some ([ts], []) := (expr_toks_iff e L ts).mp ht
  exact high_expr_yield_binaryFree rank hmin hskip e hp hl L [ts] [] hy ts
    (List.mem_cons.mpr (Or.inl rfl))

end Solidity.Frontend.ExpressionUniqueness
