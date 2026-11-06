import Solidity.Frontend.ExpressionUniqueness.LowFreeAlgebra
import Solidity.Frontend.Checked.Prec

/-!
# Certified high-precedence expressions avoid loose-root markers

Types and call argument syntax are loose-root-free at their outer level.
Expression nodes use only the existing recursive Syn.prec and root level bound.
No desired token split or expression uniqueness assumption is introduced.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem all_prec_root {c : Cat} (e : Syn c) (h : e.all Syn.precNode = true) :
    e.precNode = true := by
  cases e <;> simp only [Syn.all, Bool.and_eq_true] at h <;> first
    | exact h
    | exact h.1
    | exact h.1.1
    | exact h.1.1.1
    | exact h.1.1.1.1
    | exact h.1.1.1.1.1

theorem all_prec_implies_prec {c : Cat} (e : Syn c) (h : e.all Syn.precNode = true) :
    e.prec = true := by
  exact Bool.and_eq_true_iff.mpr ⟨all_prec_root e h, h⟩

def LowYieldProperty {c : Cat} (e : Syn c) : Prop :=
  match c with
  | .expr => e.prec = true → 2 ≤ e.level → Produces e.yield LowFreeItems
  | .typeName | .callArgs => Produces e.yield LowFreeItems
  | _ => True

theorem expression_low_property {c : Cat} (e : Syn c) : LowYieldProperty e := by
  induction e with
  | positional es ih =>
    apply produces_bind es.yield _ BalancedItems LowFreeItems (expressionCategory_yield_balanced es rfl)
    intro items hi
    exact produces_pure _ _ (lowFreeItems_single (lowFree_parens (balanced_commaSep hi)))
  | named args ih =>
    apply produces_bind args.yield _ BalancedItems LowFreeItems (expressionCategory_yield_balanced args rfl)
    intro items hi
    exact produces_pure _ _ (lowFreeItems_single (lowFree_parens (balanced_braces (balanced_commaSep hi))))
  | elem ty => exact produces_pure _ _ (lowFreeItems_single (lowFree_elem ty))
  | userType path => exact produces_pure _ _ (lowFreeItems_single (lowFree_path path))
  | array ty len ihTy ihLen =>
    apply produces_bind ty.yield _ LowFreeItems LowFreeItems (ihTy)
    intro types ht
    apply produces_bind len.yield _ BalancedItems LowFreeItems (expressionCategory_yield_balanced len rfl)
    intro lengths hl
    apply produces_pure
    apply lowFreeItems_single
    simpa only [List.append_assoc] using lowFree_append (lowFreeItems_flatten ht)
      (lowFree_square (balancedItems_flatten hl))
  | mapping key keyName value valueName ih =>
    apply produces_bind value.yield _ BalancedItems LowFreeItems (expressionCategory_yield_balanced value rfl)
    intro items hi
    apply produces_pure
    apply lowFreeItems_single
    exact lowFree_append (lowFree_tk .mapping) (lowFree_parens
      (balanced_append (balanced_append (balanced_append (balanced_append
        (balanced_mapping_key key) (balanced_optToks idt balanced_idt keyName))
        (balanced_atom rfl)) (balancedItems_flatten hi))
        (balanced_optToks idt balanced_idt valueName)))
  | fnType ps vis mu rets ihPs ihRets =>
    apply produces_bind_all popAttrs _ LowFreeItems
    intro order
    apply produces_bind ps.yield _ BalancedItems LowFreeItems (expressionCategory_yield_balanced ps rfl)
    intro params hp
    have hs : LowFreeAttrs (single .vis (optToks Visibility.toks vis) ++
        single .mutab (optToks Mutability.toks mu)) :=
      lowFreeAttrs_append (lowFree_single _ _ (lowFree_optToks Visibility.toks lowFree_visibility vis))
        (lowFree_single _ _ (lowFree_optToks Mutability.toks lowFree_mutability mu))
    apply produces_bind (attrsP _ [] order) _ LowFree LowFreeItems
      (attrsP_lowFree _ [] order hs lowFreeItems_nil)
    intro attrs ha
    apply produces_bind rets.yield _ BalancedItems LowFreeItems (expressionCategory_yield_balanced rets rfl)
    intro returns hr
    apply produces_pure
    apply lowFreeItems_single
    apply lowFree_append (lowFree_append (lowFree_append (lowFree_tk .function)
      (lowFree_parens (balanced_commaSep hp))) ha)
    split
    · exact lowFree_nil
    · exact lowFree_append (lowFree_tk .returns) (lowFree_parens (balanced_commaSep hr))
  | index e i ih0 ih1 =>
    intro hp _
    have hprece : e.prec = true := by
      apply all_prec_implies_prec e
      have hall : (Syn.index e i).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.2
    have hr : (Syn.index e i).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hlevele : 2 ≤ e.level := by omega
    apply produces_bind e.yield _ LowFreeItems LowFreeItems (ih0 hprece hlevele)
    intro value0 h0
    apply produces_bind i.yield _ BalancedItems LowFreeItems (expressionCategory_yield_balanced i rfl)
    intro value1 h1
    apply produces_pure
    apply lowFreeItems_single
    simpa only [List.append_assoc] using lowFree_append (lowFreeItems_flatten h0) (lowFree_square (balancedItems_flatten h1))
  | slice e i j ih0 ih1 ih2 =>
    intro hp _
    have hprece : e.prec = true := by
      apply all_prec_implies_prec e
      have hall : (Syn.slice e i j).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.1.2
    have hr : (Syn.slice e i j).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hlevele : 2 ≤ e.level := by omega
    apply produces_bind e.yield _ LowFreeItems LowFreeItems (ih0 hprece hlevele)
    intro value0 h0
    apply produces_bind i.yield _ BalancedItems LowFreeItems (expressionCategory_yield_balanced i rfl)
    intro value1 h1
    apply produces_bind j.yield _ BalancedItems LowFreeItems (expressionCategory_yield_balanced j rfl)
    intro value2 h2
    apply produces_pure
    apply lowFreeItems_single
    simpa only [List.append_assoc] using lowFree_append (lowFreeItems_flatten h0) (lowFree_square (balanced_append (balanced_append (balancedItems_flatten h1) (balanced_atom rfl)) (balancedItems_flatten h2)))
  | member e name ih0 =>
    intro hp _
    have hprece : e.prec = true := by
      apply all_prec_implies_prec e
      have hall : (Syn.member e name).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.2
    have hr : (Syn.member e name).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hlevele : 2 ≤ e.level := by omega
    apply produces_bind e.yield _ LowFreeItems LowFreeItems (ih0 hprece hlevele)
    intro value0 h0
    apply produces_pure
    apply lowFreeItems_single
    apply lowFree_append (lowFree_append (lowFreeItems_flatten h0) (lowFree_atom rfl rfl))
    split <;> exact lowFree_atom rfl rfl
  | callOptions e first rest ih0 ih1 ih2 =>
    intro hp _
    have hprece : e.prec = true := by
      apply all_prec_implies_prec e
      have hall : (Syn.callOptions e first rest).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.1.2
    have hr : (Syn.callOptions e first rest).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, decide_eq_true_eq] at hr
    have hlevele : 2 ≤ e.level := by omega
    apply produces_bind e.yield _ LowFreeItems LowFreeItems (ih0 hprece hlevele)
    intro value0 h0
    apply produces_bind first.yield _ BalancedItems LowFreeItems (expressionCategory_yield_balanced first rfl)
    intro value1 h1
    apply produces_bind rest.yield _ BalancedItems LowFreeItems (expressionCategory_yield_balanced rest rfl)
    intro value2 h2
    apply produces_pure
    apply lowFreeItems_single
    exact lowFree_append (lowFreeItems_flatten h0) (lowFree_braces (balanced_commaSep (balancedItems_cons (balancedItems_flatten h1) h2)))
  | call e args ih0 ih1 =>
    intro hp _
    have hprece : e.prec = true := by
      apply all_prec_implies_prec e
      have hall : (Syn.call e args).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.2
    have hr : (Syn.call e args).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, decide_eq_true_eq] at hr
    have hlevele : 2 ≤ e.level := by omega
    apply produces_bind e.yield _ LowFreeItems LowFreeItems (ih0 hprece hlevele)
    intro value0 h0
    apply produces_bind args.yield _ LowFreeItems LowFreeItems (ih1)
    intro value1 h1
    apply produces_pure
    apply lowFreeItems_single
    exact lowFree_append (lowFreeItems_flatten h0) (lowFreeItems_flatten h1)
  | payableConv args ih0 =>
    intro _ _
    apply produces_bind args.yield _ LowFreeItems LowFreeItems (ih0)
    intro value0 h0
    apply produces_pure
    apply lowFreeItems_single
    exact lowFree_append (lowFree_tk .payable) (lowFreeItems_flatten h0)
  | metaType ty ih0 =>
    intro _ _
    apply produces_bind ty.yield _ BalancedItems LowFreeItems (expressionCategory_yield_balanced ty rfl)
    intro value0 h0
    apply produces_pure
    apply lowFreeItems_single
    exact lowFree_append (lowFree_tk .type_) (lowFree_parens (balancedItems_flatten h0))
  | unaryPrefix op e ih0 =>
    intro hp _
    have hprece : e.prec = true := by
      apply all_prec_implies_prec e
      have hall : (Syn.unaryPrefix op e).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.2
    have hr : (Syn.unaryPrefix op e).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hlevele : 2 ≤ e.level := by omega
    apply produces_bind e.yield _ LowFreeItems LowFreeItems (ih0 hprece hlevele)
    intro value0 h0
    apply produces_pure
    apply lowFreeItems_single
    exact lowFree_append (lowFree_prefix op) (lowFreeItems_flatten h0)
  | unarySuffix op e ih0 =>
    intro hp _
    have hprece : e.prec = true := by
      apply all_prec_implies_prec e
      have hall : (Syn.unarySuffix op e).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.2
    have hr : (Syn.unarySuffix op e).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, decide_eq_true_eq] at hr
    have hlevele : 2 ≤ e.level := by omega
    apply produces_bind e.yield _ LowFreeItems LowFreeItems (ih0 hprece hlevele)
    intro value0 h0
    apply produces_pure
    apply lowFreeItems_single
    exact lowFree_append (lowFreeItems_flatten h0) (lowFree_suffix op)
  | exp a b ih0 ih1 =>
    intro hp _
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
    have hlevela : 2 ≤ a.level := by omega
    have hlevelb : 2 ≤ b.level := by omega
    apply produces_bind a.yield _ LowFreeItems LowFreeItems (ih0 hpreca hlevela)
    intro value0 h0
    apply produces_bind b.yield _ LowFreeItems LowFreeItems (ih1 hprecb hlevelb)
    intro value1 h1
    apply produces_pure
    apply lowFreeItems_single
    exact lowFree_append (lowFree_append (lowFreeItems_flatten h0) (lowFree_atom rfl rfl)) (lowFreeItems_flatten h1)
  | cond c a b ih0 ih1 ih2 =>
    intro _ hl
    change 2 ≤ 1 at hl
    omega
  | new ty ih0 =>
    intro _ _
    apply produces_bind ty.yield _ LowFreeItems LowFreeItems (ih0)
    intro value0 h0
    apply produces_pure
    apply lowFreeItems_single
    exact lowFree_append (lowFree_tk .new) (lowFreeItems_flatten h0)
  | tuple first rest ih0 ih1 =>
    intro _ _
    apply produces_bind first.yield _ BalancedItems LowFreeItems (expressionCategory_yield_balanced first rfl)
    intro value0 h0
    apply produces_bind rest.yield _ BalancedItems LowFreeItems (expressionCategory_yield_balanced rest rfl)
    intro value1 h1
    apply produces_pure
    apply lowFreeItems_single
    exact lowFree_parens (balanced_append (balancedItems_flatten h0) (balanced_flatMap value1 (fun ts => pu .comma ++ ts) (fun ts ht => balanced_append (balanced_atom rfl) (h1 ts ht))))
  | inlineArray first rest ih0 ih1 =>
    intro _ _
    apply produces_bind first.yield _ BalancedItems LowFreeItems (expressionCategory_yield_balanced first rfl)
    intro value0 h0
    apply produces_bind rest.yield _ BalancedItems LowFreeItems (expressionCategory_yield_balanced rest rfl)
    intro value1 h1
    apply produces_pure
    apply lowFreeItems_single
    exact lowFree_square (balanced_commaSep (balancedItems_cons (balancedItems_flatten h0) h1))
  | mulDivMod op a b ih0 ih1 =>
    intro hp _
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
    have hlevela : 2 ≤ a.level := by omega
    have hlevelb : 2 ≤ b.level := by omega
    apply produces_bind a.yield _ LowFreeItems LowFreeItems (ih0 hpreca hlevela)
    intro value0 h0
    apply produces_bind b.yield _ LowFreeItems LowFreeItems (ih1 hprecb hlevelb)
    intro value1 h1
    apply produces_pure
    apply lowFreeItems_single
    exact lowFree_append (lowFree_append (lowFreeItems_flatten h0) (lowFree_mul op)) (lowFreeItems_flatten h1)
  | addSub op a b ih0 ih1 =>
    intro hp _
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
    have hlevela : 2 ≤ a.level := by omega
    have hlevelb : 2 ≤ b.level := by omega
    apply produces_bind a.yield _ LowFreeItems LowFreeItems (ih0 hpreca hlevela)
    intro value0 h0
    apply produces_bind b.yield _ LowFreeItems LowFreeItems (ih1 hprecb hlevelb)
    intro value1 h1
    apply produces_pure
    apply lowFreeItems_single
    exact lowFree_append (lowFree_append (lowFreeItems_flatten h0) (lowFree_add op)) (lowFreeItems_flatten h1)
  | shift op a b ih0 ih1 =>
    intro hp _
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
    have hlevela : 2 ≤ a.level := by omega
    have hlevelb : 2 ≤ b.level := by omega
    apply produces_bind a.yield _ LowFreeItems LowFreeItems (ih0 hpreca hlevela)
    intro value0 h0
    apply produces_bind b.yield _ LowFreeItems LowFreeItems (ih1 hprecb hlevelb)
    intro value1 h1
    apply produces_pure
    apply lowFreeItems_single
    exact lowFree_append (lowFree_append (lowFreeItems_flatten h0) (lowFree_shift op)) (lowFreeItems_flatten h1)
  | bitAnd a b ih0 ih1 =>
    intro hp _
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
    have hlevela : 2 ≤ a.level := by omega
    have hlevelb : 2 ≤ b.level := by omega
    apply produces_bind a.yield _ LowFreeItems LowFreeItems (ih0 hpreca hlevela)
    intro value0 h0
    apply produces_bind b.yield _ LowFreeItems LowFreeItems (ih1 hprecb hlevelb)
    intro value1 h1
    apply produces_pure
    apply lowFreeItems_single
    exact lowFree_append (lowFree_append (lowFreeItems_flatten h0) (lowFree_atom rfl rfl)) (lowFreeItems_flatten h1)
  | bitXor a b ih0 ih1 =>
    intro hp _
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
    have hlevela : 2 ≤ a.level := by omega
    have hlevelb : 2 ≤ b.level := by omega
    apply produces_bind a.yield _ LowFreeItems LowFreeItems (ih0 hpreca hlevela)
    intro value0 h0
    apply produces_bind b.yield _ LowFreeItems LowFreeItems (ih1 hprecb hlevelb)
    intro value1 h1
    apply produces_pure
    apply lowFreeItems_single
    exact lowFree_append (lowFree_append (lowFreeItems_flatten h0) (lowFree_atom rfl rfl)) (lowFreeItems_flatten h1)
  | bitOr a b ih0 ih1 =>
    intro hp _
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
    have hlevela : 2 ≤ a.level := by omega
    have hlevelb : 2 ≤ b.level := by omega
    apply produces_bind a.yield _ LowFreeItems LowFreeItems (ih0 hpreca hlevela)
    intro value0 h0
    apply produces_bind b.yield _ LowFreeItems LowFreeItems (ih1 hprecb hlevelb)
    intro value1 h1
    apply produces_pure
    apply lowFreeItems_single
    exact lowFree_append (lowFree_append (lowFreeItems_flatten h0) (lowFree_atom rfl rfl)) (lowFreeItems_flatten h1)
  | order op a b ih0 ih1 =>
    intro hp _
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
    have hlevela : 2 ≤ a.level := by omega
    have hlevelb : 2 ≤ b.level := by omega
    apply produces_bind a.yield _ LowFreeItems LowFreeItems (ih0 hpreca hlevela)
    intro value0 h0
    apply produces_bind b.yield _ LowFreeItems LowFreeItems (ih1 hprecb hlevelb)
    intro value1 h1
    apply produces_pure
    apply lowFreeItems_single
    exact lowFree_append (lowFree_append (lowFreeItems_flatten h0) (lowFree_order op)) (lowFreeItems_flatten h1)
  | equality op a b ih0 ih1 =>
    intro hp _
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
    have hlevela : 2 ≤ a.level := by omega
    have hlevelb : 2 ≤ b.level := by omega
    apply produces_bind a.yield _ LowFreeItems LowFreeItems (ih0 hpreca hlevela)
    intro value0 h0
    apply produces_bind b.yield _ LowFreeItems LowFreeItems (ih1 hprecb hlevelb)
    intro value1 h1
    apply produces_pure
    apply lowFreeItems_single
    exact lowFree_append (lowFree_append (lowFreeItems_flatten h0) (lowFree_equality op)) (lowFreeItems_flatten h1)
  | and a b ih0 ih1 =>
    intro hp _
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
    have hlevela : 2 ≤ a.level := by omega
    have hlevelb : 2 ≤ b.level := by omega
    apply produces_bind a.yield _ LowFreeItems LowFreeItems (ih0 hpreca hlevela)
    intro value0 h0
    apply produces_bind b.yield _ LowFreeItems LowFreeItems (ih1 hprecb hlevelb)
    intro value1 h1
    apply produces_pure
    apply lowFreeItems_single
    exact lowFree_append (lowFree_append (lowFreeItems_flatten h0) (lowFree_atom rfl rfl)) (lowFreeItems_flatten h1)
  | or a b ih0 ih1 =>
    intro hp _
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
    have hlevela : 2 ≤ a.level := by omega
    have hlevelb : 2 ≤ b.level := by omega
    apply produces_bind a.yield _ LowFreeItems LowFreeItems (ih0 hpreca hlevela)
    intro value0 h0
    apply produces_bind b.yield _ LowFreeItems LowFreeItems (ih1 hprecb hlevelb)
    intro value1 h1
    apply produces_pure
    apply lowFreeItems_single
    exact lowFree_append (lowFree_append (lowFreeItems_flatten h0) (lowFree_atom rfl rfl)) (lowFreeItems_flatten h1)
  | assign op a b ih0 ih1 =>
    intro _ hl
    change 2 ≤ 0 at hl
    omega
  | ident name => intro _ _; exact produces_pure _ _ (lowFreeItems_single (lowFree_idt name))
  | lit l =>
    intro _ _
    apply produces_bind (litP l) _ LowFree LowFreeItems (litP_lowFree l)
    intro tokens ht
    exact produces_pure _ _ (lowFreeItems_single ht)
  | litUnit n u =>
    intro _ _
    exact produces_pure _ _ (lowFreeItems_single (lowFree_append (lowFree_atom rfl rfl) (lowFree_atom rfl rfl)))
  | elemType ty ht => intro _ _; exact produces_pure _ _ (lowFreeItems_single (lowFree_atom rfl rfl))
  | _ => trivial

theorem high_expr_yield_lowFree (e : Syn .expr) (hp : e.prec = true) (hl : 2 ≤ e.level) :
    Produces e.yield LowFreeItems := expression_low_property e hp hl

theorem type_yield_lowFree (ty : Syn .typeName) : Produces ty.yield LowFreeItems :=
  expression_low_property ty

theorem high_expr_derives_lowFree (e : Syn .expr) (ts : List Tok)
    (hp : e.prec = true) (hl : 2 ≤ e.level) (hd : e.Derives ts) : LowFree ts := by
  obtain ⟨L, ht⟩ := hd
  have hy := (expr_toks_iff e L ts).mp ht
  exact high_expr_yield_lowFree e hp hl L [ts] [] hy ts (List.mem_cons.mpr (Or.inl rfl))

end Solidity.Frontend.ExpressionUniqueness
