import Solidity.Frontend.ExpressionUniqueness.UnaryFreeAlgebra
import Solidity.Frontend.ExpressionUniqueness.ExpressionLowFree

/-!
# Original certified roots above unary operators exclude their outer markers

All six prefix and both suffix tokens are absent at delimiter depth zero for
roots of level at least15. Descendant unary expressions remain allowed inside
actual enclosures. Types and call arguments satisfy the same token invariant.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def UnaryYieldProperty {c : Cat} (e : Syn c) : Prop :=
  match c with
  | .expr => e.prec = true → 15 ≤ e.level → Produces e.yield UnaryFreeItems
  | .typeName | .callArgs => Produces e.yield UnaryFreeItems
  | _ => True

theorem expression_unary_property {c : Cat} (e : Syn c) : UnaryYieldProperty e := by
  induction e with
  | positional es ih =>
    apply produces_bind es.yield _ BalancedItems UnaryFreeItems (expressionCategory_yield_balanced es rfl)
    intro items hi
    exact produces_pure _ _ (unaryFreeItems_single (unaryFree_parens (balanced_commaSep hi)))
  | named args ih =>
    apply produces_bind args.yield _ BalancedItems UnaryFreeItems (expressionCategory_yield_balanced args rfl)
    intro items hi
    exact produces_pure _ _ (unaryFreeItems_single (unaryFree_parens (balanced_braces (balanced_commaSep hi))))
  | elem ty => exact produces_pure _ _ (unaryFreeItems_single (unaryFree_elem ty))
  | userType path => exact produces_pure _ _ (unaryFreeItems_single (unaryFree_path path))
  | array ty len ihTy ihLen =>
    apply produces_bind ty.yield _ UnaryFreeItems UnaryFreeItems (ihTy)
    intro types ht
    apply produces_bind len.yield _ BalancedItems UnaryFreeItems (expressionCategory_yield_balanced len rfl)
    intro lengths hl
    apply produces_pure
    apply unaryFreeItems_single
    simpa only [List.append_assoc] using unaryFree_append (unaryFreeItems_flatten ht)
      (unaryFree_square (balancedItems_flatten hl))
  | mapping key keyName value valueName ih =>
    apply produces_bind value.yield _ BalancedItems UnaryFreeItems (expressionCategory_yield_balanced value rfl)
    intro items hi
    apply produces_pure
    apply unaryFreeItems_single
    exact unaryFree_append (unaryFree_tk .mapping rfl) (unaryFree_parens
      (balanced_append (balanced_append (balanced_append (balanced_append
        (balanced_mapping_key key) (balanced_optToks idt balanced_idt keyName))
        (balanced_atom rfl)) (balancedItems_flatten hi))
        (balanced_optToks idt balanced_idt valueName)))
  | fnType ps vis mu rets ihPs ihRets =>
    apply produces_bind_all popAttrs _ UnaryFreeItems
    intro order
    apply produces_bind ps.yield _ BalancedItems UnaryFreeItems (expressionCategory_yield_balanced ps rfl)
    intro params hp
    have hs : UnaryFreeAttrs (single .vis (optToks Visibility.toks vis) ++
        single .mutab (optToks Mutability.toks mu)) :=
      unaryFreeAttrs_append (unaryFree_single _ _ (unaryFree_optToks Visibility.toks unaryFree_visibility vis))
        (unaryFree_single _ _ (unaryFree_optToks Mutability.toks unaryFree_mutability mu))
    apply produces_bind (attrsP _ [] order) _ UnaryFree UnaryFreeItems
      (attrsP_unaryFree _ [] order hs unaryFreeItems_nil)
    intro attrs ha
    apply produces_bind rets.yield _ BalancedItems UnaryFreeItems (expressionCategory_yield_balanced rets rfl)
    intro returns hr
    apply produces_pure
    apply unaryFreeItems_single
    apply unaryFree_append (unaryFree_append (unaryFree_append (unaryFree_tk .function rfl)
      (unaryFree_parens (balanced_commaSep hp))) ha)
    split
    · exact unaryFree_nil
    · exact unaryFree_append (unaryFree_tk .returns rfl) (unaryFree_parens (balanced_commaSep hr))
  | index e i ih0 ih1 =>
    intro hp _
    have hprece : e.prec = true := by
      apply all_prec_implies_prec e
      have hall : (Syn.index e i).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.2
    have hr : (Syn.index e i).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hlevele : 15 ≤ e.level := by omega
    apply produces_bind e.yield _ UnaryFreeItems UnaryFreeItems (ih0 hprece hlevele)
    intro value0 h0
    apply produces_bind i.yield _ BalancedItems UnaryFreeItems (expressionCategory_yield_balanced i rfl)
    intro value1 h1
    apply produces_pure
    apply unaryFreeItems_single
    simpa only [List.append_assoc] using unaryFree_append (unaryFreeItems_flatten h0) (unaryFree_square (balancedItems_flatten h1))
  | slice e i j ih0 ih1 ih2 =>
    intro hp _
    have hprece : e.prec = true := by
      apply all_prec_implies_prec e
      have hall : (Syn.slice e i j).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.1.2
    have hr : (Syn.slice e i j).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hlevele : 15 ≤ e.level := by omega
    apply produces_bind e.yield _ UnaryFreeItems UnaryFreeItems (ih0 hprece hlevele)
    intro value0 h0
    apply produces_bind i.yield _ BalancedItems UnaryFreeItems (expressionCategory_yield_balanced i rfl)
    intro value1 h1
    apply produces_bind j.yield _ BalancedItems UnaryFreeItems (expressionCategory_yield_balanced j rfl)
    intro value2 h2
    apply produces_pure
    apply unaryFreeItems_single
    simpa only [List.append_assoc] using unaryFree_append (unaryFreeItems_flatten h0) (unaryFree_square (balanced_append (balanced_append (balancedItems_flatten h1) (balanced_atom rfl)) (balancedItems_flatten h2)))
  | member e name ih0 =>
    intro hp _
    have hprece : e.prec = true := by
      apply all_prec_implies_prec e
      have hall : (Syn.member e name).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.2
    have hr : (Syn.member e name).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hlevele : 15 ≤ e.level := by omega
    apply produces_bind e.yield _ UnaryFreeItems UnaryFreeItems (ih0 hprece hlevele)
    intro value0 h0
    apply produces_pure
    apply unaryFreeItems_single
    apply unaryFree_append (unaryFree_append (unaryFreeItems_flatten h0) (unaryFree_atom rfl rfl))
    split <;> exact unaryFree_atom rfl rfl
  | callOptions e first rest ih0 ih1 ih2 =>
    intro hp _
    have hprece : e.prec = true := by
      apply all_prec_implies_prec e
      have hall : (Syn.callOptions e first rest).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.1.2
    have hr : (Syn.callOptions e first rest).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, decide_eq_true_eq] at hr
    have hlevele : 15 ≤ e.level := by omega
    apply produces_bind e.yield _ UnaryFreeItems UnaryFreeItems (ih0 hprece hlevele)
    intro value0 h0
    apply produces_bind first.yield _ BalancedItems UnaryFreeItems (expressionCategory_yield_balanced first rfl)
    intro value1 h1
    apply produces_bind rest.yield _ BalancedItems UnaryFreeItems (expressionCategory_yield_balanced rest rfl)
    intro value2 h2
    apply produces_pure
    apply unaryFreeItems_single
    exact unaryFree_append (unaryFreeItems_flatten h0) (unaryFree_braces (balanced_commaSep (balancedItems_cons (balancedItems_flatten h1) h2)))
  | call e args ih0 ih1 =>
    intro hp _
    have hprece : e.prec = true := by
      apply all_prec_implies_prec e
      have hall : (Syn.call e args).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.2
    have hr : (Syn.call e args).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, decide_eq_true_eq] at hr
    have hlevele : 15 ≤ e.level := by omega
    apply produces_bind e.yield _ UnaryFreeItems UnaryFreeItems (ih0 hprece hlevele)
    intro value0 h0
    apply produces_bind args.yield _ UnaryFreeItems UnaryFreeItems (ih1)
    intro value1 h1
    apply produces_pure
    apply unaryFreeItems_single
    exact unaryFree_append (unaryFreeItems_flatten h0) (unaryFreeItems_flatten h1)
  | payableConv args ih0 =>
    intro _ _
    apply produces_bind args.yield _ UnaryFreeItems UnaryFreeItems (ih0)
    intro value0 h0
    apply produces_pure
    apply unaryFreeItems_single
    exact unaryFree_append (unaryFree_tk .payable rfl) (unaryFreeItems_flatten h0)
  | metaType ty ih0 =>
    intro _ _
    apply produces_bind ty.yield _ BalancedItems UnaryFreeItems (expressionCategory_yield_balanced ty rfl)
    intro value0 h0
    apply produces_pure
    apply unaryFreeItems_single
    exact unaryFree_append (unaryFree_tk .type_ rfl) (unaryFree_parens (balancedItems_flatten h0))
  | unaryPrefix op e ih0 =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 13) impossible)
  | unarySuffix op e ih0 =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 14) impossible)
  | exp a b ih0 ih1 =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 12) impossible)
  | cond c a b ih0 ih1 ih2 =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 1) impossible)
  | new ty ih0 =>
    intro _ _
    apply produces_bind ty.yield _ UnaryFreeItems UnaryFreeItems (ih0)
    intro value0 h0
    apply produces_pure
    apply unaryFreeItems_single
    exact unaryFree_append (unaryFree_tk .new rfl) (unaryFreeItems_flatten h0)
  | tuple first rest ih0 ih1 =>
    intro _ _
    apply produces_bind first.yield _ BalancedItems UnaryFreeItems (expressionCategory_yield_balanced first rfl)
    intro value0 h0
    apply produces_bind rest.yield _ BalancedItems UnaryFreeItems (expressionCategory_yield_balanced rest rfl)
    intro value1 h1
    apply produces_pure
    apply unaryFreeItems_single
    exact unaryFree_parens (balanced_append (balancedItems_flatten h0) (balanced_flatMap value1 (fun ts => pu .comma ++ ts) (fun ts ht => balanced_append (balanced_atom rfl) (h1 ts ht))))
  | inlineArray first rest ih0 ih1 =>
    intro _ _
    apply produces_bind first.yield _ BalancedItems UnaryFreeItems (expressionCategory_yield_balanced first rfl)
    intro value0 h0
    apply produces_bind rest.yield _ BalancedItems UnaryFreeItems (expressionCategory_yield_balanced rest rfl)
    intro value1 h1
    apply produces_pure
    apply unaryFreeItems_single
    exact unaryFree_square (balanced_commaSep (balancedItems_cons (balancedItems_flatten h0) h1))
  | mulDivMod op a b ih0 ih1 =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 11) impossible)
  | addSub op a b ih0 ih1 =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 10) impossible)
  | shift op a b ih0 ih1 =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 9) impossible)
  | bitAnd a b ih0 ih1 =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 8) impossible)
  | bitXor a b ih0 ih1 =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 7) impossible)
  | bitOr a b ih0 ih1 =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 6) impossible)
  | order op a b ih0 ih1 =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 5) impossible)
  | equality op a b ih0 ih1 =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 4) impossible)
  | and a b ih0 ih1 =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 3) impossible)
  | or a b ih0 ih1 =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 2) impossible)
  | assign op a b ih0 ih1 =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 0) impossible)
  | ident name => intro _ _; exact produces_pure _ _ (unaryFreeItems_single (unaryFree_idt name))
  | lit l =>
    intro _ _
    apply produces_bind (litP l) _ UnaryFree UnaryFreeItems (litP_unaryFree l)
    intro tokens ht
    exact produces_pure _ _ (unaryFreeItems_single ht)
  | litUnit n u =>
    intro _ _
    exact produces_pure _ _ (unaryFreeItems_single (unaryFree_append (unaryFree_atom rfl rfl) (unaryFree_atom rfl rfl)))
  | elemType ty ht => intro _ _; exact produces_pure _ _ (unaryFreeItems_single (unaryFree_atom rfl rfl))
  | _ => trivial

theorem high_expr_yield_unaryFree (e : Syn .expr) (hp : e.prec = true) (hl : 15 ≤ e.level) :
    Produces e.yield UnaryFreeItems := expression_unary_property e hp hl

theorem type_yield_unaryFree (ty : Syn .typeName) : Produces ty.yield UnaryFreeItems :=
  expression_unary_property ty

theorem high_expr_derives_unaryFree (e : Syn .expr) (ts : List Tok)
    (hp : e.prec = true) (hl : 15 ≤ e.level) (hd : e.Derives ts) : UnaryFree ts := by
  obtain ⟨L, ht⟩ := hd
  have hy := (expr_toks_iff e L ts).mp ht
  exact high_expr_yield_unaryFree e hp hl L [ts] [] hy ts (List.mem_cons.mpr (Or.inl rfl))

end Solidity.Frontend.ExpressionUniqueness
