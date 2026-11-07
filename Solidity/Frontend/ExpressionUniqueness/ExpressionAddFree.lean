import Solidity.Frontend.ExpressionUniqueness.AddFreeAlgebra
import Solidity.Frontend.ExpressionUniqueness.ExpressionLowFree

/-!
# Certified roots above addition are additively free from an unfinished state

The entry bit is false for expressions. Types and call arguments finish from
either entry bit. Every child precedence and bound is derived from existing
Syn.prec; arbitrary initial and remaining printer layouts are retained.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def AddFreeItems (items : List (List Tok)) : Prop := AddFree items.flatten
def AddDoneItems (items : List (List Tok)) : Prop := AddDone items.flatten

theorem addFreeItems_single {ts : List Tok} (h : AddFree ts) : AddFreeItems [ts] := by
  simpa only [AddFreeItems, List.flatten_cons, List.flatten_nil, List.append_nil] using h

theorem addDoneItems_single {ts : List Tok} (h : AddDone ts) : AddDoneItems [ts] := by
  simpa only [AddDoneItems, List.flatten_cons, List.flatten_nil, List.append_nil] using h

def AddYieldProperty {c : Cat} (e : Syn c) : Prop :=
  match c with
  | .expr => e.prec = true → 10 < e.level → Produces e.yield AddFreeItems
  | .typeName | .callArgs => Produces e.yield AddDoneItems
  | _ => True

theorem expression_add_property {c : Cat} (e : Syn c) : AddYieldProperty e := by
  induction e with
  | positional es ih =>
    apply produces_bind es.yield _ BalancedItems AddDoneItems (expressionCategory_yield_balanced es rfl)
    intro items hi
    apply produces_pure
    apply addDoneItems_single
    exact addDone_parens (balanced_commaSep hi)
  | named args ih =>
    apply produces_bind args.yield _ BalancedItems AddDoneItems (expressionCategory_yield_balanced args rfl)
    intro items hi
    apply produces_pure
    apply addDoneItems_single
    exact addDone_parens (balanced_braces (balanced_commaSep hi))
  | elem ty => exact produces_pure _ _ (addDoneItems_single (addDone_elem ty))
  | userType path => exact produces_pure _ _ (addDoneItems_single (addDone_path path))
  | array ty len ihTy ihLen =>
    apply produces_bind ty.yield _ AddDoneItems AddDoneItems ihTy
    intro types ht
    apply produces_bind len.yield _ BalancedItems AddDoneItems (expressionCategory_yield_balanced len rfl)
    intro lengths hl
    apply produces_pure
    apply addDoneItems_single
    simpa only [List.append_assoc] using addDone_stable_append ht (addDone_stable (addDone_square (balancedItems_flatten hl)))
  | mapping key keyName value valueName ih =>
    apply produces_bind value.yield _ BalancedItems AddDoneItems (expressionCategory_yield_balanced value rfl)
    intro items hi
    apply produces_pure
    apply addDoneItems_single
    exact addDone_stable_append (addDone_atom _ rfl (fun _ => rfl) (fun _ => rfl))
      (addDone_stable (addDone_parens (balanced_append (balanced_append (balanced_append (balanced_append
        (balanced_mapping_key key) (balanced_optToks idt balanced_idt keyName))
        (balanced_atom rfl)) (balancedItems_flatten hi)) (balanced_optToks idt balanced_idt valueName))))
  | fnType ps vis mu rets ihPs ihRets =>
    apply produces_bind_all popAttrs _ AddDoneItems
    intro order
    apply produces_bind ps.yield _ BalancedItems AddDoneItems (expressionCategory_yield_balanced ps rfl)
    intro params hp
    have hs : AddStableAttrs (single .vis (optToks Visibility.toks vis) ++
        single .mutab (optToks Mutability.toks mu)) :=
      addStableAttrs_append (addStable_single _ _ (addStable_optToks Visibility.toks addStable_visibility vis))
        (addStable_single _ _ (addStable_optToks Mutability.toks addStable_mutability mu))
    apply produces_bind (attrsP _ [] order) _ AddStable AddDoneItems
      (attrsP_addStable _ [] order hs addStableItems_nil)
    intro attrs ha
    apply produces_bind rets.yield _ BalancedItems AddDoneItems (expressionCategory_yield_balanced rets rfl)
    intro returns hr
    apply produces_pure
    apply addDoneItems_single
    apply addDone_stable_append
    · exact addDone_stable_append
        (addDone_stable_append (addDone_atom _ rfl (fun _ => rfl) (fun _ => rfl))
          (addDone_stable (addDone_parens (balanced_commaSep hp)))) ha
    · split
      · exact addStable_nil
      · exact addDone_stable (addDone_stable_append
          (addDone_atom _ rfl (fun _ => rfl) (fun _ => rfl))
          (addDone_stable (addDone_parens (balanced_commaSep hr))))
  | index e i ih0 ih1 =>
    intro hp _
    have hprece : e.prec = true := by
      apply all_prec_implies_prec e
      have hall : (Syn.index e i).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.2
    have hr : (Syn.index e i).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hlevele : 10 < e.level := Nat.lt_of_lt_of_le (by decide : 10 < 15) hr.1
    apply produces_bind e.yield _ AddFreeItems AddFreeItems (ih0 hprece hlevele)
    intro value0 h0
    apply produces_bind i.yield _ BalancedItems AddFreeItems (expressionCategory_yield_balanced i rfl)
    intro value1 h1
    apply produces_pure
    apply addFreeItems_single
    simpa only [List.append_assoc] using addFree_stable_append h0 (addDone_stable (addDone_square (balancedItems_flatten h1)))
  | slice e i j ih0 ih1 ih2 =>
    intro hp _
    have hprece : e.prec = true := by
      apply all_prec_implies_prec e
      have hall : (Syn.slice e i j).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.1.2
    have hr : (Syn.slice e i j).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hlevele : 10 < e.level := Nat.lt_of_lt_of_le (by decide : 10 < 15) hr.1
    apply produces_bind e.yield _ AddFreeItems AddFreeItems (ih0 hprece hlevele)
    intro value0 h0
    apply produces_bind i.yield _ BalancedItems AddFreeItems (expressionCategory_yield_balanced i rfl)
    intro value1 h1
    apply produces_bind j.yield _ BalancedItems AddFreeItems (expressionCategory_yield_balanced j rfl)
    intro value2 h2
    apply produces_pure
    apply addFreeItems_single
    simpa only [List.append_assoc] using addFree_stable_append h0 (addDone_stable (addDone_square (balanced_append (balanced_append (balancedItems_flatten h1) (balanced_atom rfl)) (balancedItems_flatten h2))))
  | member e name ih0 =>
    intro hp _
    have hprece : e.prec = true := by
      apply all_prec_implies_prec e
      have hall : (Syn.member e name).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.2
    have hr : (Syn.member e name).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hlevele : 10 < e.level := Nat.lt_of_lt_of_le (by decide : 10 < 15) hr.1
    apply produces_bind e.yield _ AddFreeItems AddFreeItems (ih0 hprece hlevele)
    intro value0 h0
    apply produces_pure
    apply addFreeItems_single
    have nameFree : AddFree (if name == "address" then [.elem .address] else idt name) := by
      split <;> exact addDone_free (addDone_atom _ rfl (fun _ => rfl) (fun _ => rfl))
    simpa only [List.append_assoc] using addFree_stable_append h0
      (addReset_free_append addReset_period nameFree)
  | callOptions e first rest ih0 ih1 ih2 =>
    intro hp _
    have hprece : e.prec = true := by
      apply all_prec_implies_prec e
      have hall : (Syn.callOptions e first rest).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.1.2
    have hr : (Syn.callOptions e first rest).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, decide_eq_true_eq] at hr
    have hlevele : 10 < e.level := Nat.lt_of_lt_of_le (by decide : 10 < 15) hr
    apply produces_bind e.yield _ AddFreeItems AddFreeItems (ih0 hprece hlevele)
    intro value0 h0
    apply produces_bind first.yield _ BalancedItems AddFreeItems (expressionCategory_yield_balanced first rfl)
    intro value1 h1
    apply produces_bind rest.yield _ BalancedItems AddFreeItems (expressionCategory_yield_balanced rest rfl)
    intro value2 h2
    apply produces_pure
    apply addFreeItems_single
    exact addFree_stable_append h0 (addDone_stable (addDone_braces (balanced_commaSep (balancedItems_cons (balancedItems_flatten h1) h2))))
  | call e args ih0 ih1 =>
    intro hp _
    have hprece : e.prec = true := by
      apply all_prec_implies_prec e
      have hall : (Syn.call e args).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.2
    have hr : (Syn.call e args).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, decide_eq_true_eq] at hr
    have hlevele : 10 < e.level := Nat.lt_of_lt_of_le (by decide : 10 < 15) hr
    apply produces_bind e.yield _ AddFreeItems AddFreeItems (ih0 hprece hlevele)
    intro value0 h0
    apply produces_bind args.yield _ AddDoneItems AddFreeItems ih1
    intro value1 h1
    apply produces_pure
    apply addFreeItems_single
    exact addFree_stable_append h0 (addDone_stable h1)
  | payableConv args ih0 =>
    intro _ _
    apply produces_bind args.yield _ AddDoneItems AddFreeItems ih0
    intro value0 h0
    apply produces_pure
    apply addFreeItems_single
    exact addFree_stable_append (addDone_free (addDone_atom _ rfl (fun _ => rfl) (fun _ => rfl))) (addDone_stable h0)
  | metaType ty ih0 =>
    intro _ _
    apply produces_bind ty.yield _ BalancedItems AddFreeItems (expressionCategory_yield_balanced ty rfl)
    intro value0 h0
    apply produces_pure
    apply addFreeItems_single
    exact addFree_stable_append (addDone_free (addDone_atom _ rfl (fun _ => rfl) (fun _ => rfl))) (addDone_stable (addDone_parens (balancedItems_flatten h0)))
  | unaryPrefix op e ih0 =>
    intro hp _
    have hprece : e.prec = true := by
      apply all_prec_implies_prec e
      have hall : (Syn.unaryPrefix op e).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.2
    have hr : (Syn.unaryPrefix op e).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hlevele : 10 < e.level := Nat.lt_of_lt_of_le (by decide : 10 < 13) hr.1
    apply produces_bind e.yield _ AddFreeItems AddFreeItems (ih0 hprece hlevele)
    intro value0 h0
    apply produces_pure
    apply addFreeItems_single
    exact addPrefix_free_append (addPrefix_prefix op) h0
  | unarySuffix op e ih0 =>
    intro hp _
    have hprece : e.prec = true := by
      apply all_prec_implies_prec e
      have hall : (Syn.unarySuffix op e).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.2
    have hr : (Syn.unarySuffix op e).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, decide_eq_true_eq] at hr
    have hlevele : 10 < e.level := Nat.lt_of_lt_of_le (by decide : 10 < 15) hr
    apply produces_bind e.yield _ AddFreeItems AddFreeItems (ih0 hprece hlevele)
    intro value0 h0
    apply produces_pure
    apply addFreeItems_single
    exact addFree_stable_append h0 (addStable_suffix op)
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
    have hlevela : 10 < a.level := Nat.lt_of_lt_of_le (by decide : 10 < 13) hr.1
    have hlevelb : 10 < b.level := Nat.lt_of_lt_of_le (by decide : 10 < 12) hr.2
    apply produces_bind a.yield _ AddFreeItems AddFreeItems (ih0 hpreca hlevela)
    intro value0 h0
    apply produces_bind b.yield _ AddFreeItems AddFreeItems (ih1 hprecb hlevelb)
    intro value1 h1
    apply produces_pure
    apply addFreeItems_single
    exact addFree_binary h0 addReset_exp h1
  | cond c a b ih0 ih1 ih2 =>
    intro _ hl
    exact ((by decide : ¬ 10 < 1) hl).elim
  | new ty ih0 =>
    intro _ _
    apply produces_bind ty.yield _ AddDoneItems AddFreeItems ih0
    intro value0 h0
    apply produces_pure
    apply addFreeItems_single
    exact addPrefix_free_append addPrefix_new (addDone_free h0)
  | tuple first rest ih0 ih1 =>
    intro _ _
    apply produces_bind first.yield _ BalancedItems AddFreeItems (expressionCategory_yield_balanced first rfl)
    intro value0 h0
    apply produces_bind rest.yield _ BalancedItems AddFreeItems (expressionCategory_yield_balanced rest rfl)
    intro value1 h1
    apply produces_pure
    apply addFreeItems_single
    exact addDone_free (addDone_parens (balanced_append (balancedItems_flatten h0) (balanced_flatMap value1 (fun ts => pu .comma ++ ts) (fun ts ht => balanced_append (balanced_atom rfl) (h1 ts ht)))))
  | inlineArray first rest ih0 ih1 =>
    intro _ _
    apply produces_bind first.yield _ BalancedItems AddFreeItems (expressionCategory_yield_balanced first rfl)
    intro value0 h0
    apply produces_bind rest.yield _ BalancedItems AddFreeItems (expressionCategory_yield_balanced rest rfl)
    intro value1 h1
    apply produces_pure
    apply addFreeItems_single
    exact addDone_free (addDone_square (balanced_commaSep (balancedItems_cons (balancedItems_flatten h0) h1)))
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
    have hlevela : 10 < a.level := Nat.lt_of_lt_of_le (by decide : 10 < 11) hr.1
    have hlevelb : 10 < b.level := Nat.lt_of_lt_of_le (by decide : 10 < 12) hr.2
    apply produces_bind a.yield _ AddFreeItems AddFreeItems (ih0 hpreca hlevela)
    intro value0 h0
    apply produces_bind b.yield _ AddFreeItems AddFreeItems (ih1 hprecb hlevelb)
    intro value1 h1
    apply produces_pure
    apply addFreeItems_single
    exact addFree_binary h0 (addReset_mul op) h1
  | addSub op a b ih0 ih1 =>
    intro _ hl
    exact ((by decide : ¬ 10 < 10) hl).elim
  | shift op a b ih0 ih1 =>
    intro _ hl
    exact ((by decide : ¬ 10 < 9) hl).elim
  | bitAnd a b ih0 ih1 =>
    intro _ hl
    exact ((by decide : ¬ 10 < 8) hl).elim
  | bitXor a b ih0 ih1 =>
    intro _ hl
    exact ((by decide : ¬ 10 < 7) hl).elim
  | bitOr a b ih0 ih1 =>
    intro _ hl
    exact ((by decide : ¬ 10 < 6) hl).elim
  | order op a b ih0 ih1 =>
    intro _ hl
    exact ((by decide : ¬ 10 < 5) hl).elim
  | equality op a b ih0 ih1 =>
    intro _ hl
    exact ((by decide : ¬ 10 < 4) hl).elim
  | and a b ih0 ih1 =>
    intro _ hl
    exact ((by decide : ¬ 10 < 3) hl).elim
  | or a b ih0 ih1 =>
    intro _ hl
    exact ((by decide : ¬ 10 < 2) hl).elim
  | assign op a b ih0 ih1 =>
    intro _ hl
    exact ((by decide : ¬ 10 < 0) hl).elim
  | ident name => intro _ _; exact produces_pure _ _ (addFreeItems_single (addDone_free (addDone_idt name)))
  | lit l =>
    intro _ _
    apply produces_bind (litP l) _ AddDone AddFreeItems (litP_addDone l)
    intro tokens ht
    exact produces_pure _ _ (addFreeItems_single (addDone_free ht))
  | litUnit n u =>
    intro _ _
    exact produces_pure _ _ (addFreeItems_single (addDone_free (addDone_stable_append
      (addDone_atom _ rfl (fun _ => rfl) (fun _ => rfl)) (addStable_atom _ rfl rfl rfl))))
  | elemType ty ht => intro _ _; exact produces_pure _ _ (addFreeItems_single (addDone_free (addDone_atom _ rfl (fun _ => rfl) (fun _ => rfl))))
  | _ => trivial

theorem high_expr_yield_addFree (e : Syn .expr) (hp : e.prec = true) (hl : 10 < e.level) :
    Produces e.yield AddFreeItems := expression_add_property e hp hl

theorem type_yield_addDone (ty : Syn .typeName) : Produces ty.yield AddDoneItems :=
  expression_add_property ty

theorem callArgs_yield_addDone (args : Syn .callArgs) : Produces args.yield AddDoneItems :=
  expression_add_property args

theorem high_expr_derives_addFree (e : Syn .expr) (ts : List Tok)
    (hp : e.prec = true) (hl : 10 < e.level) (hd : e.Derives ts) : AddFree ts := by
  obtain ⟨L, ht⟩ := hd
  have h : AddFreeItems [ts] := high_expr_yield_addFree e hp hl L [ts] [] ((expr_toks_iff e L ts).mp ht)
  simpa only [AddFreeItems, List.flatten_cons, List.flatten_nil, List.append_nil] using h

end Solidity.Frontend.ExpressionUniqueness
