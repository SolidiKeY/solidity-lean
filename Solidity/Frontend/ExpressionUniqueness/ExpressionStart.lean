import Solidity.Frontend.ExpressionUniqueness.StartAlgebra
import Solidity.Frontend.ExpressionUniqueness.PostfixYieldSplit

/-!
# Actual expression-category yields never begin with an opening brace

All 29 expression constructors and type/parameter/argument closure are covered.
Call options have a nonempty existing base before their braces. This first-token
invariant allows arbitrary later braces and uses no precedence premise.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem expressionCategory_yield_startFree {c : Cat} (e : Syn c) :
    ExpressionCategory c = true → Produces e.yield StartFreeItems := by
  induction e with
  | nil => intro _; exact produces_pure _ _ startFreeItems_nil
  | none => intro _; exact produces_pure _ _ startFreeItems_nil
  | @cons c head tail ihHead ihTail =>
    intro hc
    apply produces_bind head.yield _ StartFreeItems StartFreeItems (ihHead hc)
    intro first hf
    apply produces_bind tail.yield _ StartFreeItems StartFreeItems (ihTail hc)
    intro rest hr
    exact produces_pure _ _ (startFreeItems_cons (startFreeItems_flatten hf) hr)
  | @some c value ih =>
    intro hc
    apply produces_bind value.yield _ StartFreeItems StartFreeItems (ih hc)
    intro items hi
    exact produces_pure _ _ (startFreeItems_single (startFreeItems_flatten hi))
  | positional es ih =>
    intro _
    apply produces_bind es.yield _ StartFreeItems StartFreeItems (ih rfl)
    intro items hi
    exact produces_pure _ _ (startFreeItems_single (startFree_parens (balanced_commaSep (startFreeItems_balanced hi))))
  | named args ih =>
    intro _
    apply produces_bind args.yield _ StartFreeItems StartFreeItems (ih rfl)
    intro items hi
    exact produces_pure _ _ (startFreeItems_single (startFree_parens (balanced_braces (balanced_commaSep (startFreeItems_balanced hi)))))
  | namedArg name e ih =>
    intro _
    apply produces_bind e.yield _ StartFreeItems StartFreeItems (ih rfl)
    intro items hi
    apply produces_pure
    exact startFreeItems_single (startFree_append (startFree_append (startFree_idt name)
      (startFree_atom rfl rfl)) (startFreeItems_flatten hi))
  | param ty loc name ih =>
    intro _
    apply produces_bind ty.yield _ StartFreeItems StartFreeItems (ih rfl)
    intro items hi
    apply produces_pure
    exact startFreeItems_single (startFree_append (startFree_append (startFreeItems_flatten hi)
      (startFree_optToks DataLoc.toks startFree_dataLoc loc)) (startFree_optToks idt startFree_idt name))
  | elem ty => intro _; exact produces_pure _ _ (startFreeItems_single (startFree_elem ty))
  | userType path => intro _; exact produces_pure _ _ (startFreeItems_single (startFree_path path))
  | array ty len ihTy ihLen =>
    intro _
    apply produces_bind ty.yield _ StartFreeItems StartFreeItems (ihTy rfl)
    intro types ht
    apply produces_bind len.yield _ StartFreeItems StartFreeItems (ihLen rfl)
    intro lengths hl
    apply produces_pure
    apply startFreeItems_single
    simpa only [List.append_assoc] using startFree_append (startFreeItems_flatten ht)
      (startFree_square (balancedItems_flatten (startFreeItems_balanced hl)))
  | mapping key keyName value valueName ih =>
    intro _
    apply produces_bind value.yield _ StartFreeItems StartFreeItems (ih rfl)
    intro items hi
    apply produces_pure
    apply startFreeItems_single
    exact startFree_append (startFree_tk .mapping) (startFree_parens
      (balanced_append (balanced_append (balanced_append (balanced_append
        (balanced_mapping_key key) (balanced_optToks idt balanced_idt keyName))
        (balanced_atom rfl)) (balancedItems_flatten (startFreeItems_balanced hi)))
        (balanced_optToks idt balanced_idt valueName)))
  | fnType ps vis mu rets ihPs ihRets =>
    intro _
    apply produces_bind_all popAttrs _ StartFreeItems
    intro order
    apply produces_bind ps.yield _ StartFreeItems StartFreeItems (ihPs rfl)
    intro params hp
    have hs : StartFreeAttrs (single .vis (optToks Visibility.toks vis) ++
        single .mutab (optToks Mutability.toks mu)) :=
      startFreeAttrs_append (startFree_single _ _ (startFree_optToks Visibility.toks startFree_visibility vis))
        (startFree_single _ _ (startFree_optToks Mutability.toks startFree_mutability mu))
    apply produces_bind (attrsP _ [] order) _ StartFree StartFreeItems
      (attrsP_startFree _ [] order hs startFreeItems_nil)
    intro attrs ha
    apply produces_bind rets.yield _ StartFreeItems StartFreeItems (ihRets rfl)
    intro returns hr
    apply produces_pure
    apply startFreeItems_single
    apply startFree_append (startFree_append (startFree_append (startFree_tk .function)
      (startFree_parens (balanced_commaSep (startFreeItems_balanced hp)))) ha)
    split
    · exact startFree_nil
    · exact startFree_append (startFree_tk .returns) (startFree_parens (balanced_commaSep (startFreeItems_balanced hr)))
  | index e i ih0 ih1 =>
    intro _
    apply produces_bind e.yield _ StartFreeItems StartFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind i.yield _ StartFreeItems StartFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply startFreeItems_single
    simpa only [List.append_assoc] using startFree_append (startFreeItems_flatten h0) (startFree_square (balancedItems_flatten (startFreeItems_balanced h1)))
  | slice e i j ih0 ih1 ih2 =>
    intro _
    apply produces_bind e.yield _ StartFreeItems StartFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind i.yield _ StartFreeItems StartFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_bind j.yield _ StartFreeItems StartFreeItems (ih2 rfl)
    intro value2 h2
    apply produces_pure
    apply startFreeItems_single
    simpa only [List.append_assoc] using startFree_append (startFreeItems_flatten h0) (startFree_square (balanced_append (balanced_append (balancedItems_flatten (startFreeItems_balanced h1)) (balanced_atom rfl)) (balancedItems_flatten (startFreeItems_balanced h2))))
  | member e name ih0 =>
    intro _
    apply produces_bind e.yield _ StartFreeItems StartFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_pure
    apply startFreeItems_single
    apply startFree_append (startFree_append (startFreeItems_flatten h0) (startFree_atom rfl rfl))
    split <;> exact startFree_atom rfl rfl
  | callOptions e first rest ih0 ih1 ih2 =>
    intro _ initial items final hy
    obtain ⟨xs, ys, zs, middle, next, hx, hf, hr, shape⟩ := options_yield_parts e first rest initial final items hy
    have baseStart : StartFree xs.flatten := startFreeItems_flatten (ih0 rfl initial xs middle hx)
    have nonempty : xs.flatten ≠ [] := nonemptyItem_flatten (expr_yield_nonempty e initial xs middle hx)
    have firstBal : Balanced ys.flatten := balancedItems_flatten
      (expressionCategory_yield_balanced first rfl middle ys next hf)
    have restBal : BalancedItems zs := expressionCategory_yield_balanced rest rfl next zs final hr
    rw [shape]
    exact startFreeItems_single (startFree_append_any baseStart nonempty
      (balanced_braces (balanced_commaSep (balancedItems_cons firstBal restBal))))
  | call e args ih0 ih1 =>
    intro _
    apply produces_bind e.yield _ StartFreeItems StartFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind args.yield _ StartFreeItems StartFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply startFreeItems_single
    exact startFree_append (startFreeItems_flatten h0) (startFreeItems_flatten h1)
  | payableConv args ih0 =>
    intro _
    apply produces_bind args.yield _ StartFreeItems StartFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_pure
    apply startFreeItems_single
    exact startFree_append (startFree_tk .payable) (startFreeItems_flatten h0)
  | metaType ty ih0 =>
    intro _
    apply produces_bind ty.yield _ StartFreeItems StartFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_pure
    apply startFreeItems_single
    exact startFree_append (startFree_tk .type_) (startFree_parens (balancedItems_flatten (startFreeItems_balanced h0)))
  | unaryPrefix op e ih0 =>
    intro _
    apply produces_bind e.yield _ StartFreeItems StartFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_pure
    apply startFreeItems_single
    exact startFree_append (startFree_prefix op) (startFreeItems_flatten h0)
  | unarySuffix op e ih0 =>
    intro _
    apply produces_bind e.yield _ StartFreeItems StartFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_pure
    apply startFreeItems_single
    exact startFree_append (startFreeItems_flatten h0) (startFree_suffix op)
  | exp a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ StartFreeItems StartFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ StartFreeItems StartFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply startFreeItems_single
    exact startFree_append (startFree_append (startFreeItems_flatten h0) (startFree_atom rfl rfl)) (startFreeItems_flatten h1)
  | cond c a b ih0 ih1 ih2 =>
    intro _
    apply produces_bind c.yield _ StartFreeItems StartFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind a.yield _ StartFreeItems StartFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_bind b.yield _ StartFreeItems StartFreeItems (ih2 rfl)
    intro value2 h2
    apply produces_pure
    apply startFreeItems_single
    exact startFree_append (startFree_append (startFree_append (startFree_append (startFreeItems_flatten h0) (startFree_atom rfl rfl)) (startFreeItems_flatten h1)) (startFree_atom rfl rfl)) (startFreeItems_flatten h2)
  | new ty ih0 =>
    intro _
    apply produces_bind ty.yield _ StartFreeItems StartFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_pure
    apply startFreeItems_single
    exact startFree_append (startFree_tk .new) (startFreeItems_flatten h0)
  | tuple first rest ih0 ih1 =>
    intro _
    apply produces_bind first.yield _ StartFreeItems StartFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind rest.yield _ StartFreeItems StartFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply startFreeItems_single
    exact startFree_parens (balanced_append (balancedItems_flatten (startFreeItems_balanced h0)) (balanced_flatMap value1 (fun ts => pu .comma ++ ts) (fun ts ht => balanced_append (balanced_atom rfl) (startFree_balanced (h1 ts ht)))))
  | inlineArray first rest ih0 ih1 =>
    intro _
    apply produces_bind first.yield _ StartFreeItems StartFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind rest.yield _ StartFreeItems StartFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply startFreeItems_single
    exact startFree_square (balanced_commaSep (balancedItems_cons (balancedItems_flatten (startFreeItems_balanced h0)) (startFreeItems_balanced h1)))
  | mulDivMod op a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ StartFreeItems StartFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ StartFreeItems StartFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply startFreeItems_single
    exact startFree_append (startFree_append (startFreeItems_flatten h0) (startFree_mul op)) (startFreeItems_flatten h1)
  | addSub op a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ StartFreeItems StartFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ StartFreeItems StartFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply startFreeItems_single
    exact startFree_append (startFree_append (startFreeItems_flatten h0) (startFree_add op)) (startFreeItems_flatten h1)
  | shift op a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ StartFreeItems StartFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ StartFreeItems StartFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply startFreeItems_single
    exact startFree_append (startFree_append (startFreeItems_flatten h0) (startFree_shift op)) (startFreeItems_flatten h1)
  | bitAnd a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ StartFreeItems StartFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ StartFreeItems StartFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply startFreeItems_single
    exact startFree_append (startFree_append (startFreeItems_flatten h0) (startFree_atom rfl rfl)) (startFreeItems_flatten h1)
  | bitXor a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ StartFreeItems StartFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ StartFreeItems StartFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply startFreeItems_single
    exact startFree_append (startFree_append (startFreeItems_flatten h0) (startFree_atom rfl rfl)) (startFreeItems_flatten h1)
  | bitOr a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ StartFreeItems StartFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ StartFreeItems StartFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply startFreeItems_single
    exact startFree_append (startFree_append (startFreeItems_flatten h0) (startFree_atom rfl rfl)) (startFreeItems_flatten h1)
  | order op a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ StartFreeItems StartFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ StartFreeItems StartFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply startFreeItems_single
    exact startFree_append (startFree_append (startFreeItems_flatten h0) (startFree_order op)) (startFreeItems_flatten h1)
  | equality op a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ StartFreeItems StartFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ StartFreeItems StartFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply startFreeItems_single
    exact startFree_append (startFree_append (startFreeItems_flatten h0) (startFree_equality op)) (startFreeItems_flatten h1)
  | and a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ StartFreeItems StartFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ StartFreeItems StartFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply startFreeItems_single
    exact startFree_append (startFree_append (startFreeItems_flatten h0) (startFree_atom rfl rfl)) (startFreeItems_flatten h1)
  | or a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ StartFreeItems StartFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ StartFreeItems StartFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply startFreeItems_single
    exact startFree_append (startFree_append (startFreeItems_flatten h0) (startFree_atom rfl rfl)) (startFreeItems_flatten h1)
  | assign op a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ StartFreeItems StartFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ StartFreeItems StartFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply startFreeItems_single
    exact startFree_append (startFree_append (startFreeItems_flatten h0) (startFree_assign op)) (startFreeItems_flatten h1)
  | ident name => intro _; exact produces_pure _ _ (startFreeItems_single (startFree_idt name))
  | lit l =>
    intro _
    apply produces_bind (litP l) _ StartFree StartFreeItems (litP_startFree l)
    intro tokens ht
    exact produces_pure _ _ (startFreeItems_single ht)
  | litUnit n u =>
    intro _
    exact produces_pure _ _ (startFreeItems_single (startFree_append (startFree_atom rfl rfl) (startFree_atom rfl rfl)))
  | elemType ty ht => intro _; exact produces_pure _ _ (startFreeItems_single (startFree_atom rfl rfl))
  | _ => intro impossible; cases impossible

theorem expr_yield_noInitialCurly (e : Syn .expr) (initial final : List Choice)
    (items : List (List Tok)) (hy : e.yield initial = some (items, final)) : NoInitialCurly items.flatten :=
  (startFreeItems_flatten (expressionCategory_yield_startFree e rfl initial items final hy)).2

end Solidity.Frontend.ExpressionUniqueness
