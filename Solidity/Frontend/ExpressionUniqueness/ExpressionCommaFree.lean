import Solidity.Frontend.ExpressionUniqueness.CommaFreeAlgebra

/-!
# Intrinsic expression certificates exclude top-level commas

The existing expression/type/argument category closure supplies the separator
invariant directly. Commas inside tuple, call, type and index delimiters remain
allowed. Layout witnesses are arbitrary and no precedence premise is needed.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem expressionCategory_yield_commaFree {c : Cat} (e : Syn c) :
    ExpressionCategory c = true → Produces e.yield CommaFreeItems := by
  induction e with
  | nil => intro _; exact produces_pure _ _ commaFreeItems_nil
  | none => intro _; exact produces_pure _ _ commaFreeItems_nil
  | @cons c head tail ihHead ihTail =>
    intro hc
    apply produces_bind head.yield _ CommaFreeItems CommaFreeItems (ihHead hc)
    intro first hf
    apply produces_bind tail.yield _ CommaFreeItems CommaFreeItems (ihTail hc)
    intro rest hr
    exact produces_pure _ _ (commaFreeItems_cons (commaFreeItems_flatten hf) hr)
  | @some c value ih =>
    intro hc
    apply produces_bind value.yield _ CommaFreeItems CommaFreeItems (ih hc)
    intro items hi
    exact produces_pure _ _ (commaFreeItems_single (commaFreeItems_flatten hi))
  | positional es ih =>
    intro _
    apply produces_bind es.yield _ CommaFreeItems CommaFreeItems (ih rfl)
    intro items hi
    exact produces_pure _ _ (commaFreeItems_single (commaFree_parens (balanced_commaSep (commaFreeItems_balanced hi))))
  | named args ih =>
    intro _
    apply produces_bind args.yield _ CommaFreeItems CommaFreeItems (ih rfl)
    intro items hi
    exact produces_pure _ _ (commaFreeItems_single (commaFree_parens (balanced_braces (balanced_commaSep (commaFreeItems_balanced hi)))))
  | namedArg name e ih =>
    intro _
    apply produces_bind e.yield _ CommaFreeItems CommaFreeItems (ih rfl)
    intro items hi
    apply produces_pure
    exact commaFreeItems_single (commaFree_append (commaFree_append (commaFree_idt name)
      (commaFree_atom rfl rfl)) (commaFreeItems_flatten hi))
  | param ty loc name ih =>
    intro _
    apply produces_bind ty.yield _ CommaFreeItems CommaFreeItems (ih rfl)
    intro items hi
    apply produces_pure
    exact commaFreeItems_single (commaFree_append (commaFree_append (commaFreeItems_flatten hi)
      (commaFree_optToks DataLoc.toks commaFree_dataLoc loc)) (commaFree_optToks idt commaFree_idt name))
  | elem ty => intro _; exact produces_pure _ _ (commaFreeItems_single (commaFree_elem ty))
  | userType path => intro _; exact produces_pure _ _ (commaFreeItems_single (commaFree_path path))
  | array ty len ihTy ihLen =>
    intro _
    apply produces_bind ty.yield _ CommaFreeItems CommaFreeItems (ihTy rfl)
    intro types ht
    apply produces_bind len.yield _ CommaFreeItems CommaFreeItems (ihLen rfl)
    intro lengths hl
    apply produces_pure
    apply commaFreeItems_single
    simpa only [List.append_assoc] using commaFree_append (commaFreeItems_flatten ht)
      (commaFree_square (balancedItems_flatten (commaFreeItems_balanced hl)))
  | mapping key keyName value valueName ih =>
    intro _
    apply produces_bind value.yield _ CommaFreeItems CommaFreeItems (ih rfl)
    intro items hi
    apply produces_pure
    apply commaFreeItems_single
    exact commaFree_append (commaFree_tk .mapping) (commaFree_parens
      (balanced_append (balanced_append (balanced_append (balanced_append
        (balanced_mapping_key key) (balanced_optToks idt balanced_idt keyName))
        (balanced_atom rfl)) (balancedItems_flatten (commaFreeItems_balanced hi)))
        (balanced_optToks idt balanced_idt valueName)))
  | fnType ps vis mu rets ihPs ihRets =>
    intro _
    apply produces_bind_all popAttrs _ CommaFreeItems
    intro order
    apply produces_bind ps.yield _ CommaFreeItems CommaFreeItems (ihPs rfl)
    intro params hp
    have hs : CommaFreeAttrs (single .vis (optToks Visibility.toks vis) ++
        single .mutab (optToks Mutability.toks mu)) :=
      commaFreeAttrs_append (commaFree_single _ _ (commaFree_optToks Visibility.toks commaFree_visibility vis))
        (commaFree_single _ _ (commaFree_optToks Mutability.toks commaFree_mutability mu))
    apply produces_bind (attrsP _ [] order) _ CommaFree CommaFreeItems
      (attrsP_commaFree _ [] order hs commaFreeItems_nil)
    intro attrs ha
    apply produces_bind rets.yield _ CommaFreeItems CommaFreeItems (ihRets rfl)
    intro returns hr
    apply produces_pure
    apply commaFreeItems_single
    apply commaFree_append (commaFree_append (commaFree_append (commaFree_tk .function)
      (commaFree_parens (balanced_commaSep (commaFreeItems_balanced hp)))) ha)
    split
    · exact commaFree_nil
    · exact commaFree_append (commaFree_tk .returns) (commaFree_parens (balanced_commaSep (commaFreeItems_balanced hr)))
  | index e i ih0 ih1 =>
    intro _
    apply produces_bind e.yield _ CommaFreeItems CommaFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind i.yield _ CommaFreeItems CommaFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply commaFreeItems_single
    simpa only [List.append_assoc] using commaFree_append (commaFreeItems_flatten h0) (commaFree_square (balancedItems_flatten (commaFreeItems_balanced h1)))
  | slice e i j ih0 ih1 ih2 =>
    intro _
    apply produces_bind e.yield _ CommaFreeItems CommaFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind i.yield _ CommaFreeItems CommaFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_bind j.yield _ CommaFreeItems CommaFreeItems (ih2 rfl)
    intro value2 h2
    apply produces_pure
    apply commaFreeItems_single
    simpa only [List.append_assoc] using commaFree_append (commaFreeItems_flatten h0) (commaFree_square (balanced_append (balanced_append (balancedItems_flatten (commaFreeItems_balanced h1)) (balanced_atom rfl)) (balancedItems_flatten (commaFreeItems_balanced h2))))
  | member e name ih0 =>
    intro _
    apply produces_bind e.yield _ CommaFreeItems CommaFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_pure
    apply commaFreeItems_single
    apply commaFree_append (commaFree_append (commaFreeItems_flatten h0) (commaFree_atom rfl rfl))
    split <;> exact commaFree_atom rfl rfl
  | callOptions e first rest ih0 ih1 ih2 =>
    intro _
    apply produces_bind e.yield _ CommaFreeItems CommaFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind first.yield _ CommaFreeItems CommaFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_bind rest.yield _ CommaFreeItems CommaFreeItems (ih2 rfl)
    intro value2 h2
    apply produces_pure
    apply commaFreeItems_single
    exact commaFree_append (commaFreeItems_flatten h0) (commaFree_braces (balanced_commaSep (balancedItems_cons (balancedItems_flatten (commaFreeItems_balanced h1)) (commaFreeItems_balanced h2))))
  | call e args ih0 ih1 =>
    intro _
    apply produces_bind e.yield _ CommaFreeItems CommaFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind args.yield _ CommaFreeItems CommaFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply commaFreeItems_single
    exact commaFree_append (commaFreeItems_flatten h0) (commaFreeItems_flatten h1)
  | payableConv args ih0 =>
    intro _
    apply produces_bind args.yield _ CommaFreeItems CommaFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_pure
    apply commaFreeItems_single
    exact commaFree_append (commaFree_tk .payable) (commaFreeItems_flatten h0)
  | metaType ty ih0 =>
    intro _
    apply produces_bind ty.yield _ CommaFreeItems CommaFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_pure
    apply commaFreeItems_single
    exact commaFree_append (commaFree_tk .type_) (commaFree_parens (balancedItems_flatten (commaFreeItems_balanced h0)))
  | unaryPrefix op e ih0 =>
    intro _
    apply produces_bind e.yield _ CommaFreeItems CommaFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_pure
    apply commaFreeItems_single
    exact commaFree_append (commaFree_prefix op) (commaFreeItems_flatten h0)
  | unarySuffix op e ih0 =>
    intro _
    apply produces_bind e.yield _ CommaFreeItems CommaFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_pure
    apply commaFreeItems_single
    exact commaFree_append (commaFreeItems_flatten h0) (commaFree_suffix op)
  | exp a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ CommaFreeItems CommaFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ CommaFreeItems CommaFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply commaFreeItems_single
    exact commaFree_append (commaFree_append (commaFreeItems_flatten h0) (commaFree_atom rfl rfl)) (commaFreeItems_flatten h1)
  | cond c a b ih0 ih1 ih2 =>
    intro _
    apply produces_bind c.yield _ CommaFreeItems CommaFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind a.yield _ CommaFreeItems CommaFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_bind b.yield _ CommaFreeItems CommaFreeItems (ih2 rfl)
    intro value2 h2
    apply produces_pure
    apply commaFreeItems_single
    exact commaFree_append (commaFree_append (commaFree_append (commaFree_append (commaFreeItems_flatten h0) (commaFree_atom rfl rfl)) (commaFreeItems_flatten h1)) (commaFree_atom rfl rfl)) (commaFreeItems_flatten h2)
  | new ty ih0 =>
    intro _
    apply produces_bind ty.yield _ CommaFreeItems CommaFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_pure
    apply commaFreeItems_single
    exact commaFree_append (commaFree_tk .new) (commaFreeItems_flatten h0)
  | tuple first rest ih0 ih1 =>
    intro _
    apply produces_bind first.yield _ CommaFreeItems CommaFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind rest.yield _ CommaFreeItems CommaFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply commaFreeItems_single
    exact commaFree_parens (balanced_append (balancedItems_flatten (commaFreeItems_balanced h0)) (balanced_flatMap value1 (fun ts => pu .comma ++ ts) (fun ts ht => balanced_append (balanced_atom rfl) (commaFree_balanced (h1 ts ht)))))
  | inlineArray first rest ih0 ih1 =>
    intro _
    apply produces_bind first.yield _ CommaFreeItems CommaFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind rest.yield _ CommaFreeItems CommaFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply commaFreeItems_single
    exact commaFree_square (balanced_commaSep (balancedItems_cons (balancedItems_flatten (commaFreeItems_balanced h0)) (commaFreeItems_balanced h1)))
  | mulDivMod op a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ CommaFreeItems CommaFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ CommaFreeItems CommaFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply commaFreeItems_single
    exact commaFree_append (commaFree_append (commaFreeItems_flatten h0) (commaFree_mul op)) (commaFreeItems_flatten h1)
  | addSub op a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ CommaFreeItems CommaFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ CommaFreeItems CommaFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply commaFreeItems_single
    exact commaFree_append (commaFree_append (commaFreeItems_flatten h0) (commaFree_add op)) (commaFreeItems_flatten h1)
  | shift op a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ CommaFreeItems CommaFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ CommaFreeItems CommaFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply commaFreeItems_single
    exact commaFree_append (commaFree_append (commaFreeItems_flatten h0) (commaFree_shift op)) (commaFreeItems_flatten h1)
  | bitAnd a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ CommaFreeItems CommaFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ CommaFreeItems CommaFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply commaFreeItems_single
    exact commaFree_append (commaFree_append (commaFreeItems_flatten h0) (commaFree_atom rfl rfl)) (commaFreeItems_flatten h1)
  | bitXor a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ CommaFreeItems CommaFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ CommaFreeItems CommaFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply commaFreeItems_single
    exact commaFree_append (commaFree_append (commaFreeItems_flatten h0) (commaFree_atom rfl rfl)) (commaFreeItems_flatten h1)
  | bitOr a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ CommaFreeItems CommaFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ CommaFreeItems CommaFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply commaFreeItems_single
    exact commaFree_append (commaFree_append (commaFreeItems_flatten h0) (commaFree_atom rfl rfl)) (commaFreeItems_flatten h1)
  | order op a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ CommaFreeItems CommaFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ CommaFreeItems CommaFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply commaFreeItems_single
    exact commaFree_append (commaFree_append (commaFreeItems_flatten h0) (commaFree_order op)) (commaFreeItems_flatten h1)
  | equality op a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ CommaFreeItems CommaFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ CommaFreeItems CommaFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply commaFreeItems_single
    exact commaFree_append (commaFree_append (commaFreeItems_flatten h0) (commaFree_equality op)) (commaFreeItems_flatten h1)
  | and a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ CommaFreeItems CommaFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ CommaFreeItems CommaFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply commaFreeItems_single
    exact commaFree_append (commaFree_append (commaFreeItems_flatten h0) (commaFree_atom rfl rfl)) (commaFreeItems_flatten h1)
  | or a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ CommaFreeItems CommaFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ CommaFreeItems CommaFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply commaFreeItems_single
    exact commaFree_append (commaFree_append (commaFreeItems_flatten h0) (commaFree_atom rfl rfl)) (commaFreeItems_flatten h1)
  | assign op a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ CommaFreeItems CommaFreeItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ CommaFreeItems CommaFreeItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply commaFreeItems_single
    exact commaFree_append (commaFree_append (commaFreeItems_flatten h0) (commaFree_assign op)) (commaFreeItems_flatten h1)
  | ident name => intro _; exact produces_pure _ _ (commaFreeItems_single (commaFree_idt name))
  | lit l =>
    intro _
    apply produces_bind (litP l) _ CommaFree CommaFreeItems (litP_commaFree l)
    intro tokens ht
    exact produces_pure _ _ (commaFreeItems_single ht)
  | litUnit n u =>
    intro _
    exact produces_pure _ _ (commaFreeItems_single (commaFree_append (commaFree_atom rfl rfl) (commaFree_atom rfl rfl)))
  | elemType ty ht => intro _; exact produces_pure _ _ (commaFreeItems_single (commaFree_atom rfl rfl))
  | _ => intro impossible; cases impossible

theorem expr_yield_commaFree (e : Syn .expr) : Produces e.yield CommaFreeItems :=
  expressionCategory_yield_commaFree e rfl

theorem expr_derives_commaFree (e : Syn .expr) (ts : List Tok) (h : e.Derives ts) :
    CommaFree ts := by
  obtain ⟨L, ht⟩ := h
  have hy := (expr_toks_iff e L ts).mp ht
  exact expr_yield_commaFree e L [ts] [] hy ts (List.mem_cons.mpr (Or.inl rfl))

/-- Separator reconstruction for two nonempty vectors of certified expression
spans; no skip/balance/root-split hypothesis is supplied by the caller. -/
theorem certified_expr_spans_commaSep_unique
    (a b : Syn .expr) (aspan bspan : List Tok)
    (args args' : List (Syn .expr × List Tok))
    (ha : a.Derives aspan) (hb : b.Derives bspan)
    (has : ∀ pair, pair ∈ args → pair.1.Derives pair.2)
    (hbs : ∀ pair, pair ∈ args' → pair.1.Derives pair.2)
    (he : commaSep (aspan :: args.map Prod.snd) = commaSep (bspan :: args'.map Prod.snd)) :
    aspan :: args.map Prod.snd = bspan :: args'.map Prod.snd := by
  apply commaSep_nonempty_unique aspan bspan _ _ _ _ he
  · intro ts ht
    rcases List.mem_cons.mp ht with heq | hrest
    · exact heq ▸ expr_derives_commaFree a aspan ha
    · obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hrest
      exact expr_derives_commaFree pair.1 pair.2 (has pair hpair)
  · intro ts ht
    rcases List.mem_cons.mp ht with heq | hrest
    · exact heq ▸ expr_derives_commaFree b bspan hb
    · obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hrest
      exact expr_derives_commaFree pair.1 pair.2 (hbs pair hpair)

end Solidity.Frontend.ExpressionUniqueness
