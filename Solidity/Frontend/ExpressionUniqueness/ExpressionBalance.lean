import Solidity.Frontend.ExpressionUniqueness.AttributeBalance

/-!
# Intrinsic expression yields are delimiter-balanced

The proof follows the existing indexed syntax through expressions, types,
parameters and argument syntax, including their lists and options. It imposes no
new certificate premise and does not prove uniqueness outside expression syntax.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

/-- The category closure reachable inside an intrinsic expression. -/
def ExpressionCategory : Cat → Bool
  | .expr | .typeName | .param | .callArgs | .namedArg => true
  | .list c | .opt c => ExpressionCategory c
  | _ => false

theorem balanced_mapping_key (key : MapKey) :
    Balanced (match key with | .elem e _ => e.toks | .path p => p.toks) := by
  cases key with
  | elem e _ => exact balanced_elem e
  | path p => exact balanced_path p

/-- Every successful yield in the expression category closure has individually
balanced items. Arbitrary layouts and their remaining suffixes are included. -/
theorem expressionCategory_yield_balanced {c : Cat} (e : Syn c) :
    ExpressionCategory c = true → Produces e.yield BalancedItems := by
  induction e with
  | nil => intro _; exact produces_pure _ _ balancedItems_nil
  | none => intro _; exact produces_pure _ _ balancedItems_nil
  | @cons c head tail ihHead ihTail =>
    intro hc
    apply produces_bind head.yield _ BalancedItems BalancedItems (ihHead hc)
    intro first hf
    apply produces_bind tail.yield _ BalancedItems BalancedItems (ihTail hc)
    intro rest hr
    exact produces_pure _ _ (balancedItems_cons (balancedItems_flatten hf) hr)
  | @some c value ih =>
    intro hc
    apply produces_bind value.yield _ BalancedItems BalancedItems (ih hc)
    intro items hi
    exact produces_pure _ _ (balancedItems_single (balancedItems_flatten hi))
  | positional es ih =>
    intro _
    apply produces_bind es.yield _ BalancedItems BalancedItems (ih rfl)
    intro items hi
    exact produces_pure _ _ (balancedItems_single (balanced_parens (balanced_commaSep hi)))
  | named args ih =>
    intro _
    apply produces_bind args.yield _ BalancedItems BalancedItems (ih rfl)
    intro items hi
    exact produces_pure _ _ (balancedItems_single (balanced_parens (balanced_braces (balanced_commaSep hi))))
  | namedArg name e ih =>
    intro _
    apply produces_bind e.yield _ BalancedItems BalancedItems (ih rfl)
    intro items hi
    apply produces_pure
    exact balancedItems_single (balanced_append (balanced_append (balanced_idt name)
      (balanced_atom rfl)) (balancedItems_flatten hi))
  | param ty loc name ih =>
    intro _
    apply produces_bind ty.yield _ BalancedItems BalancedItems (ih rfl)
    intro items hi
    apply produces_pure
    exact balancedItems_single (balanced_append (balanced_append (balancedItems_flatten hi)
      (balanced_optToks DataLoc.toks balanced_dataLoc loc)) (balanced_optToks idt balanced_idt name))
  | elem ty => intro _; exact produces_pure _ _ (balancedItems_single (balanced_elem ty))
  | userType path => intro _; exact produces_pure _ _ (balancedItems_single (balanced_path path))
  | array ty len ihTy ihLen =>
    intro _
    apply produces_bind ty.yield _ BalancedItems BalancedItems (ihTy rfl)
    intro types ht
    apply produces_bind len.yield _ BalancedItems BalancedItems (ihLen rfl)
    intro lengths hl
    apply produces_pure
    apply balancedItems_single
    simpa only [List.append_assoc] using balanced_append (balancedItems_flatten ht)
      (balanced_square (balancedItems_flatten hl))
  | mapping key keyName value valueName ih =>
    intro _
    apply produces_bind value.yield _ BalancedItems BalancedItems (ih rfl)
    intro items hi
    apply produces_pure
    apply balancedItems_single
    exact balanced_append (balanced_tk .mapping) (balanced_parens
      (balanced_append (balanced_append (balanced_append (balanced_append
        (balanced_mapping_key key) (balanced_optToks idt balanced_idt keyName))
        (balanced_atom rfl)) (balancedItems_flatten hi)) (balanced_optToks idt balanced_idt valueName)))
  | fnType ps vis mu rets ihPs ihRets =>
    intro _
    apply produces_bind_all popAttrs _ BalancedItems
    intro order
    apply produces_bind ps.yield _ BalancedItems BalancedItems (ihPs rfl)
    intro params hp
    have hs : BalancedAttrs (single .vis (optToks Visibility.toks vis) ++
        single .mutab (optToks Mutability.toks mu)) :=
      balancedAttrs_append (balanced_single _ _ (balanced_optToks Visibility.toks balanced_visibility vis))
        (balanced_single _ _ (balanced_optToks Mutability.toks balanced_mutability mu))
    apply produces_bind (attrsP _ [] order) _ Balanced BalancedItems
      (attrsP_balanced _ [] order hs balancedItems_nil)
    intro attrs ha
    apply produces_bind rets.yield _ BalancedItems BalancedItems (ihRets rfl)
    intro returns hr
    apply produces_pure
    apply balancedItems_single
    apply balanced_append (balanced_append (balanced_append (balanced_tk .function)
      (balanced_parens (balanced_commaSep hp))) ha)
    split
    · exact balanced_nil
    · exact balanced_append (balanced_tk .returns) (balanced_parens (balanced_commaSep hr))
  | index e i ih0 ih1 =>
    intro _
    apply produces_bind e.yield _ BalancedItems BalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind i.yield _ BalancedItems BalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply balancedItems_single
    simpa only [List.append_assoc] using balanced_append (balancedItems_flatten h0) (balanced_square (balancedItems_flatten h1))
  | slice e i j ih0 ih1 ih2 =>
    intro _
    apply produces_bind e.yield _ BalancedItems BalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind i.yield _ BalancedItems BalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_bind j.yield _ BalancedItems BalancedItems (ih2 rfl)
    intro value2 h2
    apply produces_pure
    apply balancedItems_single
    simpa only [List.append_assoc] using balanced_append (balancedItems_flatten h0) (balanced_square (balanced_append (balanced_append (balancedItems_flatten h1) (balanced_atom rfl)) (balancedItems_flatten h2)))
  | member e name ih0 =>
    intro _
    apply produces_bind e.yield _ BalancedItems BalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_pure
    apply balancedItems_single
    apply balanced_append (balanced_append (balancedItems_flatten h0) (balanced_atom rfl))
    split <;> exact balanced_atom rfl
  | callOptions e first rest ih0 ih1 ih2 =>
    intro _
    apply produces_bind e.yield _ BalancedItems BalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind first.yield _ BalancedItems BalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_bind rest.yield _ BalancedItems BalancedItems (ih2 rfl)
    intro value2 h2
    apply produces_pure
    apply balancedItems_single
    exact balanced_append (balancedItems_flatten h0) (balanced_braces (balanced_commaSep (balancedItems_cons (balancedItems_flatten h1) h2)))
  | call e args ih0 ih1 =>
    intro _
    apply produces_bind e.yield _ BalancedItems BalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind args.yield _ BalancedItems BalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply balancedItems_single
    exact balanced_append (balancedItems_flatten h0) (balancedItems_flatten h1)
  | payableConv args ih0 =>
    intro _
    apply produces_bind args.yield _ BalancedItems BalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_pure
    apply balancedItems_single
    exact balanced_append (balanced_tk .payable) (balancedItems_flatten h0)
  | metaType ty ih0 =>
    intro _
    apply produces_bind ty.yield _ BalancedItems BalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_pure
    apply balancedItems_single
    exact balanced_append (balanced_tk .type_) (balanced_parens (balancedItems_flatten h0))
  | unaryPrefix op e ih0 =>
    intro _
    apply produces_bind e.yield _ BalancedItems BalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_pure
    apply balancedItems_single
    exact balanced_append (balanced_prefix op) (balancedItems_flatten h0)
  | unarySuffix op e ih0 =>
    intro _
    apply produces_bind e.yield _ BalancedItems BalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_pure
    apply balancedItems_single
    exact balanced_append (balancedItems_flatten h0) (balanced_suffix op)
  | exp a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ BalancedItems BalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ BalancedItems BalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply balancedItems_single
    exact balanced_append (balanced_append (balancedItems_flatten h0) (balanced_atom rfl)) (balancedItems_flatten h1)
  | cond c a b ih0 ih1 ih2 =>
    intro _
    apply produces_bind c.yield _ BalancedItems BalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind a.yield _ BalancedItems BalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_bind b.yield _ BalancedItems BalancedItems (ih2 rfl)
    intro value2 h2
    apply produces_pure
    apply balancedItems_single
    exact balanced_append (balanced_append (balanced_append (balanced_append (balancedItems_flatten h0) (balanced_atom rfl)) (balancedItems_flatten h1)) (balanced_atom rfl)) (balancedItems_flatten h2)
  | new ty ih0 =>
    intro _
    apply produces_bind ty.yield _ BalancedItems BalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_pure
    apply balancedItems_single
    exact balanced_append (balanced_tk .new) (balancedItems_flatten h0)
  | tuple first rest ih0 ih1 =>
    intro _
    apply produces_bind first.yield _ BalancedItems BalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind rest.yield _ BalancedItems BalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply balancedItems_single
    exact balanced_parens (balanced_append (balancedItems_flatten h0) (balanced_flatMap value1 (fun ts => pu .comma ++ ts) (fun ts ht => balanced_append (balanced_atom rfl) (h1 ts ht))))
  | inlineArray first rest ih0 ih1 =>
    intro _
    apply produces_bind first.yield _ BalancedItems BalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind rest.yield _ BalancedItems BalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply balancedItems_single
    exact balanced_square (balanced_commaSep (balancedItems_cons (balancedItems_flatten h0) h1))
  | mulDivMod op a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ BalancedItems BalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ BalancedItems BalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply balancedItems_single
    exact balanced_append (balanced_append (balancedItems_flatten h0) (balanced_mul op)) (balancedItems_flatten h1)
  | addSub op a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ BalancedItems BalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ BalancedItems BalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply balancedItems_single
    exact balanced_append (balanced_append (balancedItems_flatten h0) (balanced_add op)) (balancedItems_flatten h1)
  | shift op a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ BalancedItems BalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ BalancedItems BalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply balancedItems_single
    exact balanced_append (balanced_append (balancedItems_flatten h0) (balanced_shift op)) (balancedItems_flatten h1)
  | bitAnd a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ BalancedItems BalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ BalancedItems BalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply balancedItems_single
    exact balanced_append (balanced_append (balancedItems_flatten h0) (balanced_atom rfl)) (balancedItems_flatten h1)
  | bitXor a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ BalancedItems BalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ BalancedItems BalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply balancedItems_single
    exact balanced_append (balanced_append (balancedItems_flatten h0) (balanced_atom rfl)) (balancedItems_flatten h1)
  | bitOr a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ BalancedItems BalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ BalancedItems BalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply balancedItems_single
    exact balanced_append (balanced_append (balancedItems_flatten h0) (balanced_atom rfl)) (balancedItems_flatten h1)
  | order op a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ BalancedItems BalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ BalancedItems BalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply balancedItems_single
    exact balanced_append (balanced_append (balancedItems_flatten h0) (balanced_order op)) (balancedItems_flatten h1)
  | equality op a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ BalancedItems BalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ BalancedItems BalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply balancedItems_single
    exact balanced_append (balanced_append (balancedItems_flatten h0) (balanced_equality op)) (balancedItems_flatten h1)
  | and a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ BalancedItems BalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ BalancedItems BalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply balancedItems_single
    exact balanced_append (balanced_append (balancedItems_flatten h0) (balanced_atom rfl)) (balancedItems_flatten h1)
  | or a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ BalancedItems BalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ BalancedItems BalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply balancedItems_single
    exact balanced_append (balanced_append (balancedItems_flatten h0) (balanced_atom rfl)) (balancedItems_flatten h1)
  | assign op a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ BalancedItems BalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ BalancedItems BalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply balancedItems_single
    exact balanced_append (balanced_append (balancedItems_flatten h0) (balanced_assign op)) (balancedItems_flatten h1)
  | ident name => intro _; exact produces_pure _ _ (balancedItems_single (balanced_idt name))
  | lit l =>
    intro _
    apply produces_bind (litP l) _ Balanced BalancedItems (litP_balanced l)
    intro tokens ht
    exact produces_pure _ _ (balancedItems_single ht)
  | litUnit n u =>
    intro _
    exact produces_pure _ _ (balancedItems_single (balanced_append (balanced_atom rfl) (balanced_atom rfl)))
  | elemType ty ht => intro _; exact produces_pure _ _ (balancedItems_single (balanced_atom rfl))
  | _ => intro impossible; cases impossible

theorem expr_yield_balanced (e : Syn .expr) : Produces e.yield BalancedItems :=
  expressionCategory_yield_balanced e rfl

theorem type_yield_balanced (ty : Syn .typeName) : Produces ty.yield BalancedItems :=
  expressionCategory_yield_balanced ty rfl

/-- The original expression token certificate itself supplies balance. -/
theorem expr_derives_balanced (e : Syn .expr) (ts : List Tok) (h : e.Derives ts) : Balanced ts := by
  obtain ⟨L, ht⟩ := h
  have hy := (expr_toks_iff e L ts).mp ht
  have hi := expr_yield_balanced e L [ts] [] hy
  exact hi ts (List.mem_cons.mpr (Or.inl rfl))

theorem expr_cannot_start_close (k : Bracket) (rest : List Tok) (e : Syn .expr) :
    ¬ e.Derives (closeTok k :: rest) := by
  intro h
  exact balanced_not_close k rest (expr_derives_balanced e _ h)

end Solidity.Frontend.ExpressionUniqueness
