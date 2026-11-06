import Solidity.Frontend.ExpressionUniqueness.ConditionalAlgebra

/-!
# Existing expression yields pair top-level questions and colons

All expression constructors and their type/parameter/call-argument closure are
covered without precedence premises. Named arguments are deliberately not in
this intermediate invariant: their colon is shielded by the actual enclosing
braces. No original syntax, certificate or uniqueness target is restricted.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def ConditionalCategory : Cat → Bool
  | .expr | .typeName | .param | .callArgs => true
  | .list c | .opt c => ConditionalCategory c
  | _ => false

theorem expressionCategory_yield_qBalanced {c : Cat} (e : Syn c) :
    ConditionalCategory c = true → Produces e.yield QBalancedItems := by
  induction e with
  | nil => intro _; exact produces_pure _ _ qBalancedItems_nil
  | none => intro _; exact produces_pure _ _ qBalancedItems_nil
  | @cons c head tail ihHead ihTail =>
    intro hc
    apply produces_bind head.yield _ QBalancedItems QBalancedItems (ihHead hc)
    intro first hf
    apply produces_bind tail.yield _ QBalancedItems QBalancedItems (ihTail hc)
    intro rest hr
    exact produces_pure _ _ (qBalancedItems_cons (qBalancedItems_flatten hf) hr)
  | @some c value ih =>
    intro hc
    apply produces_bind value.yield _ QBalancedItems QBalancedItems (ih hc)
    intro items hi
    exact produces_pure _ _ (qBalancedItems_single (qBalancedItems_flatten hi))
  | positional es ih =>
    intro _
    apply produces_bind es.yield _ QBalancedItems QBalancedItems (ih rfl)
    intro items hi
    exact produces_pure _ _ (qBalancedItems_single (qBalanced_parens (balanced_commaSep (qBalancedItems_balanced hi))))
  | named args ih =>
    intro _
    apply produces_bind args.yield _ BalancedItems QBalancedItems (expressionCategory_yield_balanced args rfl)
    intro items hi
    exact produces_pure _ _ (qBalancedItems_single (qBalanced_parens (balanced_braces (balanced_commaSep hi))))
  | namedArg name e ih => intro impossible; cases impossible
  | param ty loc name ih =>
    intro _
    apply produces_bind ty.yield _ QBalancedItems QBalancedItems (ih rfl)
    intro items hi
    apply produces_pure
    exact qBalancedItems_single (qBalanced_append (qBalanced_append (qBalancedItems_flatten hi)
      (qBalanced_optToks DataLoc.toks qBalanced_dataLoc loc)) (qBalanced_optToks idt qBalanced_idt name))
  | elem ty => intro _; exact produces_pure _ _ (qBalancedItems_single (qBalanced_elem ty))
  | userType path => intro _; exact produces_pure _ _ (qBalancedItems_single (qBalanced_path path))
  | array ty len ihTy ihLen =>
    intro _
    apply produces_bind ty.yield _ QBalancedItems QBalancedItems (ihTy rfl)
    intro types ht
    apply produces_bind len.yield _ QBalancedItems QBalancedItems (ihLen rfl)
    intro lengths hl
    apply produces_pure
    apply qBalancedItems_single
    simpa only [List.append_assoc] using qBalanced_append (qBalancedItems_flatten ht)
      (qBalanced_square (balancedItems_flatten (qBalancedItems_balanced hl)))
  | mapping key keyName value valueName ih =>
    intro _
    apply produces_bind value.yield _ QBalancedItems QBalancedItems (ih rfl)
    intro items hi
    apply produces_pure
    apply qBalancedItems_single
    exact qBalanced_append (qBalanced_tk .mapping) (qBalanced_parens
      (balanced_append (balanced_append (balanced_append (balanced_append
        (balanced_mapping_key key) (balanced_optToks idt balanced_idt keyName))
        (balanced_atom rfl)) (balancedItems_flatten (qBalancedItems_balanced hi)))
        (balanced_optToks idt balanced_idt valueName)))
  | fnType ps vis mu rets ihPs ihRets =>
    intro _
    apply produces_bind_all popAttrs _ QBalancedItems
    intro order
    apply produces_bind ps.yield _ QBalancedItems QBalancedItems (ihPs rfl)
    intro params hp
    have hs : QBalancedAttrs (single .vis (optToks Visibility.toks vis) ++
        single .mutab (optToks Mutability.toks mu)) :=
      qBalancedAttrs_append (qBalanced_single _ _ (qBalanced_optToks Visibility.toks qBalanced_visibility vis))
        (qBalanced_single _ _ (qBalanced_optToks Mutability.toks qBalanced_mutability mu))
    apply produces_bind (attrsP _ [] order) _ QBalanced QBalancedItems
      (attrsP_qBalanced _ [] order hs qBalancedItems_nil)
    intro attrs ha
    apply produces_bind rets.yield _ QBalancedItems QBalancedItems (ihRets rfl)
    intro returns hr
    apply produces_pure
    apply qBalancedItems_single
    apply qBalanced_append (qBalanced_append (qBalanced_append (qBalanced_tk .function)
      (qBalanced_parens (balanced_commaSep (qBalancedItems_balanced hp)))) ha)
    split
    · exact qBalanced_nil
    · exact qBalanced_append (qBalanced_tk .returns) (qBalanced_parens (balanced_commaSep (qBalancedItems_balanced hr)))
  | index e i ih0 ih1 =>
    intro _
    apply produces_bind e.yield _ QBalancedItems QBalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind i.yield _ QBalancedItems QBalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply qBalancedItems_single
    simpa only [List.append_assoc] using qBalanced_append (qBalancedItems_flatten h0) (qBalanced_square (balancedItems_flatten (qBalancedItems_balanced h1)))
  | slice e i j ih0 ih1 ih2 =>
    intro _
    apply produces_bind e.yield _ QBalancedItems QBalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind i.yield _ QBalancedItems QBalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_bind j.yield _ QBalancedItems QBalancedItems (ih2 rfl)
    intro value2 h2
    apply produces_pure
    apply qBalancedItems_single
    simpa only [List.append_assoc] using qBalanced_append (qBalancedItems_flatten h0) (qBalanced_square (balanced_append (balanced_append (balancedItems_flatten (qBalancedItems_balanced h1)) (balanced_atom rfl)) (balancedItems_flatten (qBalancedItems_balanced h2))))
  | member e name ih0 =>
    intro _
    apply produces_bind e.yield _ QBalancedItems QBalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_pure
    apply qBalancedItems_single
    apply qBalanced_append (qBalanced_append (qBalancedItems_flatten h0) (qNeutral_atom rfl rfl))
    split <;> exact qNeutral_atom rfl rfl
  | callOptions e first rest ih0 ih1 ih2 =>
    intro _
    apply produces_bind e.yield _ QBalancedItems QBalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind first.yield _ BalancedItems QBalancedItems (expressionCategory_yield_balanced first rfl)
    intro value1 h1
    apply produces_bind rest.yield _ BalancedItems QBalancedItems (expressionCategory_yield_balanced rest rfl)
    intro value2 h2
    apply produces_pure
    apply qBalancedItems_single
    exact qBalanced_append (qBalancedItems_flatten h0) (qBalanced_braces (balanced_commaSep
      (balancedItems_cons (balancedItems_flatten h1) h2)))
  | call e args ih0 ih1 =>
    intro _
    apply produces_bind e.yield _ QBalancedItems QBalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind args.yield _ QBalancedItems QBalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply qBalancedItems_single
    exact qBalanced_append (qBalancedItems_flatten h0) (qBalancedItems_flatten h1)
  | payableConv args ih0 =>
    intro _
    apply produces_bind args.yield _ QBalancedItems QBalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_pure
    apply qBalancedItems_single
    exact qBalanced_append (qBalanced_tk .payable) (qBalancedItems_flatten h0)
  | metaType ty ih0 =>
    intro _
    apply produces_bind ty.yield _ QBalancedItems QBalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_pure
    apply qBalancedItems_single
    exact qBalanced_append (qBalanced_tk .type_) (qBalanced_parens (balancedItems_flatten (qBalancedItems_balanced h0)))
  | unaryPrefix op e ih0 =>
    intro _
    apply produces_bind e.yield _ QBalancedItems QBalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_pure
    apply qBalancedItems_single
    exact qBalanced_append (qBalanced_prefix op) (qBalancedItems_flatten h0)
  | unarySuffix op e ih0 =>
    intro _
    apply produces_bind e.yield _ QBalancedItems QBalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_pure
    apply qBalancedItems_single
    exact qBalanced_append (qBalancedItems_flatten h0) (qBalanced_suffix op)
  | exp a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ QBalancedItems QBalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ QBalancedItems QBalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply qBalancedItems_single
    exact qBalanced_append (qBalanced_append (qBalancedItems_flatten h0) (qNeutral_atom rfl rfl)) (qBalancedItems_flatten h1)
  | cond c a b ih0 ih1 ih2 =>
    intro _
    apply produces_bind c.yield _ QBalancedItems QBalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind a.yield _ QBalancedItems QBalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_bind b.yield _ QBalancedItems QBalancedItems (ih2 rfl)
    intro value2 h2
    apply produces_pure
    apply qBalancedItems_single
    simpa only [pu, List.append_assoc, List.singleton_append] using
      qBalanced_conditional (qBalancedItems_flatten h0) (qBalancedItems_flatten h1) (qBalancedItems_flatten h2)
  | new ty ih0 =>
    intro _
    apply produces_bind ty.yield _ QBalancedItems QBalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_pure
    apply qBalancedItems_single
    exact qBalanced_append (qBalanced_tk .new) (qBalancedItems_flatten h0)
  | tuple first rest ih0 ih1 =>
    intro _
    apply produces_bind first.yield _ QBalancedItems QBalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind rest.yield _ QBalancedItems QBalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply qBalancedItems_single
    exact qBalanced_parens (balanced_append (balancedItems_flatten (qBalancedItems_balanced h0)) (balanced_flatMap value1 (fun ts => pu .comma ++ ts) (fun ts ht => balanced_append (balanced_atom rfl) (qBalanced_balanced (h1 ts ht)))))
  | inlineArray first rest ih0 ih1 =>
    intro _
    apply produces_bind first.yield _ QBalancedItems QBalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind rest.yield _ QBalancedItems QBalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply qBalancedItems_single
    exact qBalanced_square (balanced_commaSep (balancedItems_cons (balancedItems_flatten (qBalancedItems_balanced h0)) (qBalancedItems_balanced h1)))
  | mulDivMod op a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ QBalancedItems QBalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ QBalancedItems QBalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply qBalancedItems_single
    exact qBalanced_append (qBalanced_append (qBalancedItems_flatten h0) (qBalanced_mul op)) (qBalancedItems_flatten h1)
  | addSub op a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ QBalancedItems QBalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ QBalancedItems QBalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply qBalancedItems_single
    exact qBalanced_append (qBalanced_append (qBalancedItems_flatten h0) (qBalanced_add op)) (qBalancedItems_flatten h1)
  | shift op a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ QBalancedItems QBalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ QBalancedItems QBalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply qBalancedItems_single
    exact qBalanced_append (qBalanced_append (qBalancedItems_flatten h0) (qBalanced_shift op)) (qBalancedItems_flatten h1)
  | bitAnd a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ QBalancedItems QBalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ QBalancedItems QBalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply qBalancedItems_single
    exact qBalanced_append (qBalanced_append (qBalancedItems_flatten h0) (qNeutral_atom rfl rfl)) (qBalancedItems_flatten h1)
  | bitXor a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ QBalancedItems QBalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ QBalancedItems QBalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply qBalancedItems_single
    exact qBalanced_append (qBalanced_append (qBalancedItems_flatten h0) (qNeutral_atom rfl rfl)) (qBalancedItems_flatten h1)
  | bitOr a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ QBalancedItems QBalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ QBalancedItems QBalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply qBalancedItems_single
    exact qBalanced_append (qBalanced_append (qBalancedItems_flatten h0) (qNeutral_atom rfl rfl)) (qBalancedItems_flatten h1)
  | order op a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ QBalancedItems QBalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ QBalancedItems QBalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply qBalancedItems_single
    exact qBalanced_append (qBalanced_append (qBalancedItems_flatten h0) (qBalanced_order op)) (qBalancedItems_flatten h1)
  | equality op a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ QBalancedItems QBalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ QBalancedItems QBalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply qBalancedItems_single
    exact qBalanced_append (qBalanced_append (qBalancedItems_flatten h0) (qBalanced_equality op)) (qBalancedItems_flatten h1)
  | and a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ QBalancedItems QBalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ QBalancedItems QBalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply qBalancedItems_single
    exact qBalanced_append (qBalanced_append (qBalancedItems_flatten h0) (qNeutral_atom rfl rfl)) (qBalancedItems_flatten h1)
  | or a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ QBalancedItems QBalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ QBalancedItems QBalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply qBalancedItems_single
    exact qBalanced_append (qBalanced_append (qBalancedItems_flatten h0) (qNeutral_atom rfl rfl)) (qBalancedItems_flatten h1)
  | assign op a b ih0 ih1 =>
    intro _
    apply produces_bind a.yield _ QBalancedItems QBalancedItems (ih0 rfl)
    intro value0 h0
    apply produces_bind b.yield _ QBalancedItems QBalancedItems (ih1 rfl)
    intro value1 h1
    apply produces_pure
    apply qBalancedItems_single
    exact qBalanced_append (qBalanced_append (qBalancedItems_flatten h0) (qBalanced_assign op)) (qBalancedItems_flatten h1)
  | ident name => intro _; exact produces_pure _ _ (qBalancedItems_single (qBalanced_idt name))
  | lit l =>
    intro _
    apply produces_bind (litP l) _ QBalanced QBalancedItems (litP_qBalanced l)
    intro tokens ht
    exact produces_pure _ _ (qBalancedItems_single ht)
  | litUnit n u =>
    intro _
    exact produces_pure _ _ (qBalancedItems_single (qBalanced_append (qNeutral_atom rfl rfl) (qNeutral_atom rfl rfl)))
  | elemType ty ht => intro _; exact produces_pure _ _ (qBalancedItems_single (qNeutral_atom rfl rfl))
  | _ => intro impossible; cases impossible

theorem expr_yield_qBalanced (e : Syn .expr) : Produces e.yield QBalancedItems :=
  expressionCategory_yield_qBalanced e rfl

theorem expr_derives_qBalanced (e : Syn .expr) (ts : List Tok) (h : e.Derives ts) :
    QBalanced ts := by
  obtain ⟨L, ht⟩ := h
  have hy : e.yield L = some ([ts], []) := (expr_toks_iff e L ts).mp ht
  exact expr_yield_qBalanced e L [ts] [] hy ts (List.mem_singleton.mpr rfl)

end Solidity.Frontend.ExpressionUniqueness
