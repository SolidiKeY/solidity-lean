import Solidity.Frontend.ExpressionUniqueness.OperandModeAlgebra
import Solidity.Frontend.ExpressionUniqueness.ExpressionBalance

/-!
# Every successful intrinsic expression yield finishes an operand

The completion bit starts arbitrarily. This unconditional shape invariant uses
only actual successful printer states, including arbitrary layout suffixes.
No precedence, root-split or uniqueness premise is needed.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def ModeDoneItems (items : List (List Tok)) : Prop := ModeDone items.flatten

theorem modeDoneItems_single {ts : List Tok} (h : ModeDone ts) : ModeDoneItems [ts] := by
  simpa only [ModeDoneItems, List.flatten_cons, List.flatten_nil, List.append_nil] using h

def ModeYieldProperty {c : Cat} (e : Syn c) : Prop :=
  match c with
  | .expr | .typeName | .callArgs => Produces e.yield ModeDoneItems
  | _ => True

theorem expression_mode_property {c : Cat} (e : Syn c) : ModeYieldProperty e := by
  induction e with
  | positional es ih =>
    apply produces_bind es.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced es rfl)
    intro items hi
    apply produces_pure
    apply modeDoneItems_single
    exact modeDone_parens (balanced_commaSep hi)
  | named args ih =>
    apply produces_bind args.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced args rfl)
    intro items hi
    apply produces_pure
    apply modeDoneItems_single
    exact modeDone_parens (balanced_braces (balanced_commaSep hi))
  | elem ty => exact produces_pure _ _ (modeDoneItems_single (modeDone_elem ty))
  | userType path => exact produces_pure _ _ (modeDoneItems_single (modeDone_path path))
  | array ty len ihTy ihLen =>
    apply produces_bind ty.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced ty rfl)
    intro types ht
    apply produces_bind len.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced len rfl)
    intro lengths hl
    apply produces_pure
    apply modeDoneItems_single
    simpa only [List.append_assoc] using modeDone_append (balanced_modeAny _ (balancedItems_flatten ht)) (modeDone_square (balancedItems_flatten hl))
  | mapping key keyName value valueName ih =>
    apply produces_bind value.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced value rfl)
    intro items hi
    apply produces_pure
    apply modeDoneItems_single
    exact modeDone_append (balanced_modeAny _ (balanced_tk .mapping)) (modeDone_parens
      (balanced_append (balanced_append (balanced_append (balanced_append
        (balanced_mapping_key key) (balanced_optToks idt balanced_idt keyName))
        (balanced_atom rfl)) (balancedItems_flatten hi)) (balanced_optToks idt balanced_idt valueName)))
  | fnType ps vis mu rets ihPs ihRets =>
    apply produces_bind_all popAttrs _ ModeDoneItems
    intro order
    apply produces_bind ps.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced ps rfl)
    intro params hp
    have hs : ModeStableAttrs (single .vis (optToks Visibility.toks vis) ++
        single .mutab (optToks Mutability.toks mu)) :=
      modeStableAttrs_append (modeStable_single _ _ (modeStable_optToks Visibility.toks modeStable_visibility vis))
        (modeStable_single _ _ (modeStable_optToks Mutability.toks modeStable_mutability mu))
    apply produces_bind (attrsP _ [] order) _ ModeStable ModeDoneItems
      (attrsP_modeStable _ [] order hs modeStableItems_nil)
    intro attrs ha
    apply produces_bind rets.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced rets rfl)
    intro returns hr
    apply produces_pure
    apply modeDoneItems_single
    apply modeDone_stable_append
    · exact modeDone_stable_append
        (modeDone_append (balanced_modeAny _ (balanced_tk .function))
          (modeDone_parens (balanced_commaSep hp))) ha
    · split
      · exact modeStable_nil
      · exact modeDone_stable _ (modeDone_append (balanced_modeAny _ (balanced_tk .returns))
          (modeDone_parens (balanced_commaSep hr)))
  | index e i ih0 ih1 =>
    apply produces_bind e.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced e rfl)
    intro value0 h0
    apply produces_bind i.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced i rfl)
    intro value1 h1
    apply produces_pure
    apply modeDoneItems_single
    simpa only [List.append_assoc] using modeDone_append (balanced_modeAny _ (balancedItems_flatten h0)) (modeDone_square (balancedItems_flatten h1))
  | slice e i j ih0 ih1 ih2 =>
    apply produces_bind e.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced e rfl)
    intro value0 h0
    apply produces_bind i.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced i rfl)
    intro value1 h1
    apply produces_bind j.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced j rfl)
    intro value2 h2
    apply produces_pure
    apply modeDoneItems_single
    simpa only [List.append_assoc] using modeDone_append (balanced_modeAny _ (balancedItems_flatten h0)) (modeDone_square (balanced_append (balanced_append (balancedItems_flatten h1) (balanced_atom rfl)) (balancedItems_flatten h2)))
  | member e name ih0 =>
    apply produces_bind e.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced e rfl)
    intro value0 h0
    apply produces_pure
    apply modeDoneItems_single
    apply modeDone_append (balanced_modeAny _ (balanced_append (balancedItems_flatten h0) (balanced_atom rfl)))
    split <;> exact modeDone_atom _ rfl (fun _ => rfl)
  | callOptions e first rest ih0 ih1 ih2 =>
    apply produces_bind e.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced e rfl)
    intro value0 h0
    apply produces_bind first.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced first rfl)
    intro value1 h1
    apply produces_bind rest.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced rest rfl)
    intro value2 h2
    apply produces_pure
    apply modeDoneItems_single
    exact modeDone_append (balanced_modeAny _ (balancedItems_flatten h0)) (modeDone_braces (balanced_commaSep (balancedItems_cons (balancedItems_flatten h1) h2)))
  | call e args ih0 ih1 =>
    apply produces_bind e.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced e rfl)
    intro value0 h0
    apply produces_bind args.yield _ ModeDoneItems ModeDoneItems ih1
    intro value1 h1
    apply produces_pure
    apply modeDoneItems_single
    exact modeDone_append (balanced_modeAny _ (balancedItems_flatten h0)) h1
  | payableConv args ih0 =>
    apply produces_bind args.yield _ ModeDoneItems ModeDoneItems ih0
    intro value0 h0
    apply produces_pure
    apply modeDoneItems_single
    exact modeDone_append (balanced_modeAny _ (balanced_tk .payable)) h0
  | metaType ty ih0 =>
    apply produces_bind ty.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced ty rfl)
    intro value0 h0
    apply produces_pure
    apply modeDoneItems_single
    exact modeDone_append (balanced_modeAny _ (balanced_tk .type_)) (modeDone_parens (balancedItems_flatten h0))
  | unaryPrefix op e ih0 =>
    apply produces_bind e.yield _ ModeDoneItems ModeDoneItems ih0
    intro value0 h0
    apply produces_pure
    apply modeDoneItems_single
    exact modeDone_append (balanced_modeAny _ (balanced_prefix op)) h0
  | unarySuffix op e ih0 =>
    apply produces_bind e.yield _ ModeDoneItems ModeDoneItems ih0
    intro value0 h0
    apply produces_pure
    apply modeDoneItems_single
    apply modeDone_stable_append h0
    cases op <;> exact modeStable_atom _ rfl rfl
  | exp a b ih0 ih1 =>
    apply produces_bind a.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced a rfl)
    intro value0 h0
    apply produces_bind b.yield _ ModeDoneItems ModeDoneItems ih1
    intro value1 h1
    apply produces_pure
    apply modeDoneItems_single
    exact modeDone_append (balanced_modeAny _ (balanced_append (balancedItems_flatten h0) (balanced_atom rfl))) h1
  | cond c a b ih0 ih1 ih2 =>
    apply produces_bind c.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced c rfl)
    intro value0 h0
    apply produces_bind a.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced a rfl)
    intro value1 h1
    apply produces_bind b.yield _ ModeDoneItems ModeDoneItems ih2
    intro value2 h2
    apply produces_pure
    apply modeDoneItems_single
    exact modeDone_append (balanced_modeAny _ (balanced_append (balanced_append (balanced_append (balancedItems_flatten h0) (balanced_atom rfl)) (balancedItems_flatten h1)) (balanced_atom rfl))) h2
  | new ty ih0 =>
    apply produces_bind ty.yield _ ModeDoneItems ModeDoneItems ih0
    intro value0 h0
    apply produces_pure
    apply modeDoneItems_single
    exact modeDone_append (balanced_modeAny _ (balanced_tk .new)) h0
  | tuple first rest ih0 ih1 =>
    apply produces_bind first.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced first rfl)
    intro value0 h0
    apply produces_bind rest.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced rest rfl)
    intro value1 h1
    apply produces_pure
    apply modeDoneItems_single
    exact modeDone_parens (balanced_append (balancedItems_flatten h0) (balanced_flatMap value1 (fun ts => pu .comma ++ ts) (fun ts ht => balanced_append (balanced_atom rfl) (h1 ts ht))))
  | inlineArray first rest ih0 ih1 =>
    apply produces_bind first.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced first rfl)
    intro value0 h0
    apply produces_bind rest.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced rest rfl)
    intro value1 h1
    apply produces_pure
    apply modeDoneItems_single
    exact modeDone_square (balanced_commaSep (balancedItems_cons (balancedItems_flatten h0) h1))
  | mulDivMod op a b ih0 ih1 =>
    apply produces_bind a.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced a rfl)
    intro value0 h0
    apply produces_bind b.yield _ ModeDoneItems ModeDoneItems ih1
    intro value1 h1
    apply produces_pure
    apply modeDoneItems_single
    exact modeDone_append (balanced_modeAny _ (balanced_append (balancedItems_flatten h0) (balanced_mul op))) h1
  | addSub op a b ih0 ih1 =>
    apply produces_bind a.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced a rfl)
    intro value0 h0
    apply produces_bind b.yield _ ModeDoneItems ModeDoneItems ih1
    intro value1 h1
    apply produces_pure
    apply modeDoneItems_single
    exact modeDone_append (balanced_modeAny _ (balanced_append (balancedItems_flatten h0) (balanced_add op))) h1
  | shift op a b ih0 ih1 =>
    apply produces_bind a.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced a rfl)
    intro value0 h0
    apply produces_bind b.yield _ ModeDoneItems ModeDoneItems ih1
    intro value1 h1
    apply produces_pure
    apply modeDoneItems_single
    exact modeDone_append (balanced_modeAny _ (balanced_append (balancedItems_flatten h0) (balanced_shift op))) h1
  | bitAnd a b ih0 ih1 =>
    apply produces_bind a.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced a rfl)
    intro value0 h0
    apply produces_bind b.yield _ ModeDoneItems ModeDoneItems ih1
    intro value1 h1
    apply produces_pure
    apply modeDoneItems_single
    exact modeDone_append (balanced_modeAny _ (balanced_append (balancedItems_flatten h0) (balanced_atom rfl))) h1
  | bitXor a b ih0 ih1 =>
    apply produces_bind a.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced a rfl)
    intro value0 h0
    apply produces_bind b.yield _ ModeDoneItems ModeDoneItems ih1
    intro value1 h1
    apply produces_pure
    apply modeDoneItems_single
    exact modeDone_append (balanced_modeAny _ (balanced_append (balancedItems_flatten h0) (balanced_atom rfl))) h1
  | bitOr a b ih0 ih1 =>
    apply produces_bind a.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced a rfl)
    intro value0 h0
    apply produces_bind b.yield _ ModeDoneItems ModeDoneItems ih1
    intro value1 h1
    apply produces_pure
    apply modeDoneItems_single
    exact modeDone_append (balanced_modeAny _ (balanced_append (balancedItems_flatten h0) (balanced_atom rfl))) h1
  | order op a b ih0 ih1 =>
    apply produces_bind a.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced a rfl)
    intro value0 h0
    apply produces_bind b.yield _ ModeDoneItems ModeDoneItems ih1
    intro value1 h1
    apply produces_pure
    apply modeDoneItems_single
    exact modeDone_append (balanced_modeAny _ (balanced_append (balancedItems_flatten h0) (balanced_order op))) h1
  | equality op a b ih0 ih1 =>
    apply produces_bind a.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced a rfl)
    intro value0 h0
    apply produces_bind b.yield _ ModeDoneItems ModeDoneItems ih1
    intro value1 h1
    apply produces_pure
    apply modeDoneItems_single
    exact modeDone_append (balanced_modeAny _ (balanced_append (balancedItems_flatten h0) (balanced_equality op))) h1
  | and a b ih0 ih1 =>
    apply produces_bind a.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced a rfl)
    intro value0 h0
    apply produces_bind b.yield _ ModeDoneItems ModeDoneItems ih1
    intro value1 h1
    apply produces_pure
    apply modeDoneItems_single
    exact modeDone_append (balanced_modeAny _ (balanced_append (balancedItems_flatten h0) (balanced_atom rfl))) h1
  | or a b ih0 ih1 =>
    apply produces_bind a.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced a rfl)
    intro value0 h0
    apply produces_bind b.yield _ ModeDoneItems ModeDoneItems ih1
    intro value1 h1
    apply produces_pure
    apply modeDoneItems_single
    exact modeDone_append (balanced_modeAny _ (balanced_append (balancedItems_flatten h0) (balanced_atom rfl))) h1
  | assign op a b ih0 ih1 =>
    apply produces_bind a.yield _ BalancedItems ModeDoneItems (expressionCategory_yield_balanced a rfl)
    intro value0 h0
    apply produces_bind b.yield _ ModeDoneItems ModeDoneItems ih1
    intro value1 h1
    apply produces_pure
    apply modeDoneItems_single
    exact modeDone_append (balanced_modeAny _ (balanced_append (balancedItems_flatten h0) (balanced_assign op))) h1
  | ident name => exact produces_pure _ _ (modeDoneItems_single (modeDone_idt name))
  | lit l =>
    apply produces_bind (litP l) _ ModeDone ModeDoneItems (litP_modeDone l)
    intro tokens ht
    exact produces_pure _ _ (modeDoneItems_single ht)
  | litUnit n u =>
    exact produces_pure _ _ (modeDoneItems_single (modeDone_stable_append
      (modeDone_atom _ rfl (fun _ => rfl)) (modeStable_atom _ rfl rfl)))
  | elemType ty ht => exact produces_pure _ _ (modeDoneItems_single (modeDone_atom _ rfl (fun _ => rfl)))
  | _ => trivial

theorem expr_yield_modeDone (e : Syn .expr) : Produces e.yield ModeDoneItems :=
  expression_mode_property e

theorem type_yield_modeDone (ty : Syn .typeName) : Produces ty.yield ModeDoneItems :=
  expression_mode_property ty

theorem callArgs_yield_modeDone (args : Syn .callArgs) : Produces args.yield ModeDoneItems :=
  expression_mode_property args

theorem expr_derives_modeDone (e : Syn .expr) (ts : List Tok) (hd : e.Derives ts) : ModeDone ts := by
  obtain ⟨L, ht⟩ := hd
  have h : ModeDoneItems [ts] := expr_yield_modeDone e L [ts] [] ((expr_toks_iff e L ts).mp ht)
  simpa only [ModeDoneItems, List.flatten_cons, List.flatten_nil, List.append_nil] using h

end Solidity.Frontend.ExpressionUniqueness
