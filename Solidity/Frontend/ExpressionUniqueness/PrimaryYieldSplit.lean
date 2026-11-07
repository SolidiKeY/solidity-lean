import Solidity.Frontend.ExpressionUniqueness.PostfixYieldSplit

/-!
# Actual primary printer components and balanced enclosures

Existing intrinsic child nodes and their layout executions are recovered from
successful yields. All enclosure invariants follow from those executions.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem new_yield_parts (ty : Syn .typeName) (initial final : List Choice) (items : List (List Tok))
    (hy : (Syn.new ty).yield initial = some (items, final)) :
    ∃ xs, ty.yield initial = some (xs, final) ∧ items = [tk .new ++ xs.flatten] :=
  one_pure_success_split ty.yield (fun xs => [tk .new ++ xs.flatten]) initial final items hy

theorem payable_yield_parts (args : Syn .callArgs) (initial final : List Choice) (items : List (List Tok))
    (hy : (Syn.payableConv args).yield initial = some (items, final)) :
    ∃ xs, args.yield initial = some (xs, final) ∧ items = [tk .payable ++ xs.flatten] :=
  one_pure_success_split args.yield (fun xs => [tk .payable ++ xs.flatten]) initial final items hy

theorem meta_yield_parts (ty : Syn .typeName) (initial final : List Choice) (items : List (List Tok))
    (hy : (Syn.metaType ty).yield initial = some (items, final)) :
    ∃ xs, ty.yield initial = some (xs, final) ∧ items = [tk .type_ ++ parens xs.flatten] :=
  one_pure_success_split ty.yield (fun xs => [tk .type_ ++ parens xs.flatten]) initial final items hy

theorem tuple_yield_parts (first : Syn (.opt .expr)) (rest : Syn (.list (.opt .expr)))
    (initial final : List Choice) (items : List (List Tok))
    (hy : (Syn.tuple first rest).yield initial = some (items, final)) :
    ∃ xs ys middle, first.yield initial = some (xs, middle) ∧ rest.yield middle = some (ys, final) ∧
      items = [parens (xs.flatten ++ ys.flatMap (pu .comma ++ ·))] :=
  pair_pure_success_split first.yield rest.yield
    (fun xs ys => [parens (xs.flatten ++ ys.flatMap (pu .comma ++ ·))]) initial final items hy

theorem inline_yield_parts (first : Syn .expr) (rest : Syn (.list .expr))
    (initial final : List Choice) (items : List (List Tok))
    (hy : (Syn.inlineArray first rest).yield initial = some (items, final)) :
    ∃ xs ys middle, first.yield initial = some (xs, middle) ∧ rest.yield middle = some (ys, final) ∧
      items = [pu .lbrack ++ commaSep (xs.flatten :: ys) ++ pu .rbrack] :=
  pair_pure_success_split first.yield rest.yield
    (fun xs ys => [pu .lbrack ++ commaSep (xs.flatten :: ys) ++ pu .rbrack]) initial final items hy

theorem payable_actual_parens (args : Syn .callArgs) (initial final : List Choice)
    (items : List (List Tok)) (hy : (Syn.payableConv args).yield initial = some (items, final)) :
    ∃ payload, Balanced payload ∧ items = [tk .payable ++ parens payload] := by
  obtain ⟨xs, hx, shape⟩ := payable_yield_parts args initial final items hy
  obtain ⟨payload, argShape, bal⟩ := callArgs_yield_parens args initial final xs hx
  refine ⟨payload, bal, ?_⟩
  rw [shape, argShape]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]

theorem meta_actual_parens (ty : Syn .typeName) (initial final : List Choice)
    (items : List (List Tok)) (hy : (Syn.metaType ty).yield initial = some (items, final)) :
    ∃ payload, Balanced payload ∧ items = [tk .type_ ++ parens payload] := by
  obtain ⟨xs, hx, shape⟩ := meta_yield_parts ty initial final items hy
  exact ⟨xs.flatten, balancedItems_flatten (expressionCategory_yield_balanced ty rfl initial xs final hx), shape⟩

theorem tuple_actual_parens (first : Syn (.opt .expr)) (rest : Syn (.list (.opt .expr)))
    (initial final : List Choice) (items : List (List Tok))
    (hy : (Syn.tuple first rest).yield initial = some (items, final)) :
    ∃ payload, Balanced payload ∧ items = [parens payload] := by
  obtain ⟨xs, ys, middle, hx, hr, shape⟩ := tuple_yield_parts first rest initial final items hy
  have firstBal : Balanced xs.flatten := balancedItems_flatten
    (expressionCategory_yield_balanced first rfl initial xs middle hx)
  have restBal : BalancedItems ys := expressionCategory_yield_balanced rest rfl middle ys final hr
  refine ⟨xs.flatten ++ ys.flatMap (pu .comma ++ ·), ?_, shape⟩
  exact balanced_append firstBal (balanced_flatMap ys (pu .comma ++ ·)
    (fun word hw => balanced_append (balanced_atom rfl) (restBal word hw)))

theorem inline_actual_square (first : Syn .expr) (rest : Syn (.list .expr))
    (initial final : List Choice) (items : List (List Tok))
    (hy : (Syn.inlineArray first rest).yield initial = some (items, final)) :
    ∃ payload, Balanced payload ∧ items = [pu .lbrack ++ payload ++ pu .rbrack] := by
  obtain ⟨xs, ys, middle, hx, hr, shape⟩ := inline_yield_parts first rest initial final items hy
  have firstBal : Balanced xs.flatten := balancedItems_flatten
    (expressionCategory_yield_balanced first rfl initial xs middle hx)
  have restBal : BalancedItems ys := expressionCategory_yield_balanced rest rfl middle ys final hr
  exact ⟨commaSep (xs.flatten :: ys), balanced_commaSep (balancedItems_cons firstBal restBal), shape⟩

end Solidity.Frontend.ExpressionUniqueness
