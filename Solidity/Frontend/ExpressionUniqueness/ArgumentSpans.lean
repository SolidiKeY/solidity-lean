import Solidity.Frontend.ExpressionUniqueness.ArgumentWords
import Solidity.Frontend.ExpressionUniqueness.LastEnclosure

/-!
# Positional and named argument constructors reconstruct their word vectors

Actual execution supplies comma freedom, nonempty components and the first-token
boundary separating positional lists from named braces. Empty lists are allowed;
no comma split or argument-tree uniqueness is assumed.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem positional_yield_parts (args : Syn (.list .expr)) (initial final : List Choice)
    (items : List (List Tok)) (hy : (Syn.positional args).yield initial = some (items, final)) :
    ∃ xs, args.yield initial = some (xs, final) ∧ items = [parens (commaSep xs)] :=
  one_pure_success_split args.yield (fun xs => [parens (commaSep xs)]) initial final items hy

theorem named_yield_parts (args : Syn (.list .namedArg)) (initial final : List Choice)
    (items : List (List Tok)) (hy : (Syn.named args).yield initial = some (items, final)) :
    ∃ xs, args.yield initial = some (xs, final) ∧ items = [parens (braces (commaSep xs))] :=
  one_pure_success_split args.yield (fun xs => [parens (braces (commaSep xs))]) initial final items hy

def ArgumentVectorSpans {c : Cat} (args args' : Syn (.list c))
    (initial final initial' final' : List Choice) : Prop :=
  ∃ xs ys, args.yield initial = some (xs, final) ∧ args'.yield initial' = some (ys, final') ∧ xs = ys

theorem positional_argument_spans (args args' : Syn (.list .expr))
    (initial final initial' final' : List Choice) (items items' : List (List Tok))
    (hy : (Syn.positional args).yield initial = some (items, final))
    (hy' : (Syn.positional args').yield initial' = some (items', final'))
    (he : items.flatten = items'.flatten) : ArgumentVectorSpans args args' initial final initial' final' := by
  obtain ⟨xs, hx, shape⟩ := positional_yield_parts args initial final items hy
  obtain ⟨ys, hyb, shape'⟩ := positional_yield_parts args' initial' final' items' hy'
  have free : CommaFreeItems xs := expressionCategory_yield_commaFree args rfl initial xs final hx
  have free' : CommaFreeItems ys := expressionCategory_yield_commaFree args' rfl initial' ys final' hyb
  rw [shape, shape'] at he
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at he
  obtain ⟨emptyPrefix, commas⟩ := last_parens_cut_unique [] (commaSep xs) [] (commaSep ys)
    (balanced_commaSep (commaFreeItems_balanced free)) (balanced_commaSep (commaFreeItems_balanced free')) he
  exact ⟨xs, ys, hx, hyb, commaSep_unique_nonempty_words xs ys free free'
    (expressionList_yield_nonemptyWords args initial xs final hx)
    (expressionList_yield_nonemptyWords args' initial' ys final' hyb) commas⟩

theorem named_argument_spans (args args' : Syn (.list .namedArg))
    (initial final initial' final' : List Choice) (items items' : List (List Tok))
    (hy : (Syn.named args).yield initial = some (items, final))
    (hy' : (Syn.named args').yield initial' = some (items', final'))
    (he : items.flatten = items'.flatten) : ArgumentVectorSpans args args' initial final initial' final' := by
  obtain ⟨xs, hx, shape⟩ := named_yield_parts args initial final items hy
  obtain ⟨ys, hyb, shape'⟩ := named_yield_parts args' initial' final' items' hy'
  have free : CommaFreeItems xs := expressionCategory_yield_commaFree args rfl initial xs final hx
  have free' : CommaFreeItems ys := expressionCategory_yield_commaFree args' rfl initial' ys final' hyb
  have bal : Balanced (commaSep xs) := balanced_commaSep (commaFreeItems_balanced free)
  have bal' : Balanced (commaSep ys) := balanced_commaSep (commaFreeItems_balanced free')
  rw [shape, shape'] at he
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at he
  obtain ⟨emptyPrefix, bracesWord⟩ := last_parens_cut_unique [] (braces (commaSep xs)) [] (braces (commaSep ys))
    (balanced_braces bal) (balanced_braces bal') he
  obtain ⟨emptyPrefix', commas⟩ := last_braces_cut_unique [] (commaSep xs) [] (commaSep ys) bal bal' bracesWord
  exact ⟨xs, ys, hx, hyb, commaSep_unique_nonempty_words xs ys free free'
    (namedArgList_yield_nonemptyWords args initial xs final hx)
    (namedArgList_yield_nonemptyWords args' initial' ys final' hyb) commas⟩

theorem positional_named_yields_disjoint (args : Syn (.list .expr)) (names : Syn (.list .namedArg))
    (initial final initial' final' : List Choice) (items items' : List (List Tok))
    (hy : (Syn.positional args).yield initial = some (items, final))
    (hy' : (Syn.named names).yield initial' = some (items', final')) : items.flatten ≠ items'.flatten := by
  intro he
  obtain ⟨xs, hx, shape⟩ := positional_yield_parts args initial final items hy
  obtain ⟨ys, hyb, shape'⟩ := named_yield_parts names initial' final' items' hy'
  have first : StartFree (commaSep xs) := startFree_commaSep xs
    (expressionCategory_yield_startFree args rfl initial xs final hx)
  have namesBal : Balanced (commaSep ys) := balanced_commaSep
    (expressionCategory_yield_balanced names rfl initial' ys final' hyb)
  rw [shape, shape'] at he
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at he
  obtain ⟨emptyPrefix, payload⟩ := last_parens_cut_unique [] (commaSep xs) [] (braces (commaSep ys))
    first.1 (balanced_braces namesBal) he
  apply first.2 (commaSep ys ++ [.punct .rbrace])
  simpa only [braces, pu, List.cons_append, List.nil_append, List.append_assoc] using payload

end Solidity.Frontend.ExpressionUniqueness
