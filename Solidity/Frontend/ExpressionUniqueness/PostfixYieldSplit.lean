import Solidity.Frontend.ExpressionUniqueness.YieldSplit
import Solidity.Frontend.ExpressionUniqueness.ExpressionBalance

/-!
# Actual postfix and call-argument printer inversion

Recover existing intrinsic children and their successful state executions. No
root split or separate child Derives premise is supplied by the caller.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem triple_pure_success_split {α β γ δ : Type} (p : Pr α) (q : Pr β) (r : Pr γ)
    (render : α → β → γ → δ) (initial final : List Choice) (result : δ)
    (h : (do let x ← p; let y ← q; let z ← r; pure (render x y z)) initial = some (result, final)) :
    ∃ x y z middle next, p initial = some (x, middle) ∧ q middle = some (y, next) ∧
      r next = some (z, final) ∧ result = render x y z := by
  obtain ⟨x, middle, hx, remainder⟩ := bind_success_split p
    (fun x => do let y ← q; let z ← r; pure (render x y z)) initial final result h
  obtain ⟨y, z, next, hy, hz, value⟩ := pair_pure_success_split q r (render x) middle final result remainder
  exact ⟨x, y, z, middle, next, hx, hy, hz, value⟩

theorem index_yield_parts (base : Syn .expr) (index : Syn (.opt .expr))
    (initial final : List Choice) (items : List (List Tok))
    (h : (Syn.index base index).yield initial = some (items, final)) :
    ∃ xs ys middle, base.yield initial = some (xs, middle) ∧ index.yield middle = some (ys, final) ∧
      items = [xs.flatten ++ pu .lbrack ++ ys.flatten ++ pu .rbrack] :=
  pair_pure_success_split base.yield index.yield
    (fun xs ys => [xs.flatten ++ pu .lbrack ++ ys.flatten ++ pu .rbrack]) initial final items h

theorem slice_yield_parts (base : Syn .expr) (start stop : Syn (.opt .expr))
    (initial final : List Choice) (items : List (List Tok))
    (h : (Syn.slice base start stop).yield initial = some (items, final)) :
    ∃ xs ys zs middle next, base.yield initial = some (xs, middle) ∧
      start.yield middle = some (ys, next) ∧ stop.yield next = some (zs, final) ∧
      items = [xs.flatten ++ pu .lbrack ++ ys.flatten ++ pu .colon ++ zs.flatten ++ pu .rbrack] :=
  triple_pure_success_split base.yield start.yield stop.yield
    (fun xs ys zs => [xs.flatten ++ pu .lbrack ++ ys.flatten ++ pu .colon ++ zs.flatten ++ pu .rbrack])
    initial final items h

theorem call_yield_parts (base : Syn .expr) (args : Syn .callArgs)
    (initial final : List Choice) (items : List (List Tok))
    (h : (Syn.call base args).yield initial = some (items, final)) :
    ∃ xs ys middle, base.yield initial = some (xs, middle) ∧ args.yield middle = some (ys, final) ∧
      items = [xs.flatten ++ ys.flatten] :=
  pair_pure_success_split base.yield args.yield (fun xs ys => [xs.flatten ++ ys.flatten]) initial final items h

theorem options_yield_parts (base : Syn .expr) (first : Syn .namedArg) (args : Syn (.list .namedArg))
    (initial final : List Choice) (items : List (List Tok))
    (h : (Syn.callOptions base first args).yield initial = some (items, final)) :
    ∃ xs ys zs middle next, base.yield initial = some (xs, middle) ∧
      first.yield middle = some (ys, next) ∧ args.yield next = some (zs, final) ∧
      items = [xs.flatten ++ braces (commaSep (ys.flatten :: zs))] :=
  triple_pure_success_split base.yield first.yield args.yield
    (fun xs ys zs => [xs.flatten ++ braces (commaSep (ys.flatten :: zs))]) initial final items h

theorem namedArg_yield_parts (name : String) (value : Syn .expr)
    (initial final : List Choice) (items : List (List Tok))
    (h : (Syn.namedArg name value).yield initial = some (items, final)) :
    ∃ xs, value.yield initial = some (xs, final) ∧ items = [idt name ++ pu .colon ++ xs.flatten] :=
  one_pure_success_split value.yield (fun xs => [idt name ++ pu .colon ++ xs.flatten]) initial final items h

theorem callArgs_yield_parens (args : Syn .callArgs) (initial final : List Choice)
    (items : List (List Tok)) (h : args.yield initial = some (items, final)) :
    ∃ payload, items = [parens payload] ∧ Balanced payload := by
  cases args with
  | positional es =>
    obtain ⟨xs, hx, hi⟩ := one_pure_success_split es.yield
      (fun xs => [parens (commaSep xs)]) initial final items h
    exact ⟨commaSep xs, hi, balanced_commaSep (expressionCategory_yield_balanced es rfl initial xs final hx)⟩
  | named names =>
    obtain ⟨xs, hx, hi⟩ := one_pure_success_split names.yield
      (fun xs => [parens (braces (commaSep xs))]) initial final items h
    exact ⟨braces (commaSep xs), hi,
      balanced_braces (balanced_commaSep (expressionCategory_yield_balanced names rfl initial xs final hx))⟩

end Solidity.Frontend.ExpressionUniqueness
