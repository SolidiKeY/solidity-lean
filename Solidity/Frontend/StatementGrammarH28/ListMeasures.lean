import Solidity.Frontend.StatementGrammarH28.FramedItemList
import Solidity.Frontend.StatementGrammarH28.BlockLeafCoverage

/-! Universal intrinsic list measures for block/parser iteration budgets.
Successful printer yield is the only yield premise. No parser success or
expression uniqueness is assumed; the generic nonempty premise is discharged
for every statement and item constructor in the public specializations. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

theorem list_length_values {c : Cat} (xs : Syn (.list c)) :
    g0ListLength xs = (g0ListValues xs).length := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    rw [g0ListLength_cons, g0ListValues_cons, List.length_cons, list_length_values xs]
termination_by xs

theorem list_yield_length {c : Cat} (xs : Syn (.list c))
    (L M : List Choice) (parts : List (List Tok))
    (hy : xs.yield L = some (parts, M)) : parts.length = g0ListLength xs := by
  cases xs with
  | nil =>
    have eq : parts = [] := (congrArg Prod.fst (Option.some.inj hy)).symm
    subst parts
    rfl
  | cons x xs =>
    obtain ⟨head, tail, N, hh, ht, he⟩ := list_yield_cons_decompose x xs L M parts hy
    subst parts
    rw [List.length_cons, g0ListLength_cons, list_yield_length xs N M tail ht]
termination_by xs

theorem list_yield_chunks_nonempty {c : Cat}
    (hn : ∀ (x : Syn c) (L M : List Choice) (parts : List (List Tok)),
      x.yield L = some (parts, M) → parts.flatten ≠ [])
    (xs : Syn (.list c)) (L M : List Choice) (parts : List (List Tok))
    (hy : xs.yield L = some (parts, M)) : ∀ chunk ∈ parts, chunk ≠ [] := by
  cases xs with
  | nil =>
    have eq : parts = [] := (congrArg Prod.fst (Option.some.inj hy)).symm
    subst parts
    intro chunk hc
    cases hc
  | cons x xs =>
    obtain ⟨head, tail, N, hh, ht, he⟩ := list_yield_cons_decompose x xs L M parts hy
    subst parts
    intro chunk hc
    cases hc with
    | head => exact hn x L N head hh
    | tail _ hc => exact list_yield_chunks_nonempty hn xs N M tail ht chunk hc
termination_by xs

theorem nonempty_chunks_token_bound (parts : List (List Tok))
    (hn : ∀ chunk ∈ parts, chunk ≠ []) : parts.length ≤ parts.flatten.length := by
  induction parts with
  | nil => exact Nat.le_refl 0
  | cons chunk rest ih =>
    have head := hn chunk (.head _)
    have positive : 0 < chunk.length := by
      cases chunk with
      | nil => exact False.elim (head rfl)
      | cons t ts => exact Nat.zero_lt_succ _
    have tail := ih (fun c hc => hn c (.tail _ hc))
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    omega

theorem list_yield_token_bound {c : Cat}
    (hn : ∀ (x : Syn c) (L M : List Choice) (parts : List (List Tok)),
      x.yield L = some (parts, M) → parts.flatten ≠ [])
    (xs : Syn (.list c)) (L M : List Choice) (parts : List (List Tok))
    (hy : xs.yield L = some (parts, M)) : g0ListLength xs ≤ parts.flatten.length := by
  rw [← list_yield_length xs L M parts hy]
  exact nonempty_chunks_token_bound parts (list_yield_chunks_nonempty hn xs L M parts hy)

theorem statement_list_yield_token_bound {k : SCtx} (xs : Syn (.list (.stmt k)))
    (L M : List Choice) (parts : List (List Tok))
    (hy : xs.yield L = some (parts, M)) : g0ListLength xs ≤ parts.flatten.length :=
  list_yield_token_bound statement_yield_nonempty xs L M parts hy

theorem item_list_yield_token_bound {k : SCtx} (xs : Syn (.list (.item k)))
    (L M : List Choice) (parts : List (List Tok))
    (hy : xs.yield L = some (parts, M)) : g0ListLength xs ≤ parts.flatten.length :=
  list_yield_token_bound item_yield_nonempty xs L M parts hy

/-- The actual many counter on located input has room for one iteration per
represented item and the final stopping iteration, for every suffix state.
This establishes the iteration budget only, not success of the item parser. -/
theorem item_list_many_iteration_budget {k : SCtx} (xs : Syn (.list (.item k)))
    (L M : List Choice) (parts : List (List Tok))
    (hy : xs.yield L = some (parts, M)) (s : St) :
    g0ListLength xs + 1 ≤ (locatedInput parts.flatten s).ts.length + 1 := by
  have bound := item_list_yield_token_bound xs L M parts hy
  simp only [locatedInput, List.length_append, List.length_map]
  omega

theorem statement_list_many_iteration_budget {k : SCtx} (xs : Syn (.list (.stmt k)))
    (L M : List Choice) (parts : List (List Tok))
    (hy : xs.yield L = some (parts, M)) (s : St) :
    g0ListLength xs + 1 ≤ (locatedInput parts.flatten s).ts.length + 1 := by
  have bound := statement_list_yield_token_bound xs L M parts hy
  simp only [locatedInput, List.length_append, List.length_map]
  omega

#print axioms list_length_values
#print axioms list_yield_length
#print axioms list_yield_chunks_nonempty
#print axioms nonempty_chunks_token_bound
#print axioms list_yield_token_bound
#print axioms statement_list_yield_token_bound
#print axioms item_list_yield_token_bound
#print axioms item_list_many_iteration_budget
#print axioms statement_list_many_iteration_budget
end Solidity.Frontend.StatementGrammarH28
