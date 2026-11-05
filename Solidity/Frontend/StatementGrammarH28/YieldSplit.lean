import Solidity.Frontend.StatementGrammarH28.Balance

/-!
# Exact block/list yield decomposition

These lemmas expose the actual state-threaded yield of existing Syn lists and
blocks, including the intermediate layout. They assume no parser success and
introduce no replacement syntax. Token-tree uniqueness is a separate target.
-/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

theorem block_yield_map {k : SCtx} (items : Syn (.list (.item k))) (L : List Choice) :
    (Syn.block items).yield L =
      (items.yield L).map (fun (parts, M) => ([braces parts.flatten], M)) := by
  simp only [Syn.yield]
  change (items.yield L).bind (fun p => some ([braces p.1.flatten], p.2)) = _
  cases h : items.yield L with
  | none => rfl
  | some result => cases result; rfl

theorem list_cons_yield_bind {c : Cat} (x : Syn c) (xs : Syn (.list c)) (L : List Choice) :
    (Syn.cons x xs).yield L =
      (x.yield L).bind (fun (head, N) =>
        (xs.yield N).map (fun (tail, M) => (head.flatten :: tail, M))) := by
  simp only [Syn.yield]
  change (x.yield L).bind (fun p =>
    (xs.yield p.2).bind (fun q => some (p.1.flatten :: q.1, q.2))) = _
  cases hx : x.yield L with
  | none => rfl
  | some result =>
    obtain ⟨head, N⟩ := result
    change (xs.yield N).bind (fun q => some (head.flatten :: q.1, q.2)) =
      (xs.yield N).map (fun q => (head.flatten :: q.1, q.2))
    cases ht : xs.yield N with
    | none => rfl
    | some result => cases result; rfl

/-- Every successful block yield has exactly one outer braced token segment,
with the same final layout as the yield of its existing intrinsic item list. -/
theorem block_yield_decompose {k : SCtx} (items : Syn (.list (.item k)))
    (L M : List Choice) (segments : List (List Tok))
    (h : (Syn.block items).yield L = some (segments, M)) :
    ∃ parts, items.yield L = some (parts, M) ∧ segments = [braces parts.flatten] := by
  rw [block_yield_map, Option.map_eq_some_iff] at h
  obtain ⟨⟨parts, N⟩, hi, he⟩ := h
  have layouts : N = M := congrArg Prod.snd he
  subst N
  exact ⟨parts, hi, (congrArg Prod.fst he).symm⟩

theorem block_yield_of_items {k : SCtx} (items : Syn (.list (.item k)))
    (L M : List Choice) (parts : List (List Tok))
    (h : items.yield L = some (parts, M)) :
    (Syn.block items).yield L = some ([braces parts.flatten], M) := by
  rw [block_yield_map, h]
  rfl

/-- List decomposition retains the exact intermediate layout N and the
flattened head segment. It works for every existing intrinsic category. -/
theorem list_yield_cons_decompose {c : Cat} (x : Syn c) (xs : Syn (.list c))
    (L M : List Choice) (segments : List (List Tok))
    (h : (Syn.cons x xs).yield L = some (segments, M)) :
    ∃ head tail N, x.yield L = some (head, N) ∧
      xs.yield N = some (tail, M) ∧ segments = head.flatten :: tail := by
  rw [list_cons_yield_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨head, N⟩, hx, ht⟩ := h
  rw [Option.map_eq_some_iff] at ht
  obtain ⟨⟨tail, P⟩, hy, he⟩ := ht
  have layouts : P = M := congrArg Prod.snd he
  subst P
  exact ⟨head, tail, N, hx, hy, (congrArg Prod.fst he).symm⟩

theorem list_yield_cons_of {c : Cat} (x : Syn c) (xs : Syn (.list c))
    (L N M : List Choice) (head tail : List (List Tok))
    (hx : x.yield L = some (head, N)) (ht : xs.yield N = some (tail, M)) :
    (Syn.cons x xs).yield L = some (head.flatten :: tail, M) := by
  rw [list_cons_yield_bind, hx]
  change (xs.yield N).map _ = _
  rw [ht]
  rfl

theorem block_boundary_of_items {k : SCtx} (items : Syn (.list (.item k)))
    (L M : List Choice) (parts : List (List Tok))
    (hy : items.yield L = some (parts, M)) (hb : ∀ part ∈ parts, BraceBalanced part) :
    BlockBoundary (Syn.block items) L M parts.flatten :=
  ⟨block_yield_of_items items L M parts hy, balanced_flatten hb⟩

#print axioms block_yield_map
#print axioms list_cons_yield_bind
#print axioms block_yield_decompose
#print axioms block_yield_of_items
#print axioms list_yield_cons_decompose
#print axioms list_yield_cons_of
#print axioms block_boundary_of_items
end Solidity.Frontend.StatementGrammarH28
