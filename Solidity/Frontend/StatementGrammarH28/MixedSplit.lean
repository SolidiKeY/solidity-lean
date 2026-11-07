import Solidity.Frontend.StatementGrammarH28.YieldSplit

/-! Mixed self-delimiting statement/item boundaries. Chunk is a token-boundary
predicate, not an AST. IntrinsicItemChunks ties its subjects to actual Syn
yields. Expression-bearing unbraced statements are outside this fragment. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

inductive ControlLeaf where
  | emptyReturn | breakLoop | continueLoop
  deriving DecidableEq, Repr

def ControlLeaf.keyword : ControlLeaf → Kw
  | .emptyReturn => .return_
  | .breakLoop => .break_
  | .continueLoop => .continue_

inductive Chunk : List Tok → Prop where
  | block {body : List Tok} : BraceBalanced body → Chunk (braces body)
  | uncheckedBlock {body : List Tok} : BraceBalanced body →
      Chunk (.kw .unchecked :: braces body)
  | control (c : ControlLeaf) : Chunk [.kw c.keyword, .punct .semi]

/-- This scanner recognizes only the mixed fragment's first boundary. -/
def chunkSuffix : List Tok → Option (List Tok)
  | .punct .lbrace :: rest => closeSuffix 0 rest
  | .kw .unchecked :: .punct .lbrace :: rest => closeSuffix 0 rest
  | .kw .return_ :: .punct .semi :: rest => some rest
  | .kw .break_ :: .punct .semi :: rest => some rest
  | .kw .continue_ :: .punct .semi :: rest => some rest
  | _ => none

theorem chunk_frame {xs : List Tok} (h : Chunk xs) (tail : List Tok) :
    chunkSuffix (xs ++ tail) = some tail := by
  cases h with
  | block hb =>
    simp only [braces, pu, List.cons_append, List.nil_append, List.append_assoc]
    change closeSuffix 0 (_ ++ (.punct .rbrace :: tail)) = some tail
    exact close_after_balanced hb tail
  | uncheckedBlock hb =>
    simp only [braces, pu, List.cons_append, List.nil_append, List.append_assoc]
    change closeSuffix 0 (_ ++ (.punct .rbrace :: tail)) = some tail
    exact close_after_balanced hb tail
  | control c => cases c <;> rfl

theorem chunk_nonempty {xs : List Tok} (h : Chunk xs) : xs ≠ [] := by
  intro he
  have bad := chunk_frame h []
  rw [he] at bad
  cases bad

/-- Mixed block/unchecked/control prefixes have unique content and remainder. -/
theorem chunk_split {xs ys rest tail : List Tok} (hx : Chunk xs) (hy : Chunk ys)
    (he : xs ++ rest = ys ++ tail) : xs = ys ∧ rest = tail := by
  have scan := chunk_frame hx rest
  rw [he, chunk_frame hy tail] at scan
  have suffix : tail = rest := Option.some.inj scan
  subst tail
  exact ⟨List.append_cancel_right he, rfl⟩

/-- Every segment is nonempty and self-delimiting, so an arbitrary finite
mixed sequence has exactly one token-segment decomposition. -/
theorem mixed_chunks_unique (xss : List (List Tok)) :
    ∀ yss : List (List Tok), (∀ xs ∈ xss, Chunk xs) →
      (∀ ys ∈ yss, Chunk ys) → xss.flatten = yss.flatten → xss = yss := by
  induction xss with
  | nil =>
    intro yss hx hy he
    cases yss with
    | nil => rfl
    | cons ys rest =>
      have hn : ys ≠ [] := chunk_nonempty (hy ys (.head _))
      have empty : ys ++ rest.flatten = [] := he.symm
      exact False.elim (hn ((List.eq_nil_of_append_eq_nil empty).1))
  | cons xs rest ih =>
    intro yss hx hy he
    cases yss with
    | nil =>
      have hn : xs ≠ [] := chunk_nonempty (hx xs (.head _))
      have empty : xs ++ rest.flatten = [] := he
      exact False.elim (hn ((List.eq_nil_of_append_eq_nil empty).1))
    | cons ys tail =>
      have split := chunk_split (hx xs (.head _)) (hy ys (.head _)) he
      obtain ⟨heads, tails⟩ := split
      subst ys
      exact congrArg (List.cons xs) (ih tail
        (fun x h => hx x (.tail _ h)) (fun y h => hy y (.tail _ h)) tails)

/-- An actual intrinsic item-list yield whose segments all have the mixed
fragment's boundaries. Layout consumption is preserved exactly. -/
structure IntrinsicItemChunks {k : SCtx} (items : Syn (.list (.item k)))
    (L M : List Choice) (parts : List (List Tok)) : Prop where
  yield_eq : items.yield L = some (parts, M)
  chunks : ∀ part ∈ parts, Chunk part

theorem intrinsic_chunks_nil (k : SCtx) (L : List Choice) :
    IntrinsicItemChunks (Syn.nil (c := .item k)) L L [] :=
  ⟨rfl, fun _part h => nomatch h⟩

theorem intrinsic_chunks_cons {k : SCtx} (x : Syn (.item k))
    (xs : Syn (.list (.item k))) (L N M : List Choice)
    (head : List Tok) (parts : List (List Tok))
    (hx : x.yield L = some ([head], N)) (hc : Chunk head)
    (ht : IntrinsicItemChunks xs N M parts) :
    IntrinsicItemChunks (.cons x xs) L M (head :: parts) := by
  constructor
  · have hy := list_yield_cons_of x xs L N M [head] parts hx ht.yield_eq
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using hy
  · intro part hm
    cases hm with
    | head => exact hc
    | tail _ hm => exact ht.chunks part hm

theorem intrinsic_mixed_split {k j : SCtx}
    {items : Syn (.list (.item k))} {other : Syn (.list (.item j))}
    {L M N P : List Choice} {xs ys : List (List Tok)}
    (hx : IntrinsicItemChunks items L M xs) (hy : IntrinsicItemChunks other N P ys)
    (he : xs.flatten = ys.flatten) : xs = ys :=
  mixed_chunks_unique xs ys hx.chunks hy.chunks he

#print axioms chunk_frame
#print axioms chunk_nonempty
#print axioms chunk_split
#print axioms mixed_chunks_unique
#print axioms intrinsic_chunks_nil
#print axioms intrinsic_chunks_cons
#print axioms intrinsic_mixed_split
end Solidity.Frontend.StatementGrammarH28
