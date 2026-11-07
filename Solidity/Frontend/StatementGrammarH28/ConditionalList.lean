import Solidity.Frontend.StatementGrammarH28.ConditionalYield
import Solidity.Frontend.StatementGrammarH28.SyntaxBalance

/-! Arbitrary-width intrinsic item lists from the recursive Boolean fragment.
Next-statement tokens supply the preceding open-if boundary. No general item
or unchecked coverage, block parser completeness or expression uniqueness claim. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

theorem boolean_statement_no_else_input {k : SCtx} {x : Syn (.stmt k)}
    {ts : List Tok} {d : Nat} (h : BooleanStatements x ts d) (s : St) :
    NoFollowingElse (locatedInput ts s) := by
  cases h with
  | loops h => cases h <;> intro bad <;> cases bad
  | ifNone => intro bad; cases bad
  | ifSome => intro bad; cases bad
  | whileLoop => intro bad; cases bad
  | forLoop => intro bad; cases bad
  | doLoop => intro bad; cases bad

theorem boolean_statement_tokens_nonempty {k : SCtx} {x : Syn (.stmt k)}
    {ts : List Tok} {d : Nat} (h : BooleanStatements x ts d) : ts ≠ [] := by
  intro he
  subst ts
  exact boolean_statement_no_else_input h (locatedInput [.kw .else_] ⟨[], [], 0⟩) rfl

inductive BooleanItemList : {k : SCtx} → Syn (.list (.item k)) → List (List Tok) → Prop where
  | nil {k : SCtx} : BooleanItemList (Syn.nil (c := .item k)) []
  | cons {k : SCtx} {x : Syn (.stmt k)} {xs : Syn (.list (.item k))}
      {ts : List Tok} {parts : List (List Tok)} {d : Nat} :
      BooleanStatements x ts d → BooleanItemList xs parts →
      BooleanItemList (.cons (.stmtItem x) xs) (ts :: parts)

theorem boolean_item_list_no_else {k : SCtx} {xs : Syn (.list (.item k))}
    {parts : List (List Tok)} (h : BooleanItemList xs parts) (s : St)
    (hs : NoFollowingElse s) : NoFollowingElse (locatedInput parts.flatten s) := by
  cases h with
  | nil => exact hs
  | cons hx ht =>
    rw [List.flatten_cons, locatedInput_append]
    exact boolean_statement_no_else_input hx _

theorem boolean_item_list_yield {k : SCtx} {xs : Syn (.list (.item k))}
    {parts : List (List Tok)} (h : BooleanItemList xs parts) (L : List Choice) :
    xs.yield L = some (parts, L) := by
  induction h with
  | nil => rfl
  | @cons x xs ts parts d hx ht ih =>
    have item : (Syn.stmtItem x).yield L = some ([ts], L) := by
      rw [Syn.yield]
      exact boolean_statements_yield hx L
    rw [Syn.yield]
    change ((Syn.stmtItem x).yield L).bind (fun p =>
      (xs.yield p.2).bind (fun q => some (p.1.flatten :: q.1, q.2))) = _
    rw [item, Option.bind_some, ih]
    simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil]

/-- The next item cannot start else. Thus the prefix theorem supplies both
head-tree equality and a strictly smaller tail equation at every cons. -/
theorem boolean_item_list_token_unique {k : SCtx} {xs ys : Syn (.list (.item k))}
    {parts qs : List (List Tok)} (hx : BooleanItemList xs parts)
    (hy : BooleanItemList ys qs) (he : parts.flatten = qs.flatten) : xs = ys := by
  induction hx generalizing ys qs with
  | nil =>
    cases hy with
    | nil => rfl
    | cons hh ht =>
      simp only [List.flatten_nil, List.flatten_cons] at he
      exact False.elim (boolean_statement_tokens_nonempty hh (List.eq_nil_of_append_eq_nil he.symm).1)
  | @cons x xs ts parts d hh ht ih =>
    cases hy with
    | nil =>
      simp only [List.flatten_nil, List.flatten_cons] at he
      exact False.elim (boolean_statement_tokens_nonempty hh (List.eq_nil_of_append_eq_nil he).1)
    | @cons y ys us qs e hyh hyt =>
      simp only [List.flatten_cons] at he
      let s : St := ⟨[], [], 0⟩
      have stop : NoFollowingElse s := by intro bad; cases bad
      obtain ⟨tree, tail⟩ := boolean_statements_prefix_unique hh hyh s
        (Or.inr (boolean_item_list_no_else ht s stop))
        (Or.inr (boolean_item_list_no_else hyt s stop)) he
      have rest := ih hyt tail
      subst y
      subst ys
      rfl

theorem boolean_item_segments_unique {k : SCtx} {xs ys : Syn (.list (.item k))}
    {parts qs : List (List Tok)} (hx : BooleanItemList xs parts)
    (hy : BooleanItemList ys qs) (he : parts.flatten = qs.flatten) : xs = ys ∧ parts = qs := by
  have tree := boolean_item_list_token_unique hx hy he
  subst ys
  have segments := (boolean_item_list_yield hx []).symm.trans (boolean_item_list_yield hy [])
  exact ⟨rfl, congrArg Prod.fst (Option.some.inj segments)⟩

theorem boolean_item_list_derives_iff {k : SCtx} {xs : Syn (.list (.item k))}
    {parts : List (List Tok)} (h : BooleanItemList xs parts) (words : List Tok) :
    xs.Derives words ↔ words = parts.flatten := by
  constructor
  · intro ⟨L, hy⟩
    unfold Syn.toks at hy
    rw [boolean_item_list_yield h L] at hy
    cases L with
    | nil => exact (Option.some.inj hy).symm
    | cons choice rest => cases hy
  · intro he
    subst words
    refine ⟨[], ?_⟩
    unfold Syn.toks
    rw [boolean_item_list_yield h []]

theorem boolean_item_list_yield_unique {k : SCtx} {xs ys : Syn (.list (.item k))}
    {parts qs : List (List Tok)} {words : List Tok} (hx : BooleanItemList xs parts)
    (hy : BooleanItemList ys qs) (dx : xs.Derives words) (dy : ys.Derives words) :
    xs = ys ∧ parts = qs :=
  boolean_item_segments_unique hx hy
    (((boolean_item_list_derives_iff hx words).mp dx).symm.trans
      ((boolean_item_list_derives_iff hy words).mp dy))

theorem boolean_item_list_balanced {k : SCtx} {xs : Syn (.list (.item k))}
    {parts : List (List Tok)} (h : BooleanItemList xs parts) : BraceBalanced parts.flatten :=
  balancedParts_flat (syntax_yield_balanced xs rfl [] parts [] (boolean_item_list_yield h []))

theorem boolean_item_block_yield {k : SCtx} {xs : Syn (.list (.item k))}
    {parts : List (List Tok)} (h : BooleanItemList xs parts) (L : List Choice) :
    (Syn.block xs).yield L = some ([braces parts.flatten], L) :=
  block_yield_of_items xs L L parts (boolean_item_list_yield h L)

/-- Balanced block splitting combines with conditional item segmentation to
recover the intrinsic contents, each statement's tokens and an arbitrary suffix. -/
theorem boolean_item_block_prefix_unique {k : SCtx} {xs ys : Syn (.list (.item k))}
    {parts qs : List (List Tok)} {rest tail : List Tok}
    (hx : BooleanItemList xs parts) (hy : BooleanItemList ys qs)
    (he : braces parts.flatten ++ rest = braces qs.flatten ++ tail) :
    xs = ys ∧ parts = qs ∧ rest = tail := by
  obtain ⟨inner, suffix⟩ := balanced_braced_split
    (boolean_item_list_balanced hx) (boolean_item_list_balanced hy) he
  obtain ⟨tree, segments⟩ := boolean_item_segments_unique hx hy inner
  exact ⟨tree, segments, suffix⟩

#print axioms boolean_item_list_balanced
#print axioms boolean_item_block_yield
#print axioms boolean_item_block_prefix_unique
#print axioms boolean_statement_no_else_input
#print axioms boolean_statement_tokens_nonempty
#print axioms boolean_item_list_no_else
#print axioms boolean_item_list_yield
#print axioms boolean_item_list_token_unique
#print axioms boolean_item_segments_unique
#print axioms boolean_item_list_derives_iff
#print axioms boolean_item_list_yield_unique
end Solidity.Frontend.StatementGrammarH28
