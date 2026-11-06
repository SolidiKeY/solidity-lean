import Solidity.Frontend.StatementGrammarH28.NestedCoverage

/-! Unconditional actual-yield uniqueness inside the recursive block/control
fragment. Common fuel is proved sufficient from both syntax witnesses; no
successful parse or expression uniqueness is assumed. Broader grammar
uniqueness remains separate, including the retained flag counterexample. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

/-- A common syntactic bound turns equality of fragment token lists into
equality of existing intrinsic item lists, using the actual parser. -/
theorem nested_items_token_unique {k : SCtx}
    {xs ys : Syn (.list (.item k))} {ts us : List Tok} {d e : Nat}
    (hx : NestedItems xs ts d) (hy : NestedItems ys us e) (he : ts = us) : xs = ys := by
  subst us
  let s : St := ⟨[], [], 0⟩
  have px := nested_block_coverage hx e s
  have py := nested_block_coverage hy d s
  have fuel : e + d + 4 = d + e + 4 := by omega
  rw [fuel] at px
  have result : (Syn.block xs, s) = (Syn.block ys, s) :=
    Except.ok.inj (px.symm.trans py)
  have trees : Syn.block xs = Syn.block ys := congrArg Prod.fst result
  cases trees
  rfl

theorem nested_block_toks {k : SCtx} {xs : Syn (.list (.item k))}
    {ts : List Tok} {d : Nat} (h : NestedItems xs ts d) :
    (Syn.block xs).toks [] = some (braces ts) := by
  unfold Syn.toks
  rw [nested_block_yield h]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]

/-- The fragment consumes no layout choices. Its actual derivation relation
therefore has exactly the token sequence given by the intrinsic witness. -/
theorem nested_block_derives_iff {k : SCtx} {xs : Syn (.list (.item k))}
    {ts : List Tok} {d : Nat} (h : NestedItems xs ts d) (words : List Tok) :
    (Syn.block xs).Derives words ↔ words = braces ts := by
  constructor
  · intro ⟨L, hy⟩
    unfold Syn.toks at hy
    rw [nested_block_yield h L] at hy
    cases L with
    | nil =>
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hy
      exact (Option.some.inj hy).symm
    | cons choice rest => cases hy
  · intro he
    subst words
    exact ⟨[], nested_block_toks h⟩

/-- Balanced boundary splitting and syntax-derived parser coverage together
recover both syntax and suffix, for arbitrary nested fragment prefixes. -/
theorem nested_block_prefix_unique {k : SCtx}
    {xs ys : Syn (.list (.item k))} {ts us rest tail : List Tok} {d e : Nat}
    (hx : NestedItems xs ts d) (hy : NestedItems ys us e)
    (he : braces ts ++ rest = braces us ++ tail) : xs = ys ∧ rest = tail := by
  obtain ⟨words, suffix⟩ := balanced_braced_split
    (nested_tokens_balanced hx) (nested_tokens_balanced hy) he
  exact ⟨nested_items_token_unique hx hy words, suffix⟩

/-- Actual successful yield uniqueness for all recursive block/control trees
in the indexed fragment, independent of SOL-EU and layout witnesses. -/
theorem nested_block_yield_unique {k : SCtx}
    {xs ys : Syn (.list (.item k))} {ts us words : List Tok} {d e : Nat}
    (hx : NestedItems xs ts d) (hy : NestedItems ys us e)
    (dx : (Syn.block xs).Derives words) (dy : (Syn.block ys).Derives words) : xs = ys := by
  have tx := (nested_block_derives_iff hx words).mp dx
  have ty := (nested_block_derives_iff hy words).mp dy
  have prefixes : braces ts ++ [] = braces us ++ [] := by
    simp only [List.append_nil]
    exact tx.symm.trans ty
  exact (nested_block_prefix_unique hx hy prefixes).1

#print axioms nested_items_token_unique
#print axioms nested_block_toks
#print axioms nested_block_derives_iff
#print axioms nested_block_prefix_unique
#print axioms nested_block_yield_unique
end Solidity.Frontend.StatementGrammarH28
