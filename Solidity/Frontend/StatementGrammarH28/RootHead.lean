import Solidity.Frontend.StatementGrammarH28.SyntaxHead
import Solidity.Frontend.StatementGrammarH28.TokenRoot

/-! Complete raw-yield statement-root collision classification. Simple and
contextual revert remain the only possible unequal-root pair. This theorem
does not omit that pair or claim it impossible without the existing contract. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

theorem simple_statement_yield_safe (s : Syn .simple) {k : SCtx} :
    PrEnsures (Syn.simpleStmt (k := k) s).yield SafeParts := by
  rw [Syn.yield]
  apply ensures_bind_checked _ _ SafeParts SafeParts (simple_yield_safe_start s)
  intro a ha
  apply ensures_pure _ SafeParts
  simpa only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil] using
    safe_start_append ha (pu .semi)

theorem simple_root_yield_safe {k : SCtx} (s : Syn (.stmt k)) (h : root s = .simple) :
    PrEnsures s.yield SafeParts := by
  cases s with
  | simpleStmt simple => exact simple_statement_yield_safe simple
  | _ => cases h

theorem root_hard_token (r : Root) (hs : r ≠ .simple) (hr : r ≠ .revertError) :
    ∃ tok, r.firstToken = some tok ∧ hardStatementToken tok = true := by
  cases r <;> first
    | exact ⟨_, rfl, rfl⟩
    | exact False.elim (hs rfl)
    | exact False.elim (hr rfl)

/-- Actual simple-statement yields cannot share a prefix with any fixed hard
statement root, at arbitrary contexts, input/output layouts and suffixes. -/
theorem simple_hard_prefix_distinct {k j : SCtx}
    (s : Syn (.stmt k)) (t : Syn (.stmt j))
    (hs : root s = .simple) (ht : root t ≠ .simple) (hr : root t ≠ .revertError)
    (L M N P : List Choice) (xs ys : List (List Tok)) (rest tail : List Tok)
    (hyS : s.yield L = some (xs, M)) (hyT : t.yield N = some (ys, P)) :
    xs.flatten ++ rest ≠ ys.flatten ++ tail := by
  intro he
  obtain ⟨tok, hfirst, hhard⟩ := root_hard_token (root t) ht hr
  obtain ⟨a, after, words, hsafe⟩ := simple_root_yield_safe s hs L xs M hyS
  have headS : xs.flatten.head? = some a := by rw [words]; rfl
  have headT : ys.flatten.head? = some tok := statement_fixed_head t tok hfirst N ys P hyT
  have prefixS := head_append_of_some xs.flatten rest a headS
  have prefixT := head_append_of_some ys.flatten tail tok headT
  rw [he, prefixT] at prefixS
  have tokenEq : tok = a := Option.some.inj prefixS
  subst tok
  have bad : false = true := hsafe.symm.trans hhard
  cases bad

/-- Universal classification, without a root exclusion or expression premise.
The contextual simple/revert ambiguity is reported, not silently discarded. -/
theorem statement_root_collision_cases {k j : SCtx}
    (s : Syn (.stmt k)) (t : Syn (.stmt j))
    (L M N P : List Choice) (xs ys : List (List Tok)) (rest tail : List Tok)
    (hyS : s.yield L = some (xs, M)) (hyT : t.yield N = some (ys, P))
    (he : xs.flatten ++ rest = ys.flatten ++ tail) :
    root s = root t ∨ (root s = .simple ∧ root t = .revertError) ∨
      (root s = .revertError ∧ root t = .simple) := by
  by_cases hs : root s = .simple
  · by_cases ht : root t = .simple
    · exact Or.inl (hs.trans ht.symm)
    · by_cases hr : root t = .revertError
      · exact Or.inr (Or.inl ⟨hs, hr⟩)
      · exact False.elim (simple_hard_prefix_distinct s t hs ht hr L M N P xs ys rest tail hyS hyT he)
  · by_cases ht : root t = .simple
    · by_cases hr : root s = .revertError
      · exact Or.inr (Or.inr ⟨hr, ht⟩)
      · exact False.elim (simple_hard_prefix_distinct t s ht hs hr N P L M ys xs tail rest hyT hyS he.symm)
    · exact Or.inl (nonSimple_root_of_equal_prefix s t hs ht L M N P xs ys rest tail hyS hyT he)

#print axioms simple_statement_yield_safe
#print axioms simple_root_yield_safe
#print axioms root_hard_token
#print axioms simple_hard_prefix_distinct
#print axioms statement_root_collision_cases
end Solidity.Frontend.StatementGrammarH28
