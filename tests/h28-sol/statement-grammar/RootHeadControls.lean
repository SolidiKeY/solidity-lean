import Solidity.Frontend.StatementGrammarH28.RootHead
import Solidity.Frontend.Checked.Prec
import Solidity.Frontend.StatementGrammarH28.BlockLeafCoverage

/-! Inhabited leading-token controls and the raw contextual-revert collision.
The collision does not satisfy the existing revert precedence/path contract. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

theorem empty_string_still_has_token :
    (Syn.lit (.str [])).yield [.frags [0]] = some ([[.str []]], []) := by decide +kernel

theorem empty_fragment_choice_refused :
    (Syn.lit (.str [])).yield [.frags []] = none := by decide +kernel

theorem zero_fragment_first_token_safe : SafeParts [[.str []]] :=
  expression_yield_safe_start (.lit (.str [])) [.frags [0]] [[.str []]] []
    empty_string_still_has_token

theorem arbitrary_simple_vs_return {k j : SCtx} (s : Syn .simple) (e : Syn (.opt .expr))
    (L M N P : List Choice) (xs ys : List (List Tok)) (rest tail : List Tok)
    (hs : (Syn.simpleStmt (k := k) s).yield L = some (xs, M))
    (hr : (Syn.returnStmt (k := j) e).yield N = some (ys, P)) :
    xs.flatten ++ rest ≠ ys.flatten ++ tail :=
  simple_hard_prefix_distinct (.simpleStmt s) (.returnStmt e) rfl
    (by intro h; cases h) (by intro h; cases h) L M N P xs ys rest tail hs hr

def rawRevertStmt : Syn (.stmt .body) :=
  .revert (.tuple (.some (.ident "E")) .nil) (.positional .nil)

def rawSimpleStmt : Syn (.stmt .body) :=
  .simpleStmt (.exprStmt (.call
    (.call (.ident "revert") (.positional (.cons (.ident "E") .nil))) (.positional .nil)))

def rawRevertTokens : List Tok :=
  [.ident "revert", .punct .lparen, .ident "E", .punct .rparen,
   .punct .lparen, .punct .rparen, .punct .semi]

theorem raw_pair_successful_yields :
    rawRevertStmt.yield [] = some ([rawRevertTokens], []) ∧
    rawSimpleStmt.yield [] = some ([rawRevertTokens], []) := by decide +kernel

theorem raw_pair_successful_toks :
    rawRevertStmt.toks [] = some rawRevertTokens ∧
    rawSimpleStmt.toks [] = some rawRevertTokens := by decide +kernel

theorem raw_pair_different_roots : root rawRevertStmt ≠ root rawSimpleStmt := by
  intro h
  cases h

theorem raw_pair_contract_boundary : rawRevertStmt.prec = false ∧ rawSimpleStmt.prec = true := by
  decide +kernel

/-- The actual token parser selects the simple call chain. The raw revert
candidate violates the existing path contract; no contract result is refuted. -/
theorem raw_pair_parser_selects_simple (n : Nat) (s : St) :
    stmt (n + 20) .body (locatedInput rawRevertTokens s) = .ok (rawSimpleStmt, s) := by
  rfl

theorem raw_pair_classified :
    root rawRevertStmt = root rawSimpleStmt ∨
      (root rawRevertStmt = .simple ∧ root rawSimpleStmt = .revertError) ∨
      (root rawRevertStmt = .revertError ∧ root rawSimpleStmt = .simple) :=
  statement_root_collision_cases rawRevertStmt rawSimpleStmt [] [] [] []
    [rawRevertTokens] [rawRevertTokens] [] []
    raw_pair_successful_yields.1 raw_pair_successful_yields.2 rfl

theorem contextual_token_not_hard : hardStatementToken (.ident "revert") = false ∧
    hardStatementToken (.kw .return_) = true ∧ hardStatementToken (.punct .lbrace) = true := by
  decide +kernel

#print axioms empty_string_still_has_token
#print axioms empty_fragment_choice_refused
#print axioms zero_fragment_first_token_safe
#print axioms arbitrary_simple_vs_return
#print axioms raw_pair_successful_yields
#print axioms raw_pair_successful_toks
#print axioms raw_pair_different_roots
#print axioms raw_pair_contract_boundary
#print axioms raw_pair_parser_selects_simple
#print axioms raw_pair_classified
#print axioms contextual_token_not_hard
end Solidity.Frontend.StatementGrammarH28
