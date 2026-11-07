import Solidity.Frontend.StatementGrammarH28.SyntaxBalance
import Solidity.Frontend.StatementGrammarH28.FlagCounterexample

/-! Inhabited actual-yield balance controls, invalid layouts and a retained
collision control. Token brace balance does not establish tree uniqueness. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def balanceItems : Syn (.list (.item .body)) :=
  .cons (.stmtItem (.simpleStmt (.declVar
    (.varDecl (.fnType .nil (.some .internal) (.some .view) .nil) .none "fp") .none)))
  (.cons (.stmtItem (.simpleStmt (.exprStmt
    (.callOptions (.ident "f") (.namedArg "gas" (.lit (.num (.dec 1 0 0)))) .nil))))
  (.cons (.stmtItem (.simpleStmt (.exprStmt (.lit (.str [123, 125])))))
  (.cons (.uncheckedItem (.block (.cons (.stmtItem (.returnStmt .none)) .nil))) .nil)))

def balanceLayout : List Choice := [.attrs [.vis, .mutab], .frags [2]]

def balanceParts : List (List Tok) :=
  [[.kw .function, .punct .lparen, .punct .rparen, .kw .internal, .kw .view, .ident "fp", .punct .semi],
   [.ident "f", .punct .lbrace, .ident "gas", .punct .colon, .num (.dec 1 0 0), .punct .rbrace, .punct .semi],
   [.str [123, 125], .punct .semi],
   [.kw .unchecked, .punct .lbrace, .kw .return_, .punct .semi, .punct .rbrace]]

theorem actual_balance_items_yield (tail : List Choice) :
    balanceItems.yield (balanceLayout ++ tail) = some (balanceParts, tail) := by
  rfl

theorem arbitrary_balance_control (tail : List Choice) : BalancedParts balanceParts :=
  syntax_yield_balanced balanceItems rfl (balanceLayout ++ tail) balanceParts tail
    (actual_balance_items_yield tail)

theorem actual_balance_block_boundary (tail : List Choice) :
    BlockBoundary (.block balanceItems) (balanceLayout ++ tail) tail balanceParts.flatten :=
  arbitrary_block_boundary balanceItems _ _ _ (actual_balance_items_yield tail)

theorem actual_balance_block_toks :
    (Syn.block balanceItems).toks balanceLayout = some (braces balanceParts.flatten) := by
  decide +kernel

theorem invalid_attrs_still_fail :
    balanceItems.yield [.attrs [.vis, .vis, .mutab], .frags [2]] = none := by
  decide +kernel

theorem invalid_fragments_still_fail :
    balanceItems.yield [.attrs [.vis, .mutab], .frags [1]] = none := by
  decide +kernel

/-- A closing-brace byte in a string token is neutral, including in an actual
successful statement yield. It is not a closing-brace punctuation token. -/
theorem string_payload_close_neutral :
    (Syn.simpleStmt (k := .body) (.exprStmt (.lit (.str [125])))).yield [.frags [1]] =
      some ([[.str [125], .punct .semi]], []) := by
  decide +kernel

theorem arbitrary_statement_cannot_yield_unmatched_close {k : SCtx} (s : Syn (.stmt k))
    (L M : List Choice) (parts : List (List Tok)) (hc : parts.flatten = [.punct .rbrace]) :
    s.yield L ≠ some (parts, M) := by
  intro hs
  have hb := balancedParts_flat (statement_yield_balanced s L parts M hs)
  rw [hc] at hb
  exact unmatched_close_not_balanced hb

/-- The pre-existing distinct-tree collision still has balanced tokens.
The new boundary theorem must not be read as syntax/yield injectivity. -/
theorem flag_collision_remains_balanced : BraceBalanced flagTokens ∧
    flagStmtASCII ≠ flagStmtUnicode ∧
    flagStmtASCII.toks [] = some flagTokens ∧ flagStmtUnicode.toks [] = some flagTokens := by
  have hy : flagStmtASCII.yield [] = some ([flagTokens], []) := by decide +kernel
  have hb : BalancedParts [flagTokens] := statement_yield_balanced flagStmtASCII [] _ [] hy
  exact ⟨hb flagTokens (.head _), flag_statements_distinct,
    flag_successful_common_yield.1, flag_successful_common_yield.2⟩

#print axioms actual_balance_items_yield
#print axioms arbitrary_balance_control
#print axioms actual_balance_block_boundary
#print axioms actual_balance_block_toks
#print axioms invalid_attrs_still_fail
#print axioms invalid_fragments_still_fail
#print axioms string_payload_close_neutral
#print axioms arbitrary_statement_cannot_yield_unmatched_close
#print axioms flag_collision_remains_balanced
end Solidity.Frontend.StatementGrammarH28
