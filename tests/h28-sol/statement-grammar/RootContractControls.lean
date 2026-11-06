import Solidity.Frontend.StatementGrammarH28.RootContract
import Solidity.Frontend.StatementGrammarH28.ContextualDeclCounterexample

/-! Inhabited contract-level root controls and the distinct parser-completeness
counterexample. The theorem concludes root equality, not full tree equality. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def validRevertStmt : Syn (.stmt .body) := .revert (.ident "E") (.positional .nil)
def validRevertWords : List Tok :=
  [.ident "revert", .ident "E", .punct .lparen, .punct .rparen, .punct .semi]
def qualifiedRevertStmt : Syn (.stmt .body) :=
  .revert (.member (.ident "E") "Err") (.positional .nil)
def qualifiedRevertWords : List Tok :=
  [.ident "revert", .ident "E", .punct .period, .ident "Err", .punct .lparen, .punct .rparen, .punct .semi]
def namedRevertStmt : Syn (.stmt .body) :=
  .revert (.ident "E") (.named (.cons (.namedArg "x" (.lit (.bool true))) .nil))
def namedRevertWords : List Tok :=
  [.ident "revert", .ident "E", .punct .lparen, .punct .lbrace, .ident "x", .punct .colon,
   .bool true, .punct .rbrace, .punct .rparen, .punct .semi]

theorem contract_revert_positive_yields :
    validRevertStmt.yield [] = some ([validRevertWords], []) ∧
    qualifiedRevertStmt.yield [] = some ([qualifiedRevertWords], []) ∧
    namedRevertStmt.yield [] = some ([namedRevertWords], []) := by decide +kernel

theorem contract_revert_precedence : validRevertStmt.prec = true ∧
    qualifiedRevertStmt.prec = true ∧ namedRevertStmt.prec = true := by decide +kernel

theorem contextual_decl_layout_yield (L : List Choice) :
    contextualDeclStmt.yield L = some ([contextualDeclTokens], L) := by rfl

theorem real_third_token_discriminator (tail : List Tok) :
    badStmtTriple (contextualDeclTokens ++ tail) = false ∧
    badStmtTriple (validRevertWords ++ tail) = true ∧
    badStmtTriple (qualifiedRevertWords ++ tail) = true := by
  exact ⟨rfl, rfl, rfl⟩

theorem every_simple_distinct_from_valid_revert {k : SCtx} (s : Syn .simple)
    (L M : List Choice) (parts : List (List Tok)) (rest tail : List Tok)
    (hs : (Syn.simpleStmt (k := k) s).yield L = some (parts, M)) :
    parts.flatten ++ rest ≠ validRevertWords ++ tail :=
  simple_revert_prefix_distinct s (.ident "E") (.positional .nil) rfl L M [] []
    parts [validRevertWords] rest tail hs contract_revert_positive_yields.1

/-- Any precedence-valid candidate with a matching actual token prefix has
the revert root; the positive witness itself inhabits this premise. -/
theorem matching_valid_revert_root {k : SCtx} (s : Syn (.stmt k)) (hp : s.prec = true)
    (L M : List Choice) (parts : List (List Tok)) (rest tail : List Tok)
    (hs : s.yield L = some (parts, M))
    (he : parts.flatten ++ rest = validRevertWords ++ tail) : root s = .revertError :=
  statement_root_unique s validRevertStmt hp contract_revert_precedence.1 L M [] []
    parts [validRevertWords] rest tail hs contract_revert_positive_yields.1 he

/-- An identifier/colon prefix belongs to named-argument syntax, so the atom
pair invariant must not silently be generalized to that category. -/
theorem named_argument_outside_atom_pair_claim :
    (Syn.namedArg "x" (.ident "y")).yield [] =
      some ([[.ident "x", .punct .colon, .ident "y"]], []) ∧
    badAtomPair [.ident "x", .punct .colon, .ident "y"] = true := by decide +kernel

theorem arbitrary_expression_cannot_yield_bad_pair (e : Syn .expr) (L M : List Choice)
    (parts : List (List Tok)) (a b : String) (tail : List Tok)
    (he : parts.flatten = .ident a :: .ident b :: tail) : e.yield L ≠ some (parts, M) := by
  intro hy
  have hs := expression_pair_safe e L parts M hy
  change badAtomPair parts.flatten = false at hs
  rw [he] at hs
  cases hs

#print axioms contract_revert_positive_yields
#print axioms contract_revert_precedence
#print axioms contextual_decl_layout_yield
#print axioms real_third_token_discriminator
#print axioms every_simple_distinct_from_valid_revert
#print axioms matching_valid_revert_root
#print axioms named_argument_outside_atom_pair_claim
#print axioms arbitrary_expression_cannot_yield_bad_pair
end Solidity.Frontend.StatementGrammarH28
