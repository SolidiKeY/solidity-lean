import Solidity.Frontend.StatementGrammarH28.RootContract
import Solidity.Frontend.StatementGrammarH28.LeafCoverage
import Solidity.Source.Ctor
import Solidity.Frontend.Checked.Lexer

/-! An inhabited ASCII declaration counterexample to intrinsic-profile parser
completeness. Both checked parser and solc refuse the contextual prefix; this
is not a claim of solc-accepted source rejection or expression uniqueness. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def contextualDeclStmt : Syn (.stmt .body) :=
  .simpleStmt (.declVar (.varDecl (.userType ⟨"revert", []⟩) .none "E") .none)

def contextualDeclTokens : List Tok := [.ident "revert", .ident "E", .punct .semi]

def contextualDeclInput (a b c d e f : Nat) (s : St) : St :=
  { s with ts := atToken (.ident "revert") a b :: atToken (.ident "E") c d ::
    atToken (.punct .semi) e f :: s.ts }

theorem contextual_decl_successful_yield :
    contextualDeclStmt.toks [] = some contextualDeclTokens := by decide +kernel

theorem contextual_decl_existing_guards :
    contextualDeclStmt.prec = true ∧ contextualDeclStmt.InProfile := by decide +kernel

theorem contextual_decl_ascii_lexer :
    (tokens (ascii "revert E;")).map (fun ts => ts.map Located.tok) =
      .ok contextualDeclTokens := by rfl

/-- Exact positive-fuel refusal, at arbitrary token locations and suffixes.
The parser chooses contextual revert, then requires its call parentheses. -/
theorem contextual_decl_refused (n : Nat) (k : SCtx) (a b c d e f : Nat) (s : St) :
    stmt (n + 2) k (contextualDeclInput a b c d e f s) = .error ⟨e, "expected '('"⟩ := by
  rfl

theorem contextual_decl_no_success (fuel : Nat) (k : SCtx) (a b c d e f : Nat) (s out : St)
    (tree : Syn (.stmt k)) :
    stmt fuel k (contextualDeclInput a b c d e f s) ≠ .ok (tree, out) := by
  intro h
  cases fuel with
  | zero => cases h
  | succ n =>
    cases n with
    | zero => cases h
    | succ n => rw [contextual_decl_refused] at h; cases h

theorem contextual_decl_not_complete :
    ¬ ∃ fuel, stmt fuel .body (contextualDeclInput 0 6 7 8 8 9 ⟨[], [], 9⟩) =
      .ok (contextualDeclStmt, ⟨[], [], 9⟩) := by
  intro ⟨fuel, h⟩
  exact contextual_decl_no_success fuel .body 0 6 7 8 8 9 _ _ contextualDeclStmt h

#print axioms contextual_decl_successful_yield
#print axioms contextual_decl_existing_guards
#print axioms contextual_decl_ascii_lexer
#print axioms contextual_decl_refused
#print axioms contextual_decl_no_success
#print axioms contextual_decl_not_complete
end Solidity.Frontend.StatementGrammarH28
