import Solidity.Frontend.StatementGrammarH28.NearestElse
import Solidity.Frontend.Checked.Print

/-! Inhabited positive/negative dangling-else controls. No parser completeness claim. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def danglingOuter : Syn (.stmt .body) :=
  .ifStmt (.ident "p") (.ifStmt (.ident "q") (.returnStmt .none) .none)
    (.some (.returnStmt .none))

def danglingInner : Syn (.stmt .body) :=
  .ifStmt (.ident "p") (.ifStmt (.ident "q") (.returnStmt .none)
    (.some (.returnStmt .none))) .none

def danglingTokens : List Tok :=
  [.kw .if_, .punct .lparen, .ident "p", .punct .rparen,
   .kw .if_, .punct .lparen, .ident "q", .punct .rparen,
   .kw .return_, .punct .semi, .kw .else_, .kw .return_, .punct .semi]

theorem dangling_successful_yield :
    danglingOuter.toks [] = some danglingTokens ∧
    danglingInner.toks [] = some danglingTokens := by decide

/-- Raw yields alone are ambiguous; the existing precedence contract matters. -/
theorem dangling_same_yield : danglingOuter.toks [] = danglingInner.toks [] := by decide

theorem dangling_different : danglingOuter ≠ danglingInner := by
  intro h
  cases h

theorem dangling_outer_refused : danglingOuter.prec = false := by decide

theorem dangling_inner_allowed : danglingInner.prec = true := by decide

example {k : SCtx} (c : Syn .expr) (s : Syn (.stmt k)) :
    OpenSpine (.ifStmt c s .none) := .missing c s

example {k : SCtx} (c : Syn .expr) (s t : Syn (.stmt k)) :
    OpenSpine (.ifStmt c s (.some (.ifStmt c t .none))) :=
  .elseBranch _ _ _ (.missing _ _)

example {l u : Bool} (c : Syn .expr) (s : Syn (.stmt ⟨true, u⟩)) :
    OpenSpine (.whileStmt (l := l) c (.ifStmt c s .none)) :=
  .whileBody _ _ (.missing _ _)

example {l u : Bool} (c : Syn .expr) (s : Syn (.stmt ⟨true, u⟩)) :
    OpenSpine (.forStmt (l := l) .none .none .none (.ifStmt c s .none)) :=
  .forBody _ _ _ _ (.missing _ _)

example {l u : Bool} (c : Syn .expr) (s : Syn (.stmt ⟨true, u⟩)) :
    ¬ OpenSpine (.doWhile (l := l) (.ifStmt c s .none) c) := doWhile_closed _ _

example {k : SCtx} (c : Syn .expr) (s : Syn (.stmt k)) :
    ¬ OpenSpine (.blockStmt (.block (.cons (.stmtItem (.ifStmt c s .none)) .nil))) :=
  block_closed _

#print axioms dangling_successful_yield
#print axioms dangling_same_yield
#print axioms dangling_different
#print axioms dangling_outer_refused
#print axioms dangling_inner_allowed
end Solidity.Frontend.StatementGrammarH28
