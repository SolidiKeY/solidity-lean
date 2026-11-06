import Solidity.Frontend.StatementGrammarH28.ElsePosition

/-! Inhabited position controls. Tokens and source parsing remain separate. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source

def twoMissing : Syn (.stmt .body) :=
  .ifStmt (.ident "p") (.ifStmt (.ident "q") (.returnStmt .none) .none) .none

theorem twoMissing_nearest : NearestSlot twoMissing [.thenBranch] :=
  .thenBranch _ _ (.root _ _ rfl)

theorem twoMissing_outer_not_nearest : ¬ NearestSlot twoMissing [] := by
  intro h
  have bad : ([] : List ElseEdge) = [.thenBranch] := nearestSlot_unique h twoMissing_nearest
  cases bad

/-- Closing the inner if with else exposes the outer missing-else slot. -/
theorem inner_closed_outer_exposed :
    NearestSlot (.ifStmt (k := .body) (.ident "p")
      (.ifStmt (.ident "q") (.returnStmt .none) (.some (.returnStmt .none))) .none) [] :=
  .root _ _ rfl

/-- An existing else takes the exposed path through its else branch. -/
theorem else_branch_position :
    NearestSlot (.ifStmt (k := .body) (.ident "p") (.returnStmt .none)
      (.some (.ifStmt (.ident "q") (.returnStmt .none) .none))) [.elseBranch] :=
  .elseBranch _ _ _ (.root _ _ rfl)

theorem loop_position :
    NearestSlot (.forStmt (l := false) (u := false) .none .none .none
      (.whileStmt (.ident "p")
        (.ifStmt (.ident "q") (.ifStmt (.ident "r") (.breakStmt) .none) .none)))
      [.forBody, .whileBody, .thenBranch] :=
  .forBody _ _ _ _ (.whileBody _ _ (.thenBranch _ _ (.root _ _ rfl)))

theorem block_hides_position {k : SCtx} (b : Syn (.block k)) (p : List ElseEdge) :
    ¬ NearestSlot (.blockStmt b) p := by
  intro hp
  have bad : false = true := hp.isOpen
  cases bad

theorem doWhile_hides_position {l u : Bool} (b : Syn (.stmt ⟨true, u⟩))
    (c : Syn .expr) (p : List ElseEdge) :
    ¬ NearestSlot (.doWhile (l := l) b c) p := by
  intro hp
  have bad : false = true := hp.isOpen
  cases bad

/-- The wrong outer attachment fails the existing precedence contract. -/
theorem attachment_over_open_then_refused :
    (Syn.ifStmt (k := .body) (.ident "p")
      (.ifStmt (.ident "q") (.returnStmt .none) .none)
      (.some (.returnStmt .none))).prec = false := by decide +kernel

#print axioms twoMissing_nearest
#print axioms twoMissing_outer_not_nearest
#print axioms inner_closed_outer_exposed
#print axioms else_branch_position
#print axioms loop_position
#print axioms block_hides_position
#print axioms doWhile_hides_position
#print axioms attachment_over_open_then_refused
end Solidity.Frontend.StatementGrammarH28
