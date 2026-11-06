import Solidity.Frontend.StatementGrammarH28.BoolCompound

/-! Inhabited positive/negative compound and necessary else-boundary controls. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def compoundLoopItems : Syn (.list (.item ⟨true, false⟩)) :=
  .cons (.stmtItem .breakStmt) (.cons (.stmtItem .continueStmt)
    (.cons (.stmtItem (.blockStmt (.block (.cons (.stmtItem (.returnStmt .none)) .nil)))) .nil))

def compoundLoopTokens : List Tok :=
  [.kw .break_, .punct .semi, .kw .continue_, .punct .semi] ++
    braces [.kw .return_, .punct .semi]

theorem compound_loop_relation : NestedItems compoundLoopItems compoundLoopTokens 3 :=
  .breakCons (.continueCons (.blockCons (.returnCons .nil) .nil))

theorem while_recursive_control (n : Nat) (b : Bool) (s : St) :
    stmt (n + 9) .body (conditionInput .while_ b (blockInput compoundLoopTokens s)) =
      .ok (.whileStmt (.lit (.bool b)) (.blockStmt (.block compoundLoopItems)), s) :=
  while_bool_block_coverage compound_loop_relation n b s

theorem do_recursive_control (n : Nat) (b : Bool) (s : St) :
    stmt (n + 9) .body (doInput compoundLoopTokens b s) =
      .ok (.doWhile (.blockStmt (.block compoundLoopItems)) (.lit (.bool b)), s) :=
  do_bool_block_coverage compound_loop_relation n b s

theorem for_recursive_control (n : Nat) (s : St) :
    stmt (n + 9) .body (forEmptyInput (blockInput compoundLoopTokens s)) =
      .ok (.forStmt .none .none .none (.blockStmt (.block compoundLoopItems)), s) :=
  for_empty_block_coverage compound_loop_relation n s

theorem if_none_close_boundary (n : Nat) (b : Bool) (s : St) :
    stmt (n + 6) .body (conditionInput .if_ b (blockInput [] (endState s))) =
      .ok (.ifStmt (.lit (.bool b)) (.blockStmt (.block .nil)) .none, endState s) :=
  if_bool_block_none_coverage .nil n b (endState s) (by intro h; cases h)

theorem if_some_both_booleans (n : Nat) (b : Bool) (s : St) :
    stmt (n + 6) .body (conditionInput .if_ b (blockInput [] (elseInput [] s))) =
      .ok (.ifStmt (.lit (.bool b)) (.blockStmt (.block .nil))
        (.some (.blockStmt (.block .nil))), s) :=
  if_bool_blocks_some_coverage .nil .nil n b s

/-- Omitting the no-else boundary would make no-else coverage false: the
existing parser consumes this else and builds the some alternative. -/
theorem following_else_captured (s : St) :
    stmt 6 .body (conditionInput .if_ true (blockInput [] (elseInput [] s))) =
      .ok (.ifStmt (.lit (.bool true)) (.blockStmt (.block .nil))
        (.some (.blockStmt (.block .nil))), s) := if_some_both_booleans 0 true s

theorem no_else_without_boundary_false (s : St) :
    stmt 6 .body (conditionInput .if_ true (blockInput [] (elseInput [] s))) ≠
      .ok (.ifStmt (.lit (.bool true)) (.blockStmt (.block .nil)) .none, elseInput [] s) := by
  rw [following_else_captured]
  intro h
  cases h

theorem following_else_not_closed (s : St) : ¬ NoFollowingElse (elseInput [] s) := by
  intro h
  exact h rfl

theorem unchecked_loop_context (n : Nat) (b : Bool) (s : St) :
    stmt (n + 6) ⟨false, true⟩ (conditionInput .while_ b (blockInput [] s)) =
      .ok (.whileStmt (.lit (.bool b)) (.blockStmt (.block .nil)), s) :=
  while_bool_block_coverage .nil n b s

def compoundSuffix : St := ⟨[atToken (.kw .else_) 8 12], [.frags [2]], 19⟩

theorem while_nonempty_suffix_layout (b : Bool) :
    stmt 9 .body (conditionInput .while_ b (blockInput compoundLoopTokens compoundSuffix)) =
      .ok (.whileStmt (.lit (.bool b)) (.blockStmt (.block compoundLoopItems)), compoundSuffix) :=
  while_recursive_control 0 b compoundSuffix

theorem while_actual_yield (b : Bool) (L : List Choice) :
    (Syn.whileStmt (l := false) (.lit (.bool b)) (.blockStmt (.block compoundLoopItems))).yield L =
      some ([tk .while_ ++ parens [.bool b] ++ braces compoundLoopTokens], L) :=
  while_bool_block_yield compound_loop_relation b L

theorem if_some_actual_yield (b : Bool) (L : List Choice) :
    (Syn.ifStmt (k := .body) (.lit (.bool b)) (.blockStmt (.block .nil))
      (.some (.blockStmt (.block .nil)))).yield L =
      some ([tk .if_ ++ parens [.bool b] ++ braces [] ++ tk .else_ ++ braces []], L) :=
  if_bool_blocks_some_yield .nil .nil b L

#print axioms compound_loop_relation
#print axioms while_recursive_control
#print axioms do_recursive_control
#print axioms for_recursive_control
#print axioms if_none_close_boundary
#print axioms if_some_both_booleans
#print axioms following_else_captured
#print axioms no_else_without_boundary_false
#print axioms following_else_not_closed
#print axioms unchecked_loop_context
#print axioms while_nonempty_suffix_layout
#print axioms while_actual_yield
#print axioms if_some_actual_yield
end Solidity.Frontend.StatementGrammarH28
