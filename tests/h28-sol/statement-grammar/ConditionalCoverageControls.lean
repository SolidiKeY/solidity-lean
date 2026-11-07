import Solidity.Frontend.StatementGrammarH28.ConditionalYield

/-! Inhabited six-constructor controls, universal depth/fuel/suffix controls,
and the actual dangling-else collision outside the unchanged contract. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def closedBlock (k : SCtx) : Syn (.stmt k) := .blockStmt (.block .nil)

def ifWords (b : Bool) (ts : List Tok) : List Tok :=
  [.kw .if_, .punct .lparen, .bool b, .punct .rparen] ++ ts

theorem closed_block_relation (k : SCtx) :
    BooleanStatements (closedBlock k) (braces []) 0 := .loops (.block .nil)

def ifTower (k : SCtx) : Nat → Syn (.stmt k)
  | 0 => closedBlock k
  | n + 1 => .ifStmt (.lit (.bool true)) (ifTower k n) .none

def ifTowerTokens : Nat → List Tok
  | 0 => braces []
  | n + 1 => ifWords true (ifTowerTokens n)

theorem if_tower_relation (k : SCtx) (n : Nat) :
    BooleanStatements (ifTower k n) (ifTowerTokens n) n := by
  induction n with
  | zero => exact closed_block_relation k
  | succ n ih => exact .ifNone ih

theorem arbitrary_if_depth_coverage (k : SCtx) (n extra : Nat) (s : St)
    (he : NoFollowingElse s) :
    stmt (extra + n + 6) k (locatedInput (ifTowerTokens n) s) = .ok (ifTower k n, s) :=
  boolean_statements_coverage (if_tower_relation k n) extra s (Or.inr he)

def matchedInner : Syn (.stmt ⟨true, false⟩) :=
  .ifStmt (.lit (.bool false)) (closedBlock ⟨true, false⟩) (.some (closedBlock ⟨true, false⟩))

def innerTokens : List Tok := ifWords false (braces []) ++ [.kw .else_] ++ braces []

theorem matched_inner_relation : BooleanStatements matchedInner innerTokens 1 :=
  .ifSome (closed_block_relation _) (closed_block_relation _) rfl

def properTree : Syn (.stmt .body) :=
  .ifStmt (.lit (.bool true)) (.whileStmt (.lit (.bool false)) matchedInner) .none

def properTokens : List Tok :=
  ifWords true ([.kw .while_, .punct .lparen, .bool false, .punct .rparen] ++ innerTokens)

theorem nearest_tree_relation : BooleanStatements properTree properTokens 3 :=
  .ifNone (.whileLoop matched_inner_relation)

theorem nearest_tree_coverage (n : Nat) (s : St) (he : NoFollowingElse s) :
    stmt (n + 9) .body (locatedInput properTokens s) = .ok (properTree, s) :=
  boolean_statements_coverage nearest_tree_relation n s (Or.inr he)

def wrongTree : Syn (.stmt .body) :=
  .ifStmt (.lit (.bool true))
    (.whileStmt (.lit (.bool false))
      (.ifStmt (.lit (.bool false)) (closedBlock ⟨true, false⟩) .none))
    (.some (closedBlock .body))

theorem dangling_else_same_actual_tokens : properTree.toks [] = wrongTree.toks [] := by
  rfl

theorem wrong_association_refused_by_contract : wrongTree.precNode = false := by rfl

theorem wrong_association_not_in_fragment (ts : List Tok) (d : Nat) :
    ¬ BooleanStatements wrongTree ts d := by
  intro h
  have bad : wrongTree.precNode = true := boolean_statements_node h
  cases bad

theorem nearest_actual_tree_unique {x : Syn (.stmt .body)} {ts : List Tok} {d : Nat}
    (h : BooleanStatements x ts d) (hx : x.Derives properTokens) : x = properTree :=
  boolean_statements_yield_unique h nearest_tree_relation hx
    ((boolean_statements_derives_iff nearest_tree_relation properTokens).mpr rfl)

def doOpen : Syn (.stmt .body) :=
  .doWhile (.ifStmt (.lit (.bool true)) (closedBlock ⟨true, false⟩) .none) (.lit (.bool false))

def doOpenTokens : List Tok := [.kw .do_] ++ ifWords true (braces []) ++
  [.kw .while_, .punct .lparen, .bool false, .punct .rparen, .punct .semi]

theorem do_closes_open_relation : BooleanStatements doOpen doOpenTokens 2 :=
  .doLoop (.ifNone (closed_block_relation _))

theorem do_open_arbitrary_suffix (n : Nat) (s : St) :
    stmt (n + 8) .body (locatedInput doOpenTokens s) = .ok (doOpen, s) :=
  boolean_statements_coverage do_closes_open_relation n s (Or.inl rfl)

theorem do_open_else_suffix_preserved (n : Nat) (s : St) :
    stmt (n + 8) .body (locatedInput doOpenTokens (locatedInput [.kw .else_] s)) =
      .ok (doOpen, locatedInput [.kw .else_] s) := do_open_arbitrary_suffix n _

def forWhileIf : Syn (.stmt .body) :=
  .forStmt .none .none .none (.whileStmt (.lit (.bool true)) matchedInner)

def forWhileTokens : List Tok :=
  [.kw .for_, .punct .lparen, .punct .semi, .punct .semi, .punct .rparen] ++
  [.kw .while_, .punct .lparen, .bool true, .punct .rparen] ++ innerTokens

theorem for_while_relation : BooleanStatements forWhileIf forWhileTokens 3 :=
  .forLoop (.whileLoop matched_inner_relation)

theorem for_while_arbitrary_suffix (n : Nat) (s : St) :
    stmt (n + 9) .body (locatedInput forWhileTokens s) = .ok (forWhileIf, s) :=
  boolean_statements_coverage for_while_relation n s (Or.inl rfl)

theorem else_open_relation (k : SCtx) (b : Bool) :
    BooleanStatements (.ifStmt (.lit (.bool b)) (closedBlock k) (.some (ifTower k 1)))
      (ifWords b (braces []) ++ [.kw .else_] ++ ifTowerTokens 1) 2 :=
  .ifSome (closed_block_relation _) (if_tower_relation _ 1) rfl

theorem open_suffix_captures_else :
    stmt 12 .body (locatedInput (ifWords true (braces []))
      (locatedInput ([.kw .else_] ++ braces []) ⟨[], [], 0⟩)) =
      .ok (.ifStmt (.lit (.bool true)) (closedBlock .body) (.some (closedBlock .body)), ⟨[], [], 0⟩) := by
  rfl

theorem do_open_prefix_unique {x : Syn (.stmt .body)} {ts rest tail : List Tok} {d : Nat}
    (h : BooleanStatements x ts d) (s : St) (frame : StatementFrame x (locatedInput tail s))
    (he : doOpenTokens ++ rest = ts ++ tail) : doOpen = x ∧ rest = tail :=
  boolean_statements_prefix_unique do_closes_open_relation h s (Or.inl rfl) frame he

#print axioms do_open_prefix_unique
#print axioms closed_block_relation
#print axioms if_tower_relation
#print axioms arbitrary_if_depth_coverage
#print axioms matched_inner_relation
#print axioms nearest_tree_relation
#print axioms nearest_tree_coverage
#print axioms dangling_else_same_actual_tokens
#print axioms wrong_association_refused_by_contract
#print axioms wrong_association_not_in_fragment
#print axioms nearest_actual_tree_unique
#print axioms do_closes_open_relation
#print axioms do_open_arbitrary_suffix
#print axioms do_open_else_suffix_preserved
#print axioms for_while_relation
#print axioms for_while_arbitrary_suffix
#print axioms else_open_relation
#print axioms open_suffix_captures_else
end Solidity.Frontend.StatementGrammarH28
