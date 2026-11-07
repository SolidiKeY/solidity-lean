import Solidity.Frontend.StatementGrammarH28.AtomYield

/-! Inhabited controls for every AtomStatements constructor, identifier atoms
in every condition position, the dangling-else association with identifier
conditions, and negative controls for the exposed atom premise and the
precedence contract. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def emptyBlock (k : SCtx) : Syn (.stmt k) := .blockStmt (.block .nil)

theorem empty_block_atom (k : SCtx) : AtomStatements (emptyBlock k) (braces []) 0 :=
  .boolean (.loops (.block .nil))

/-- `if (x) if (y) {} else {}`: the else belongs to the inner if. -/
def identInner : Syn (.stmt .body) :=
  .ifStmt (.ident "y") (emptyBlock .body) (.some (emptyBlock .body))

def identNearest : Syn (.stmt .body) := .ifStmt (.ident "x") identInner .none

def identWrong : Syn (.stmt .body) :=
  .ifStmt (.ident "x") (.ifStmt (.ident "y") (emptyBlock .body) .none) (.some (emptyBlock .body))

def identTokens : List Tok :=
  [.kw .if_, .punct .lparen, .ident "x", .punct .rparen,
   .kw .if_, .punct .lparen, .ident "y", .punct .rparen] ++ braces [] ++ [.kw .else_] ++ braces []

theorem ident_inner_relation :
    AtomStatements identInner
      ([.kw .if_, .punct .lparen] ++ [.ident "y"] ++ [.punct .rparen] ++ braces [] ++
        [.kw .else_] ++ braces []) 6 :=
  .ifSome (ident_atom_rparen "y") (empty_block_atom _) (empty_block_atom _) rfl

theorem ident_nearest_relation : AtomStatements identNearest identTokens 12 :=
  .ifNone (ident_atom_rparen "x") ident_inner_relation

theorem ident_nearest_coverage (n : Nat) (s : St) (he : NoFollowingElse s) :
    stmt (n + 18) .body (locatedInput identTokens s) = .ok (identNearest, s) :=
  atom_statements_coverage ident_nearest_relation n s (Or.inr he)

theorem ident_nearest_actual_parse :
    stmt 18 .body (locatedInput identTokens ⟨[], [], 0⟩) = .ok (identNearest, ⟨[], [], 0⟩) := by
  rfl

theorem ident_wrong_refused_by_contract : identWrong.precNode = false := by rfl

theorem ident_wrong_not_in_fragment (ts : List Tok) (d : Nat) :
    ¬ AtomStatements identWrong ts d := by
  intro h
  have bad : identWrong.precNode = true := atom_statements_node h
  cases bad

theorem ident_nearest_unique {x : Syn (.stmt .body)} {d : Nat}
    (h : AtomStatements x identTokens d) : x = identNearest :=
  atom_statements_token_unique h ident_nearest_relation rfl

/-- `while (x) for (;;) do {} while (y);` with arbitrary suffix. -/
def loopTree : Syn (.stmt .body) :=
  .whileStmt (.ident "x")
    (.forStmt .none .none .none (.doWhile (emptyBlock ⟨true, false⟩) (.ident "y")))

def loopTokens : List Tok :=
  [.kw .while_, .punct .lparen] ++ [.ident "x"] ++ [.punct .rparen] ++
  ([.kw .for_, .punct .lparen, .punct .semi, .punct .semi, .punct .rparen] ++
   ([.kw .do_] ++ braces [] ++ [.kw .while_, .punct .lparen] ++ [.ident "y"] ++
     [.punct .rparen, .punct .semi]))

theorem loop_relation : AtomStatements loopTree loopTokens 13 :=
  .whileLoop (ident_atom_rparen "x") (.forLoop (.doLoop (ident_atom_rparen "y") (empty_block_atom _)))

theorem loop_arbitrary_suffix (n : Nat) (s : St) :
    stmt (n + 19) .body (locatedInput loopTokens s) = .ok (loopTree, s) :=
  atom_statements_coverage loop_relation n s (Or.inl rfl)

theorem loop_else_suffix_preserved (n : Nat) (s : St) :
    stmt (n + 19) .body (locatedInput loopTokens (locatedInput [.kw .else_] s)) =
      .ok (loopTree, locatedInput [.kw .else_] s) := loop_arbitrary_suffix n _

/-- Boolean witnesses embed unchanged. -/
theorem boolean_embeds (k : SCtx) :
    AtomStatements (.ifStmt (.lit (.bool true)) (emptyBlock k) .none)
      ([.kw .if_, .punct .lparen, .bool true, .punct .rparen] ++ braces []) 1 :=
  atom_statements_of_boolean (.ifNone (.loops (.block .nil)))

/-- Mixed atoms: a Boolean literal condition through the atom constructor. -/
theorem bool_atom_if (k : SCtx) :
    AtomStatements (.ifStmt (.lit (.bool false)) (emptyBlock k) .none)
      ([.kw .if_, .punct .lparen] ++ [.bool false] ++ [.punct .rparen] ++ braces []) 6 :=
  .ifNone (bool_atom_rparen false) (empty_block_atom k)

/-- Negative: the premise names the parsed expression, not an arbitrary one. -/
theorem atom_premise_names_parsed_expression : ¬ ExprAtomRparen (.ident "y") [.ident "x"] 5 := by
  intro h
  have bad := (ident_atom_rparen "x" 0 ⟨[], [], 0⟩).symm.trans (h 0 ⟨[], [], 0⟩)
  injection bad with bad
  injection bad with bad
  injection bad with bad
  exact absurd bad (by decide)

/-- Negative: a call head is not an atom before `)` with the identifier alone. -/
theorem atom_premise_refuses_extra_tokens :
    ¬ ExprAtomRparen (.ident "x") [.ident "x", .punct .lparen] 5 := by
  intro h
  have bad := congrArg (fun r => r.toOption.map (fun p => p.2.ts.length)) (h 0 ⟨[], [], 0⟩)
  revert bad
  decide +kernel

/-- Negative: zero budget is not enough at zero excess fuel. -/
theorem atom_premise_needs_budget : ¬ ExprAtomRparen (.ident "x") [.ident "x"] 0 := by
  intro h
  have bad := congrArg (fun r => r.toOption.map (fun p => p.2.ts.length)) (h 0 ⟨[], [], 0⟩)
  revert bad
  decide +kernel

/-- Printed tokens of the dangling-else tree, and yield uniqueness: any
fragment tree deriving the same words is the nearest-else tree. -/
theorem ident_nearest_yields : AtomYields identNearest identTokens :=
  .ifNone (ident_atom_yield "x")
    (.ifSome (ident_atom_yield "y") (.boolean (.loops (.block .nil)))
      (.boolean (.loops (.block .nil))))

theorem ident_nearest_derives : identNearest.Derives identTokens :=
  (atom_yields_derives_iff ident_nearest_yields identTokens).mpr rfl

theorem ident_nearest_yield_unique {x : Syn (.stmt .body)} {ts : List Tok} {d : Nat}
    (hx : AtomStatements x ts d) (px : AtomYields x ts) (dx : x.Derives identTokens) :
    x = identNearest :=
  atom_statements_yield_unique hx px ident_nearest_relation ident_nearest_yields dx
    ident_nearest_derives

/-- The wrong association prints the same tokens; it is excluded by the
precedence contract, not by the printer. -/
theorem ident_wrong_same_print : identWrong.toks [] = identNearest.toks [] := by rfl

/-- Negative: the printer premise names the printed tokens. -/
theorem atom_yield_names_tokens : ¬ AtomYield (.ident "x") [.ident "y"] := by
  intro h
  have bad := h []
  injection bad with bad
  injection bad with bad
  injection bad with bad
  injection bad with bad
  injection bad with bad
  exact absurd bad (by decide)

#print axioms ident_nearest_yields
#print axioms ident_nearest_derives
#print axioms ident_nearest_yield_unique
#print axioms ident_wrong_same_print
#print axioms atom_yield_names_tokens
#print axioms ident_nearest_coverage
#print axioms ident_nearest_actual_parse
#print axioms ident_wrong_not_in_fragment
#print axioms ident_nearest_unique
#print axioms loop_arbitrary_suffix
#print axioms boolean_embeds
#print axioms bool_atom_if
#print axioms atom_premise_names_parsed_expression
#print axioms atom_premise_refuses_extra_tokens
#print axioms atom_premise_needs_budget
end Solidity.Frontend.StatementGrammarH28
