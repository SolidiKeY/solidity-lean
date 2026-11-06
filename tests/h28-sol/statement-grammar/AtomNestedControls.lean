import Solidity.Frontend.StatementGrammarH28.AtomNested
import Solidity.Frontend.StatementGrammarH28.G0Nodes

/-! Inhabited controls for every AtomStmt and AtomItems constructor, nested
blocks, unchecked items, `return e;`, arbitrary width and depth, the
dangling-else association inside blocks, and negative controls. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

/-- The loop body `{ if (y) break; else continue; }`. -/
def loopBody : Syn (.stmt ⟨true, false⟩) :=
  .blockStmt (.block (.cons (.stmtItem (.ifStmt (.ident "y") .breakStmt (.some .continueStmt))) .nil))

def loopBodyParts : List (List Tok) :=
  [[.kw .if_, .punct .lparen] ++ [.ident "y"] ++ [.punct .rparen] ++
    [.kw .break_, .punct .semi] ++ [.kw .else_] ++ [.kw .continue_, .punct .semi]]

theorem loop_body_relation : AtomStmt loopBody (braces loopBodyParts.flatten) 13 :=
  .block (.stmtCons (.ifSome (ident_atom_rparen "y") .breakStmt .continueStmt rfl) .nil)

/-- The items of `{ while (x) { if (y) break; else continue; } return z; unchecked { return; } }`. -/
def outerItems : Syn (.list (.item .body)) :=
  .cons (.stmtItem (.whileStmt (.ident "x") loopBody))
    (.cons (.stmtItem (.returnStmt (.some (.ident "z"))))
      (.cons (.uncheckedItem (.block (.cons (.stmtItem (.returnStmt .none)) .nil))) .nil))

def outerParts : List (List Tok) :=
  [[.kw .while_, .punct .lparen] ++ [.ident "x"] ++ [.punct .rparen] ++ braces loopBodyParts.flatten,
   [.kw .return_] ++ [.ident "z"] ++ [.punct .semi],
   .kw .unchecked :: braces [[.kw .return_, .punct .semi]].flatten]

theorem outer_relation : AtomItems outerItems outerParts 26 :=
  .stmtCons (.whileLoop (ident_atom_rparen "x") loop_body_relation)
    (.stmtCons (.returnSome (ident_atom_semi "z") ⟨(by intro h; cases h), (by intro h; cases h)⟩)
      (.uncheckedCons (.stmtCons .returnNone .nil) .nil))

theorem outer_block_coverage (n : Nat) (s : St) :
    stmt (n + 26 + 6) .body (locatedInput (braces outerParts.flatten) s) =
      .ok (.blockStmt (.block outerItems), s) :=
  atom_stmt_coverage (.block outer_relation) n s (Or.inl rfl) (Or.inl rfl)

/-- An instance of the universal coverage theorem at zero excess fuel. -/
theorem outer_block_at_fuel_32 :
    stmt 32 .body (locatedInput (braces outerParts.flatten) ⟨[], [], 0⟩) =
      .ok (.blockStmt (.block outerItems), ⟨[], [], 0⟩) :=
  outer_block_coverage 0 ⟨[], [], 0⟩

theorem outer_block_unique {x : Syn (.stmt .body)} {d : Nat}
    (h : AtomStmt x (braces outerParts.flatten) d) : x = .blockStmt (.block outerItems) :=
  atom_stmt_token_unique h (.block outer_relation) rfl

/-- Arbitrary width: `n` copies of `return x;` in one block, constant budget. -/
def returnItems (k : SCtx) : Nat → Syn (.list (.item k))
  | 0 => .nil
  | n + 1 => .cons (.stmtItem (.returnStmt (.some (.ident "x")))) (returnItems k n)

def returnParts : Nat → List (List Tok)
  | 0 => []
  | n + 1 => ([.kw .return_] ++ [.ident "x"] ++ [.punct .semi]) :: returnParts n

theorem return_items_relation (k : SCtx) (n : Nat) :
    AtomItems (returnItems k n) (returnParts n) (if n = 0 then 0 else 13) := by
  induction n with
  | zero => exact .nil
  | succ n ih =>
    have h := AtomItems.stmtCons
      (AtomStmt.returnSome (k := k) (ident_atom_semi "x") ⟨(by intro h; cases h), (by intro h; cases h)⟩) ih
    cases n with
    | zero => exact h
    | succ n => exact h

theorem arbitrary_width_block (k : SCtx) (w n : Nat) (s : St) :
    block (n + 14) k (blockInput (returnParts w).flatten s) = .ok (.block (returnItems k w), s) := by
  have h := atom_items_block_coverage (return_items_relation k w) (n + 13 - (if w = 0 then 0 else 13)) s
  have hf : n + 13 - (if w = 0 then 0 else 13) + (if w = 0 then 0 else 13) + 1 = n + 14 := by
    split <;> omega
  rw [hf] at h
  exact h

/-- Arbitrary depth: `if (x) { … }` nested `n` times. -/
def ifDepth : Nat → Syn (.stmt .body)
  | 0 => .blockStmt (.block .nil)
  | n + 1 => .ifStmt (.ident "x") (.blockStmt (.block (.cons (.stmtItem (ifDepth n)) .nil))) .none

def ifDepthTokens : Nat → List Tok
  | 0 => braces []
  | n + 1 => [.kw .if_, .punct .lparen] ++ [.ident "x"] ++ [.punct .rparen] ++
      braces [ifDepthTokens n].flatten

def ifDepthBudget : Nat → Nat
  | 0 => 0
  | n + 1 => max (ifDepthBudget n + 7) 0 + 5 + 1

theorem if_depth_relation (n : Nat) : AtomStmt (ifDepth n) (ifDepthTokens n) (ifDepthBudget n) := by
  induction n with
  | zero => exact .block .nil
  | succ n ih => exact .ifNone (ident_atom_rparen "x") (.block (.stmtCons ih .nil))

theorem arbitrary_depth_coverage (n extra : Nat) (s : St) (he : NoFollowingElse s) :
    stmt (extra + ifDepthBudget n + 6) .body (locatedInput (ifDepthTokens n) s) = .ok (ifDepth n, s) :=
  atom_stmt_coverage (if_depth_relation n) extra s (Or.inr he)
    (Or.inl (by cases n <;> rfl))

/-- Inside a block the closing brace frames an open if: a following else
stays outside the block. -/
theorem open_if_in_block_closed (n : Nat) (s : St) :
    stmt (n + max (ifDepthBudget 1 + 7) 0 + 6) .body
      (locatedInput (braces [ifDepthTokens 1].flatten) (locatedInput [.kw .else_] s)) =
      .ok (.blockStmt (.block (.cons (.stmtItem (ifDepth 1)) .nil)), locatedInput [.kw .else_] s) :=
  atom_stmt_coverage (.block (.stmtCons (if_depth_relation 1) .nil)) n
    (locatedInput [.kw .else_] s) (Or.inl rfl) (Or.inl rfl)

/-- Negative: `return;` is the empty return, not an atom return. -/
theorem no_semi_head_refuses_empty : ¬ NoSemiHead [] := fun h => h.1 rfl

theorem no_semi_head_refuses_semi : ¬ NoSemiHead [.punct .semi] := fun h => h.2 rfl

def nestedWrong : Syn (.stmt .body) :=
  .ifStmt (.ident "x") (.ifStmt (.ident "y") (.blockStmt (.block .nil)) .none)
    (.some (.blockStmt (.block .nil)))

/-- Negative: the wrong dangling-else tree is outside the fragment. -/
theorem nested_wrong_tree_excluded (ts : List Tok) (d : Nat) : ¬ AtomStmt nestedWrong ts d := by
  intro h
  have bad := atom_stmt_node h
  cases bad

/-- Negative: the actual parser refuses nested unchecked, which AtomItems
cannot represent (its unchecked constructor needs an unchecked-free context). -/
theorem nested_unchecked_actual_refusal (n : Nat) (l : Bool) (ts : List Tok) (s : St) :
    ∃ err, item (n + 1) ⟨l, true⟩ (uncheckedInput ts s) = .error err :=
  ⟨_, unchecked_nested_refused n l ts s⟩

/-- `for (;;) do { continue; } while (x);` with arbitrary suffix:
the empty-header `forLoop` and `doLoop` constructors. -/
def forDoTree : Syn (.stmt .body) :=
  .forStmt .none .none .none (.doWhile (.blockStmt (.block (.cons (.stmtItem .continueStmt) .nil)))
    (.ident "x"))

def forDoTokens : List Tok :=
  [.kw .for_, .punct .lparen, .punct .semi, .punct .semi, .punct .rparen] ++
  ([.kw .do_] ++ braces [[.kw .continue_, .punct .semi]].flatten ++ [.kw .while_, .punct .lparen] ++
    [.ident "x"] ++ [.punct .rparen, .punct .semi])

theorem for_do_relation : AtomStmt forDoTree forDoTokens 14 :=
  .forLoop (.doLoop (ident_atom_rparen "x") (.block (.stmtCons .continueStmt .nil)))

theorem for_do_arbitrary_suffix (n : Nat) (s : St) :
    stmt (n + 14 + 6) .body (locatedInput forDoTokens s) = .ok (forDoTree, s) :=
  atom_stmt_coverage for_do_relation n s (Or.inl rfl) (Or.inl rfl)

/-- `for (; c; u) break;` in all four shapes of the optional condition and update. -/
def forHeaderTokens (cs vs : List Tok) : List Tok :=
  [.kw .for_, .punct .lparen, .punct .semi] ++ cs ++ [.punct .semi] ++ vs ++ [.punct .rparen] ++
    [.kw .break_, .punct .semi]

theorem for_header_none_none (n : Nat) (s : St) :
    stmt (n + 1 + 6) .body (locatedInput (forHeaderTokens [] []) s) =
      .ok (.forStmt .none .none .none .breakStmt, s) :=
  atom_stmt_coverage (.forAtom .none .none .breakStmt) n s (Or.inl rfl) (Or.inl rfl)

theorem for_header_cond (n : Nat) (s : St) :
    stmt (n + 6 + 6) .body (locatedInput (forHeaderTokens [.ident "c"] []) s) =
      .ok (.forStmt .none (.some (.ident "c")) .none .breakStmt, s) :=
  atom_stmt_coverage (.forAtom (.some (ident_atom_semi "c") (by intro h; cases h)
    (by intro h; cases h)) .none .breakStmt) n s (Or.inl rfl) (Or.inl rfl)

theorem for_header_update (n : Nat) (s : St) :
    stmt (n + 6 + 6) .body (locatedInput (forHeaderTokens [] [.ident "v"]) s) =
      .ok (.forStmt .none .none (.some (.ident "v")) .breakStmt, s) :=
  atom_stmt_coverage (.forAtom .none (.some (ident_atom_rparen "v") (by intro h; cases h)
    (by intro h; cases h)) .breakStmt) n s (Or.inl rfl) (Or.inl rfl)

theorem for_header_both (n : Nat) (s : St) :
    stmt (n + 11 + 6) .body (locatedInput (forHeaderTokens [.bool true] [.ident "v"]) s) =
      .ok (.forStmt .none (.some (.lit (.bool true))) (.some (.ident "v")) .breakStmt, s) :=
  atom_stmt_coverage (.forAtom (.some (bool_atom_semi true) (by intro h; cases h)
    (by intro h; cases h)) (.some (ident_atom_rparen "v") (by intro h; cases h)
    (by intro h; cases h)) .breakStmt) n s (Or.inl rfl) (Or.inl rfl)

/-- The kernel evaluates the actual parser on the four-shape header. -/
theorem for_header_both_kernel :
    stmt 17 .body (locatedInput (forHeaderTokens [.bool true] [.ident "v"]) ⟨[], [], 0⟩) =
      .ok (.forStmt .none (.some (.lit (.bool true))) (.some (.ident "v")) .breakStmt,
        ⟨[], [], 0⟩) := by
  rfl

/-- Negative: an update atom may not start with `)` (the parser reads it as absent). -/
theorem opt_atom_refuses_rparen_head (e : Syn .expr) (a : Nat) :
    ¬ OptAtom .rparen (.some e) [.punct .rparen] a := by
  intro h
  cases h with
  | some _ _ hh => exact hh rfl

/-- Negative: `break` needs the loop context the relation's index demands;
outside a loop the actual parser refuses it. -/
theorem break_outside_loop_refused (n : Nat) (s : St) :
    ∃ err, stmt (n + 1) .body (locatedInput [.kw .break_, .punct .semi] s) = .error err :=
  ⟨_, break_outside_loop n false 0 0 0 0 s⟩

/-- `{ x; for (y; z; ) { w; } }`: simple statements as items, a body and a
`for` initialiser, through the stated `simple` premise. -/
def simpleBody : Syn (.stmt ⟨true, false⟩) :=
  .blockStmt (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "w")))) .nil))

def simpleItems : Syn (.list (.item .body)) :=
  .cons (.stmtItem (.simpleStmt (.exprStmt (.ident "x"))))
    (.cons (.stmtItem (.forStmt (.some (.exprStmt (.ident "y"))) (.some (.ident "z")) .none simpleBody))
      .nil)

def simpleParts : List (List Tok) :=
  [[.ident "x"] ++ [.punct .semi],
   [.kw .for_, .punct .lparen] ++ [.ident "y"] ++ [.punct .semi] ++ [.ident "z"] ++
     [.punct .semi] ++ [] ++ [.punct .rparen] ++ braces [[.ident "w"] ++ [.punct .semi]].flatten]

theorem simple_items_relation : AtomItems simpleItems simpleParts 33 :=
  .stmtCons (.simpleS (ident_simple_atom "x") rfl)
    (.stmtCons (.forInit (ident_simple_atom "y") rfl
      (.some (ident_atom_semi "z") (by intro h; cases h) (by intro h; cases h)) .none
      (.block (.stmtCons (.simpleS (ident_simple_atom "w") rfl) .nil))) .nil)

theorem simple_block_coverage (n : Nat) (s : St) :
    stmt (n + 33 + 6) .body (locatedInput (braces simpleParts.flatten) s) =
      .ok (.blockStmt (.block simpleItems), s) :=
  atom_stmt_coverage (.block simple_items_relation) n s (Or.inl rfl) (Or.inl rfl)

/-- The kernel evaluates the actual parser on `x;` at the derived fuel. -/
theorem simple_stmt_kernel :
    stmt 13 .body (locatedInput ([.ident "x"] ++ [.punct .semi]) ⟨[], [], 0⟩) =
      .ok (.simpleStmt (.exprStmt (.ident "x")), ⟨[], [], 0⟩) := by
  rfl

theorem simple_block_unique {x : Syn (.stmt .body)} {d : Nat}
    (h : AtomStmt x (braces simpleParts.flatten) d) : x = .blockStmt (.block simpleItems) :=
  atom_stmt_token_unique h (.block simple_items_relation) rfl

/-- Negative: statement keywords, `else`, braces, `;` and `revert` are not
simple-statement heads (their dispatchers read them). -/
theorem simple_head_refusals :
    simpleHeadList [.kw .if_] = false ∧ simpleHeadList [.kw .else_] = false ∧
    simpleHeadList [.kw .unchecked] = false ∧ simpleHeadList [.punct .lbrace] = false ∧
    simpleHeadList [.punct .rbrace] = false ∧ simpleHeadList [.punct .semi] = false ∧
    simpleHeadList [.ident "revert"] = false ∧ simpleHeadList [] = false := by
  decide

/-- Negative: the `simple` premise names the parsed tree. -/
theorem simple_premise_names_parsed :
    ¬ SimpleAtom (.exprStmt (.ident "y")) [.ident "x"] 6 := by
  intro h
  have bad := (ident_simple_atom "x" 0 ⟨[], [], 0⟩).symm.trans (h 0 ⟨[], [], 0⟩)
  injection bad with bad
  injection bad with bad
  injection bad with bad
  injection bad with bad
  exact absurd bad (by decide)

/-- `{ emit E(); revert Err(); }` through the path and argument premises. -/
def callItems : Syn (.list (.item .body)) :=
  .cons (.stmtItem (.emit (.ident "E") (.positional .nil)))
    (.cons (.stmtItem (.revert (.ident "Err") (.positional .nil))) .nil)

def callParts : List (List Tok) :=
  [[.kw .emit] ++ [.ident "E"] ++ [.punct .lparen, .punct .rparen] ++ [.punct .semi],
   [.ident "revert"] ++ [.ident "Err"] ++ [.punct .lparen, .punct .rparen] ++ [.punct .semi]]

theorem call_items_relation : AtomItems callItems callParts 8 :=
  .stmtCons (.emitS (ident_path_atom "E") empty_args_atom rfl rfl)
    (.stmtCons (.revertS (ps := []) (ident_path_atom "Err") empty_args_atom rfl rfl) .nil)

theorem call_block_coverage (n : Nat) (s : St) :
    stmt (n + 8 + 6) .body (locatedInput (braces callParts.flatten) s) =
      .ok (.blockStmt (.block callItems), s) :=
  atom_stmt_coverage (.block call_items_relation) n s (Or.inl rfl) (Or.inl rfl)

/-- The kernel evaluates the actual parser on `revert Err();`. -/
theorem revert_kernel :
    stmt 8 .body (locatedInput ([.ident "revert"] ++ [.ident "Err"] ++
      [.punct .lparen, .punct .rparen] ++ [.punct .semi]) ⟨[], [], 0⟩) =
      .ok (.revert (.ident "Err") (.positional .nil), ⟨[], [], 0⟩) := by
  rfl

/-- Contextual `revert`: followed by a non-identifier it is not a revert
statement; the dispatcher sends it to `simpleStmt`, which reads `revert;` and
`revert();` as expression statements (all tokens consumed). -/
theorem revert_needs_identifier :
    (stmt 8 .body (locatedInput [.ident "revert", .punct .semi] ⟨[], [], 0⟩)).toOption.map
      (fun p => ((g0NodeCtors p.1).take 3, p.2.ts.length)) =
      some ([.simpleStmt, .exprStmt, .ident], 0) ∧
    (stmt 20 .body (locatedInput [.ident "revert", .punct .lparen, .punct .rparen,
      .punct .semi] ⟨[], [], 0⟩)).toOption.map
      (fun p => ((g0NodeCtors p.1).take 3, p.2.ts.length)) =
      some ([.simpleStmt, .exprStmt, .call], 0) := by
  decide +kernel

/-- Negative: the precedence contract refuses a non-path event. -/
theorem emit_needs_path : (Syn.emit (k := .body) (.lit (.bool true)) (.positional .nil)).precNode = false := by
  rfl

#print axioms call_block_coverage
#print axioms revert_kernel
#print axioms revert_needs_identifier
#print axioms emit_needs_path
#print axioms simple_block_coverage
#print axioms simple_stmt_kernel
#print axioms simple_block_unique
#print axioms simple_head_refusals
#print axioms simple_premise_names_parsed
#print axioms for_do_arbitrary_suffix
#print axioms for_header_none_none
#print axioms for_header_cond
#print axioms for_header_update
#print axioms for_header_both
#print axioms for_header_both_kernel
#print axioms opt_atom_refuses_rparen_head
#print axioms break_outside_loop_refused
#print axioms outer_block_coverage
#print axioms outer_block_at_fuel_32
#print axioms outer_block_unique
#print axioms arbitrary_width_block
#print axioms arbitrary_depth_coverage
#print axioms open_if_in_block_closed
#print axioms no_semi_head_refuses_empty
#print axioms no_semi_head_refuses_semi
#print axioms nested_wrong_tree_excluded
#print axioms nested_unchecked_actual_refusal
end Solidity.Frontend.StatementGrammarH28
