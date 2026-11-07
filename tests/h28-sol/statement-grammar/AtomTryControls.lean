import Solidity.Frontend.StatementGrammarH28.AtomNested
import Solidity.Frontend.StatementGrammarH28.G0Nodes
import Solidity.Frontend.StatementGrammarH28.G0Rejections

/-! Controls for `try` statements, catch clauses, `assembly` statements and
contextual `revert` expression statements in the mutual atom fragment: every new constructor of
`AtomStmt`, `AtomCatch` and `AtomCatches` inhabited, coverage at every excess
fuel and catch-free suffix, kernel parses, nesting inside blocks and
conditionals, and negative controls for the greedy catch loop and the
call-options lookahead. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

/-- `try f { return; } catch { x; } catch (bool e) { }`. -/
def tryTree : Syn (.stmt .body) :=
  .tryStmt (.ident "f") .nil (.block (.cons (.stmtItem (.returnStmt .none)) .nil))
    (.catchPlain (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "x")))) .nil)))
    (.cons (.catchSig .none (.param (.elem .bool) .none (.some "e")) .nil (.block .nil)) .nil)

def tryTokens : List Tok :=
  [.kw .try_] ++ [.ident "f"] ++ braces [[.kw .return_, .punct .semi]].flatten ++
    ([.kw .catch_] ++ braces [[.ident "x"] ++ [.punct .semi]].flatten) ++
    [[.kw .catch_] ++ optToks idt none ++ parens ([.elem .bool] ++ optToks idt (some "e")) ++
      braces ([] : List (List Tok)).flatten].flatten

theorem try_relation : AtomStmt tryTree tryTokens 37 :=
  .tryS (ident_expr_brace "f") (.stmtCons .returnNone .nil) (fun _ => rfl)
    (.plain (.stmtCons (.simpleS (ident_simple_atom "x") rfl) .nil))
    (.cons (.sig (bool_params_atom (some "e")) rfl .nil) .nil)

/-- Coverage at every excess fuel and every suffix that does not start with `catch`. -/
theorem try_coverage (n : Nat) (s : St) (hs : NoFollowingCatch s) :
    stmt (n + 37 + 6) .body (locatedInput tryTokens s) = .ok (tryTree, s) :=
  atom_stmt_coverage try_relation n s (Or.inl rfl) (Or.inr hs)

theorem try_token_unique {x : Syn (.stmt .body)} {d : Nat} (h : AtomStmt x tryTokens d) :
    x = tryTree :=
  atom_stmt_token_unique h try_relation rfl

/-- The kernel evaluates the actual parser on `try f {} catch {}`. -/
theorem try_small_kernel :
    stmt 12 .body (locatedInput [.kw .try_, .ident "f", .punct .lbrace, .punct .rbrace,
      .kw .catch_, .punct .lbrace, .punct .rbrace] ⟨[], [], 0⟩) =
      .ok (.tryStmt (.ident "f") .nil (.block .nil) (.catchPlain (.block .nil)) .nil,
        ⟨[], [], 0⟩) := by
  rfl

/-- `try f returns (bool) {} catch {}`, through the return-parameter premise. -/
theorem try_rets_relation :
    AtomStmt (k := .body)
      (.tryStmt (.ident "f") (.cons (.param (.elem .bool) .none .none) .nil) (.block .nil)
        (.catchPlain (.block .nil)) .nil)
      ([.kw .try_] ++ [.ident "f"] ++
        (.kw .returns :: [.punct .lparen, .elem .bool, .punct .rparen]) ++
        braces ([] : List (List Tok)).flatten ++
        ([.kw .catch_] ++ braces ([] : List (List Tok)).flatten) ++
        ([] : List (List Tok)).flatten) 15 :=
  .tryRets (ident_expr_returns "f") bool_rets_atom .nil (.plain .nil) .nil

theorem try_rets_coverage (n : Nat) (s : St) (hs : NoFollowingCatch s) :
    stmt (n + 15 + 6) .body (locatedInput ([.kw .try_] ++ [.ident "f"] ++
        (.kw .returns :: [.punct .lparen, .elem .bool, .punct .rparen]) ++
        braces ([] : List (List Tok)).flatten ++
        ([.kw .catch_] ++ braces ([] : List (List Tok)).flatten) ++
        ([] : List (List Tok)).flatten) s) =
      .ok (.tryStmt (.ident "f") (.cons (.param (.elem .bool) .none .none) .nil) (.block .nil)
        (.catchPlain (.block .nil)) .nil, s) :=
  atom_stmt_coverage try_rets_relation n s (Or.inl rfl) (Or.inr hs)

/-- A try inside a block, followed by a simple statement: the following item
discharges the catch frame. -/
def tryBlockParts : List (List Tok) :=
  [[.kw .try_] ++ [.ident "f"] ++ braces ([] : List (List Tok)).flatten ++
      ([.kw .catch_] ++ braces ([] : List (List Tok)).flatten) ++ ([] : List (List Tok)).flatten,
   [.ident "y"] ++ [.punct .semi]]

theorem try_block_relation :
    AtomItems (k := .body)
      (.cons (.stmtItem (.tryStmt (.ident "f") .nil (.block .nil) (.catchPlain (.block .nil)) .nil))
        (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "y")))) .nil)) tryBlockParts 16 :=
  .stmtCons (.tryS (ident_expr_brace "f") .nil (fun _ => rfl) (.plain .nil) .nil)
    (.stmtCons (.simpleS (ident_simple_atom "y") rfl) .nil)

/-- Any suffix after a block: the block is not catch-open. -/
theorem try_block_coverage (n : Nat) (s : St) :
    stmt (n + 16 + 6) .body (locatedInput (braces tryBlockParts.flatten) s) =
      .ok (.blockStmt (.block (.cons (.stmtItem (.tryStmt (.ident "f") .nil (.block .nil)
        (.catchPlain (.block .nil)) .nil))
        (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "y")))) .nil))), s) :=
  atom_stmt_coverage (.block try_block_relation) n s (Or.inl rfl) (Or.inl rfl)

/-- `if (c) try f {} catch {}`: the conditional is catch-open through its
then-branch, so it needs the frame; nearest else is unaffected. -/
theorem if_try_relation :
    AtomStmt (k := .body)
      (.ifStmt (.ident "c")
        (.tryStmt (.ident "f") .nil (.block .nil) (.catchPlain (.block .nil)) .nil) .none)
      ([.kw .if_, .punct .lparen] ++ [.ident "c"] ++ [.punct .rparen] ++
        ([.kw .try_] ++ [.ident "f"] ++ braces ([] : List (List Tok)).flatten ++
          ([.kw .catch_] ++ braces ([] : List (List Tok)).flatten) ++
          ([] : List (List Tok)).flatten)) 15 :=
  .ifNone (ident_atom_rparen "c") (.tryS (ident_expr_brace "f") .nil (fun _ => rfl) (.plain .nil) .nil)

theorem if_try_catch_open :
    catchOpen (Syn.ifStmt (k := .body) (.ident "c")
      (.tryStmt (.ident "f") .nil (.block .nil) (.catchPlain (.block .nil)) .nil) .none) = true := rfl

theorem if_try_coverage (n : Nat) (s : St) (he : NoFollowingElse s) (hs : NoFollowingCatch s) :
    stmt (n + 15 + 6) .body (locatedInput ([.kw .if_, .punct .lparen] ++ [.ident "c"] ++
        [.punct .rparen] ++
        ([.kw .try_] ++ [.ident "f"] ++ braces ([] : List (List Tok)).flatten ++
          ([.kw .catch_] ++ braces ([] : List (List Tok)).flatten) ++
          ([] : List (List Tok)).flatten)) s) =
      .ok (.ifStmt (.ident "c")
        (.tryStmt (.ident "f") .nil (.block .nil) (.catchPlain (.block .nil)) .nil) .none, s) :=
  atom_stmt_coverage if_try_relation n s (Or.inr he) (Or.inr hs)

/-- Negative: the catch loop is greedy. With a second `catch` as suffix the
actual parser reads both clauses, so a frame without `catch` is necessary. -/
theorem try_greedy_catch_kernel :
    stmt 12 .body (locatedInput [.kw .try_, .ident "f", .punct .lbrace, .punct .rbrace,
      .kw .catch_, .punct .lbrace, .punct .rbrace,
      .kw .catch_, .punct .lbrace, .punct .rbrace] ⟨[], [], 0⟩) =
      .ok (.tryStmt (.ident "f") .nil (.block .nil) (.catchPlain (.block .nil))
        (.cons (.catchPlain (.block .nil)) .nil), ⟨[], [], 0⟩) := by
  rfl

theorem catch_suffix_refused (ts : List Tok) (s : St) :
    ¬ NoFollowingCatch (locatedInput (.kw .catch_ :: ts) s) := fun h => h rfl

/-- Negative: a success body starting with `ident :` fails the block-body
side condition, and the actual expression parser reads it as call options. -/
theorem named_body_refused : ¬ BlockBodyParts [[.ident "x", .punct .colon]] :=
  fun h => absurd (h []) (by decide)

theorem named_body_call_options :
    (expr 20 (locatedInput [.ident "f", .punct .lbrace, .ident "x", .punct .colon, .ident "y",
      .punct .rbrace] ⟨[], [], 0⟩)).toOption.map
      (fun p => ((g0NodeCtors p.1).take 1, p.2.ts.length)) = some ([.callOptions], 0) := by
  decide +kernel

/-- Contextual `revert`: `{ revert; revert Err(); revert(); }`. The first and
last are expression statements (`revertExpr`), the middle a revert statement. -/
theorem revert_call_simple_atom :
    SimpleAtom (.exprStmt (.call (.ident "revert") (.positional .nil)))
      [.ident "revert", .punct .lparen, .punct .rparen] 8 :=
  fun _ _ => rfl

def revertItems : Syn (.list (.item .body)) :=
  .cons (.stmtItem (.simpleStmt (.exprStmt (.ident "revert"))))
    (.cons (.stmtItem (.revert (.ident "Err") (.positional .nil)))
      (.cons (.stmtItem (.simpleStmt (.exprStmt (.call (.ident "revert") (.positional .nil)))))
        .nil))

def revertParts : List (List Tok) :=
  [.ident "revert" :: ([] : List Tok) ++ [.punct .semi],
   [.ident "revert"] ++ [.ident "Err"] ++ [.punct .lparen, .punct .rparen] ++ [.punct .semi],
   .ident "revert" :: [.punct .lparen, .punct .rparen] ++ [.punct .semi]]

theorem revert_items_relation : AtomItems revertItems revertParts 16 :=
  .stmtCons (.revertExpr (ss := []) (ident_simple_atom "revert") rfl)
    (.stmtCons (.revertS (ps := []) (ident_path_atom "Err") empty_args_atom rfl rfl)
      (.stmtCons (.revertExpr revert_call_simple_atom rfl) .nil))

theorem revert_block_coverage (n : Nat) (s : St) :
    stmt (n + 16 + 6) .body (locatedInput (braces revertParts.flatten) s) =
      .ok (.blockStmt (.block revertItems), s) :=
  atom_stmt_coverage (.block revert_items_relation) n s (Or.inl rfl) (Or.inl rfl)

/-- `revert Err();` is never an expression statement of the fragment: an
identifier after `revert` fails `revertExprNext`. -/
theorem revert_ident_not_expr (y : String) (ts : List Tok) :
    revertExprNext (.ident y :: ts) = false := rfl

/-- Negative: `catch` is not a simple-statement head. -/
theorem catch_not_simple_head : simpleHeadList [.kw .catch_] = false := by decide

/-- `{ assembly {} assembly "evmasm" ("memory-safe") {} }`: both dialect
forms and both flag forms through the premises. -/
def asmItems : Syn (.list (.item .body)) :=
  .cons (.stmtItem (.assembly false [] .nil))
    (.cons (.stmtItem (.assembly true ["memory-safe"] .nil)) .nil)

def asmParts : List (List Tok) :=
  [[.kw .assembly] ++ evmToks false ++ [] ++ [.punct .lbrace, .punct .rbrace],
   [.kw .assembly] ++ evmToks true ++
      ([.punct .lparen] ++ [.str (ascii "memory-safe")] ++ [.punct .rparen]) ++
      [.punct .lbrace, .punct .rbrace]]

theorem asm_items_relation : AtomItems asmItems asmParts 9 :=
  .stmtCons (.asm .none empty_yul_body rfl)
    (.stmtCons (.asm (.some memory_safe_flag_atom) empty_yul_body rfl) .nil)

theorem asm_block_coverage (n : Nat) (s : St) :
    stmt (n + 9 + 6) .body (locatedInput (braces asmParts.flatten) s) =
      .ok (.blockStmt (.block asmItems), s) :=
  atom_stmt_coverage (.block asm_items_relation) n s (Or.inl rfl) (Or.inl rfl)

/-- The kernel parses the canonical rethrow statement of the accepted fixture
(`assembly ("memory-safe") { revert(add(raw, 32), mload(raw)) }`), consuming
every token, and the linked rethrow twin admits it (no rejection). -/
theorem rethrow_asm_kernel :
    (stmt 16 .body (locatedInput [.kw .assembly, .punct .lparen, .str (ascii "memory-safe"),
      .punct .rparen, .punct .lbrace, .ident "revert", .punct .lparen, .ident "add",
      .punct .lparen, .ident "raw", .punct .comma, .yulDec 32, .punct .rparen, .punct .comma,
      .ident "mload", .punct .lparen, .ident "raw", .punct .rparen, .punct .rparen,
      .punct .rbrace] ⟨[], [], 0⟩)).toOption.map
      (fun p => (g0Rejections p.1, (g0NodeCtors p.1).take 3, p.2.ts.length)) =
      some ([], [.assembly, .cons, .yulExprStmt], 0) := by
  decide +kernel

/-- The rethrow statement of the accepted fixture as an `AtomStmt`, through the
compositional `rethrow_yul_body`, with coverage at every suffix. -/
theorem rethrow_asm_relation :
    AtomStmt (k := .body) (.assembly false ["memory-safe"] (.cons (.yulExprStmt rethrowCall) .nil))
      ([.kw .assembly] ++ evmToks false ++
        ([.punct .lparen] ++ [.str (ascii "memory-safe")] ++ [.punct .rparen]) ++
        (.punct .lbrace :: rethrowCallToks ++ [.punct .rbrace])) 7 :=
  .asm (.some memory_safe_flag_atom) rethrow_yul_body rfl

theorem rethrow_asm_coverage (n : Nat) (s : St) :
    stmt (n + 7 + 6) .body (locatedInput ([.kw .assembly] ++ evmToks false ++
        ([.punct .lparen] ++ [.str (ascii "memory-safe")] ++ [.punct .rparen]) ++
        (.punct .lbrace :: rethrowCallToks ++ [.punct .rbrace])) s) =
      .ok (.assembly false ["memory-safe"] (.cons (.yulExprStmt rethrowCall) .nil), s) :=
  atom_stmt_coverage rethrow_asm_relation n s (Or.inl rfl) (Or.inl rfl)

/-- Negative: an unknown dialect string is not `"evmasm"`; it is neither a
flag list nor a Yul body, and the actual parser fails. -/
theorem asm_unknown_dialect_refused :
    (stmt 10 .body (locatedInput [.kw .assembly, .str (ascii "other"), .punct .lbrace,
      .punct .rbrace] ⟨[], [], 0⟩)).toOption.isNone = true := by
  decide +kernel

/-- A `try`-free block needs no catch frame: the general lemma, with the
node inventory checked by the kernel. -/
theorem revert_block_coverage_no_try (n : Nat) (s : St) :
    stmt (n + 16 + 6) .body (locatedInput (braces revertParts.flatten) s) =
      .ok (.blockStmt (.block revertItems), s) :=
  atom_stmt_coverage_no_try (.block revert_items_relation) (by decide +kernel) n s (Or.inl rfl)

/-- Negative: the lemma does not apply to a tree with a `try` node. -/
theorem try_tree_has_try : Ctor.tryStmt ∈ g0NodeCtors tryTree := by decide +kernel

#print axioms try_relation
#print axioms try_coverage
#print axioms try_token_unique
#print axioms try_small_kernel
#print axioms try_rets_relation
#print axioms try_rets_coverage
#print axioms try_block_relation
#print axioms try_block_coverage
#print axioms if_try_relation
#print axioms if_try_catch_open
#print axioms if_try_coverage
#print axioms try_greedy_catch_kernel
#print axioms catch_suffix_refused
#print axioms named_body_refused
#print axioms named_body_call_options
#print axioms revert_call_simple_atom
#print axioms revert_items_relation
#print axioms revert_block_coverage
#print axioms revert_ident_not_expr
#print axioms catch_not_simple_head
#print axioms asm_items_relation
#print axioms revert_block_coverage_no_try
#print axioms try_tree_has_try
#print axioms asm_block_coverage
#print axioms rethrow_asm_kernel
#print axioms rethrow_asm_relation
#print axioms rethrow_asm_coverage
#print axioms asm_unknown_dialect_refused
end Solidity.Frontend.StatementGrammarH28
