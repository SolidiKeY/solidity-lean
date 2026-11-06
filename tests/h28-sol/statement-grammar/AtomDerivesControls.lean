import Solidity.Frontend.StatementGrammarH28.AtomDerives

/-! Controls for yield and `Derives` uniqueness of the mutual atom fragment:
print witnesses for a block with every new statement form (try with plain
and signature catches, assembly, contextual revert, unchecked, loops), their
`Derives` characterisation and uniqueness, and negative controls. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

/-- `{ try f { return; } catch (bool e) { } revert; assembly {} unchecked { x; } }`. -/
def mixedItems : Syn (.list (.item .body)) :=
  .cons (.stmtItem (.tryStmt (.ident "f") .nil (.block (.cons (.stmtItem (.returnStmt .none)) .nil))
      (.catchSig .none (.param (.elem .bool) .none (.some "e")) .nil (.block .nil)) .nil))
    (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "revert"))))
      (.cons (.stmtItem (.assembly false [] .nil))
        (.cons (.uncheckedItem (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "x")))) .nil)))
          .nil)))

def mixedParts : List (List Tok) :=
  [[.kw .try_] ++ [.ident "f"] ++ braces [[.kw .return_, .punct .semi]].flatten ++
      ([.kw .catch_] ++ optToks idt none ++ parens ([.elem .bool] ++ optToks idt (some "e")) ++
        braces ([] : List (List Tok)).flatten) ++ ([] : List (List Tok)).flatten,
   .ident "revert" :: ([] : List Tok) ++ [.punct .semi],
   [.kw .assembly] ++ evmToks false ++ [] ++ [.punct .lbrace, .punct .rbrace],
   .kw .unchecked :: braces [[.ident "x"] ++ [.punct .semi]].flatten]

theorem mixed_relation : AtomItems mixedItems mixedParts 28 :=
  .stmtCons (.tryS (ident_expr_brace "f") (.stmtCons .returnNone .nil) (fun _ => rfl)
      (.sig (bool_params_atom (some "e")) rfl .nil) .nil)
    (.stmtCons (.revertExpr (ss := []) (ident_simple_atom "revert") rfl)
      (.stmtCons (.asm .none empty_yul_body rfl)
        (.uncheckedCons (.stmtCons (.simpleS (ident_simple_atom "x") rfl) .nil) .nil)))

theorem mixed_print_relation : AtomItemsP mixedItems mixedParts :=
  .stmtCons (.tryS (ident_prints_to "f") (.stmtCons .returnNone .nil)
      (.sig (bool_param_prints_to (some "e")) nil_prints rfl .nil) .nil)
    (.stmtCons (.revertExpr (ss := []) (simple_ident_prints_to "revert"))
      (.stmtCons (.asm (bs := []) rfl ⟨[], nil_prints, rfl⟩)
        (.uncheckedCons (.stmtCons (.simpleS (simple_ident_prints_to "x")) .nil) .nil)))

theorem mixed_block_derives (words : List Tok) :
    (Syn.blockStmt (k := .body) (.block mixedItems)).Derives words ↔
      words = braces mixedParts.flatten :=
  atom_stmt_derives_iff (.block mixed_print_relation) words

/-- The only fragment tree deriving the block's words. -/
theorem mixed_block_yield_unique {y : Syn (.stmt .body)} {us : List Tok} {e : Nat}
    (hy : AtomStmt y us e) (py : AtomStmtP y us)
    (dy : y.Derives (braces mixedParts.flatten)) : y = .blockStmt (.block mixedItems) :=
  atom_stmt_yield_unique hy py (.block mixed_relation) (.block mixed_print_relation) dy
    ((mixed_block_derives _).mpr rfl)

/-- The printer agrees with the parse tokens, computed by the kernel. -/
theorem mixed_block_toks_kernel :
    (Syn.blockStmt (k := .body) (.block mixedItems)).toks [] = some (braces mixedParts.flatten) := by
  decide +kernel

/-- `try f returns (bool) {} catch {}` through the return-parameter print premise. -/
theorem try_rets_print_relation :
    AtomStmtP (k := .body)
      (.tryStmt (.ident "f") (.cons (.param (.elem .bool) .none .none) .nil) (.block .nil)
        (.catchPlain (.block .nil)) .nil)
      ([.kw .try_] ++ [.ident "f"] ++
        (.kw .returns :: [.punct .lparen, .elem .bool, .punct .rparen]) ++
        braces ([] : List (List Tok)).flatten ++
        ([.kw .catch_] ++ braces ([] : List (List Tok)).flatten) ++
        ([] : List (List Tok)).flatten) :=
  .tryRets (ident_prints_to "f") (rps := [[.elem .bool]]) (fun _ => rfl) (by intro h; cases h) rfl
    .nil (.plain .nil) .nil

/-- `assembly ("memory-safe") {}` through the flag print side condition. -/
theorem asm_flag_print_relation :
    AtomStmtP (k := .body) (.assembly true ["memory-safe"] .nil)
      ([.kw .assembly] ++ evmToks true ++
        ([.punct .lparen] ++ [.str (ascii "memory-safe")] ++ [.punct .rparen]) ++ braces []) :=
  .asm rfl ⟨[], nil_prints, rfl⟩

/-- `revert Err();` and `emit E();` through the path and argument print premises. -/
theorem call_print_relation :
    AtomItemsP (k := .body)
      (.cons (.stmtItem (.revert (.ident "Err") (.positional .nil)))
        (.cons (.stmtItem (.emit (.ident "E") (.positional .nil))) .nil))
      [[.ident "revert"] ++ [.ident "Err"] ++ [.punct .lparen, .punct .rparen] ++ [.punct .semi],
       [.kw .emit] ++ [.ident "E"] ++ [.punct .lparen, .punct .rparen] ++ [.punct .semi]] :=
  .stmtCons (.revertS (ps := []) (ident_prints_to "Err") empty_args_prints_to)
    (.stmtCons (.emitS (ident_prints_to "E") empty_args_prints_to) .nil)

/-- Negative: a tree derives no other word list. -/
theorem mixed_block_derives_nothing_else :
    ¬ (Syn.blockStmt (k := .body) (.block mixedItems)).Derives [] := by
  intro h
  have := (mixed_block_derives []).mp h
  cases this

/-- Negative: the print premise names the printed tokens. -/
theorem prints_to_names_tokens : ¬ Prints (Syn.ident "x") [[.ident "y"]] := by
  intro h
  have bad := h []
  simp only [Syn.yield, idt] at bad
  injection bad with bad
  injection bad with bad
  injection bad with bad
  injection bad with bad
  exact absurd bad (by decide)

#print axioms mixed_relation
#print axioms mixed_print_relation
#print axioms mixed_block_derives
#print axioms mixed_block_yield_unique
#print axioms mixed_block_toks_kernel
#print axioms try_rets_print_relation
#print axioms asm_flag_print_relation
#print axioms call_print_relation
#print axioms mixed_block_derives_nothing_else
#print axioms prints_to_names_tokens
end Solidity.Frontend.StatementGrammarH28
