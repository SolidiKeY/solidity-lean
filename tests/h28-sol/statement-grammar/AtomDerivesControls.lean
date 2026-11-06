import Solidity.Frontend.StatementGrammarH28.AtomDerives

/-! Controls for yield and `Derives` uniqueness of the mutual atom fragment:
print witnesses for every `AtomStmtP`, `AtomItemsP`, `AtomCatchP` and
`AtomCatchesP` constructor (blocks, loops, conditionals, `return`, `for`
headers, try with plain and signature catches, assembly, calls, contextual
revert, unchecked), the `Derives` characterisation and uniqueness, and
negative controls. -/
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

/-- Print witnesses for the loop and conditional constructors and a two-clause
catch list: `while (c) { if (c) break; else continue; } for (;;) {}
for (; c; v) {} for (x; c; v) {} do {} while (c); return y;` and
`try f {} catch {} catch (bool) {}`. -/
theorem loops_print_relation :
    AtomItemsP (k := .body)
      (.cons (.stmtItem (.whileStmt (.ident "c") (.blockStmt (.block (.cons (.stmtItem
          (.ifStmt (.ident "c") .breakStmt (.some .continueStmt))) .nil)))))
      (.cons (.stmtItem (.forStmt .none .none .none (.blockStmt (.block .nil))))
      (.cons (.stmtItem (.forStmt .none (.some (.ident "c")) (.some (.ident "v"))
          (.blockStmt (.block .nil))))
      (.cons (.stmtItem (.forStmt (.some (.exprStmt (.ident "x"))) (.some (.ident "c"))
          (.some (.ident "v")) (.blockStmt (.block .nil))))
      (.cons (.stmtItem (.doWhile (.blockStmt (.block .nil)) (.ident "c")))
      (.cons (.stmtItem (.returnStmt (.some (.ident "y"))))
      (.cons (.stmtItem (.ifStmt (.ident "c") (.returnStmt .none) .none))
      (.cons (.stmtItem (.tryStmt (.ident "f") .nil (.block .nil) (.catchPlain (.block .nil))
          (.cons (.catchSig .none (.param (.elem .bool) .none .none) .nil (.block .nil)) .nil)))
        .nil))))))))
      [[.kw .while_, .punct .lparen] ++ [.ident "c"] ++ [.punct .rparen] ++
          braces [[.kw .if_, .punct .lparen] ++ [.ident "c"] ++ [.punct .rparen] ++
            [.kw .break_, .punct .semi] ++ [.kw .else_] ++ [.kw .continue_, .punct .semi]].flatten,
       [.kw .for_, .punct .lparen, .punct .semi, .punct .semi, .punct .rparen] ++
          braces ([] : List (List Tok)).flatten,
       [.kw .for_, .punct .lparen, .punct .semi] ++ [.ident "c"] ++ [.punct .semi] ++
          [.ident "v"] ++ [.punct .rparen] ++ braces ([] : List (List Tok)).flatten,
       [.kw .for_, .punct .lparen] ++ [.ident "x"] ++ [.punct .semi] ++ [.ident "c"] ++
          [.punct .semi] ++ [.ident "v"] ++ [.punct .rparen] ++ braces ([] : List (List Tok)).flatten,
       [.kw .do_] ++ braces ([] : List (List Tok)).flatten ++ [.kw .while_, .punct .lparen] ++
          [.ident "c"] ++ [.punct .rparen, .punct .semi],
       [.kw .return_] ++ [.ident "y"] ++ [.punct .semi],
       [.kw .if_, .punct .lparen] ++ [.ident "c"] ++ [.punct .rparen] ++ [.kw .return_, .punct .semi],
       [.kw .try_] ++ [.ident "f"] ++ braces ([] : List (List Tok)).flatten ++
          ([.kw .catch_] ++ braces ([] : List (List Tok)).flatten) ++
          [[.kw .catch_] ++ optToks idt none ++ parens ([.elem .bool] ++ optToks idt none) ++
            braces ([] : List (List Tok)).flatten].flatten] :=
  .stmtCons (.whileLoop (ident_prints_to "c")
      (.block (.stmtCons (.ifSome (ident_prints_to "c") .breakStmt .continueStmt) .nil)))
    (.stmtCons (.forLoop (.block .nil))
    (.stmtCons (.forAtom (ident_prints_to "c") (ident_prints_to "v") (.block .nil))
    (.stmtCons (.forInit (simple_ident_prints_to "x") (ident_prints_to "c")
        (ident_prints_to "v") (.block .nil))
    (.stmtCons (.doLoop (ident_prints_to "c") (.block .nil))
    (.stmtCons (.returnSome (ident_prints_to "y"))
    (.stmtCons (.ifNone (ident_prints_to "c") .returnNone)
    (.stmtCons (.tryS (ident_prints_to "f") .nil (.plain .nil)
        (.cons (.sig (bool_param_prints_to none) nil_prints rfl .nil) .nil))
      .nil)))))))

/-- Negative: the dangling-else tree with the outer association has a print
witness (the printer cannot tell the associations apart), but no parse
witness: the precedence contract refuses it. -/
theorem outer_else_print_relation :
    AtomStmtP (k := .body)
      (.ifStmt (.ident "c") (.ifStmt (.ident "d") (.returnStmt .none) .none)
        (.some (.returnStmt .none)))
      ([.kw .if_, .punct .lparen] ++ [.ident "c"] ++ [.punct .rparen] ++
        ([.kw .if_, .punct .lparen] ++ [.ident "d"] ++ [.punct .rparen] ++
          [.kw .return_, .punct .semi]) ++ [.kw .else_] ++ [.kw .return_, .punct .semi]) :=
  .ifSome (ident_prints_to "c") (.ifNone (ident_prints_to "d") .returnNone) .returnNone

theorem outer_else_not_parsed {ts : List Tok} {d : Nat} :
    ¬ AtomStmt (k := .body)
      (.ifStmt (.ident "c") (.ifStmt (.ident "d") (.returnStmt .none) .none)
        (.some (.returnStmt .none))) ts d :=
  fun h => absurd (atom_stmt_node h) (by decide)

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
#print axioms loops_print_relation
#print axioms outer_else_print_relation
#print axioms outer_else_not_parsed
end Solidity.Frontend.StatementGrammarH28
