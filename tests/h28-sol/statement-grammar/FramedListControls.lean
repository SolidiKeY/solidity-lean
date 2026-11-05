import Solidity.Frontend.StatementGrammarH28.FramedStatementList

/-! Inhabited token-boundary controls. No parser success claim is made. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def frameCtx : SCtx := ⟨true, false⟩

def semiStatementWitnesses : List (Syn (.stmt frameCtx) × List Choice) :=
  [(.simpleStmt (.exprStmt (.ident "x")), []),
   (.simpleStmt (.declVar (.varDecl (.elem .bool) .none "x") .none), []),
   (.simpleStmt (.declTuple 1 (.varDecl (.elem .bool) .none "x") .nil (.ident "y")), []),
   (.continueStmt, []), (.breakStmt, []),
   (.returnStmt .none, []), (.returnStmt (.some (.ident "x")), []),
   (.returnStmt (.some (.lit (.str [59]))), [.frags [1]]),
   (.emit (.ident "E") (.positional .nil), []),
   (.emit (.ident "E") (.named (.cons (.namedArg "x" (.ident "y")) .nil)), []),
   (.revert (.ident "E") (.positional .nil), []),
   (.revert (.ident "E") (.named (.cons (.namedArg "x" (.ident "y")) .nil)), [])]

def firstSemiCheck (w : Syn (.stmt frameCtx) × List Choice) : Bool :=
  match w.1.yield w.2 with
  | some (parts, []) => SemiRoot (root w.1) && semiSuffix parts.flatten == some []
  | _ => false

theorem all_semicolon_variants_checked :
    semiStatementWitnesses.length = 12 ∧
    semiStatementWitnesses.all firstSemiCheck = true := by decide +kernel

theorem six_roots_exhaustive :
    (semiStatementWitnesses.map (fun w => root w.1)).eraseDups =
      [.simple, .continueLoop, .breakLoop, .returnValue, .emitEvent, .revertError] := by
  decide +kernel

def mixedFramedList : Syn (.list (.stmt frameCtx)) :=
  .cons (.simpleStmt (.exprStmt (.ident "x"))) (.cons (.blockStmt (.block (.cons (.stmtItem (.ifStmt (.ident "c") (.returnStmt (.some (.ident "x"))) .none)) .nil))) (.cons (.returnStmt (.some (.lit (.str [59])))) (.cons (.continueStmt) (.cons (.breakStmt) (.cons (.emit (.ident "E") (.positional .nil)) (.cons (.revert (.ident "E") (.positional .nil)) (.nil)))))))

theorem mixed_framed_inhabited : FramedStatements mixedFramedList := by
  simp only [mixedFramedList, FramedStatements_nil, FramedStatements_cons, FramedStatement, root_simpleStmt, root_blockStmt, root_returnStmt, root_continueStmt,
    root_breakStmt, root_emit, root_revert, SemiRoot,
    or_true, true_or, and_true]

def mixedFramedTokens : List (List Tok) :=
  [[.ident "x", .punct .semi],
   [.punct .lbrace, .kw .if_, .punct .lparen, .ident "c", .punct .rparen,
    .kw .return_, .ident "x", .punct .semi, .punct .rbrace],
   [.kw .return_, .str [59], .punct .semi],
   [.kw .continue_, .punct .semi], [.kw .break_, .punct .semi],
   [.kw .emit, .ident "E", .punct .lparen, .punct .rparen, .punct .semi],
   [.ident "revert", .ident "E", .punct .lparen, .punct .rparen, .punct .semi]]

theorem mixed_framed_actual_yield :
    mixedFramedList.yield [.frags [1]] = some (mixedFramedTokens, []) := by
  decide +kernel

theorem any_matching_list_segments {j : SCtx}
    (other : Syn (.list (.stmt j))) (L M : List Choice) (parts : List (List Tok))
    (hy : other.yield L = some (parts, M))
    (he : mixedFramedTokens.flatten = parts.flatten) : mixedFramedTokens = parts :=
  framed_statement_list_split mixedFramedList other mixed_framed_inhabited
    [.frags [1]] [] L M mixedFramedTokens parts mixed_framed_actual_yield hy he

def actualStatementRoots {k : SCtx} (ss : Syn (.list (.stmt k))) : List Root :=
  (g0ListValues ss).map root

theorem mixed_seven_roots :
    actualStatementRoots mixedFramedList =
      [.simple, .block, .returnValue, .continueLoop, .breakLoop, .emitEvent,
        .revertError] := by
  simp only [actualStatementRoots, mixedFramedList, g0ListValues_nil, g0ListValues_cons,
    List.map_cons, List.map_nil, root_simpleStmt, root_blockStmt, root_returnStmt, root_continueStmt,
    root_breakStmt, root_emit, root_revert]

/-- First-semicolon framing is false for a do-while body that returns. -/
theorem do_while_not_first_semicolon :
    let s : Syn (.stmt frameCtx) := .doWhile (.returnStmt .none) (.lit (.bool true))
    s.yield [] = some ([[.kw .do_, .kw .return_, .punct .semi, .kw .while_,
      .punct .lparen, .bool true, .punct .rparen, .punct .semi]], []) ∧
    SemiRoot (root s) = false ∧
    semiSuffix [.kw .do_, .kw .return_, .punct .semi, .kw .while_,
      .punct .lparen, .bool true, .punct .rparen, .punct .semi] ≠ some [] := by
  decide +kernel

#print axioms all_semicolon_variants_checked
#print axioms six_roots_exhaustive
#print axioms mixed_framed_inhabited
#print axioms mixed_framed_actual_yield
#print axioms any_matching_list_segments
#print axioms mixed_seven_roots
#print axioms do_while_not_first_semicolon
end Solidity.Frontend.StatementGrammarH28
