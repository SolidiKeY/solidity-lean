import Solidity.Frontend.StatementGrammarH28.TokenRoot

/-! All fixed roots have inhabited actual-yield controls. Simple/revert head
collision is retained as a negative control on first-token-only reasoning. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def fixedRootControls : List (Syn (.stmt ⟨true, false⟩) × Tok) :=
  [(.blockStmt (.block .nil), .punct .lbrace),
   (.ifStmt (.ident "p") (.returnStmt .none) .none, .kw .if_),
   (.forStmt .none .none .none (.breakStmt), .kw .for_),
   (.whileStmt (.ident "p") (.continueStmt), .kw .while_),
   (.doWhile (.breakStmt) (.ident "p"), .kw .do_),
   (.continueStmt, .kw .continue_),
   (.breakStmt, .kw .break_),
   (.tryStmt (.ident "g") .nil (.block .nil) (.catchPlain (.block .nil)) .nil, .kw .try_),
   (.returnStmt .none, .kw .return_),
   (.emit (.ident "E") (.positional .nil), .kw .emit),
   (.revert (.ident "Err") (.positional .nil), .ident "revert"),
   (.assembly false [] .nil, .kw .assembly)]

def fixedRootControlCheck (pair : Syn (.stmt ⟨true, false⟩) × Tok) : Bool :=
  match pair.1.toks [] with
  | none => false
  | some ts => ts.head? == some pair.2

theorem fixed_root_controls_checked : fixedRootControls.all fixedRootControlCheck = true := by
  decide +kernel

theorem fixed_root_controls_inventory : fixedRootControls.map (fun p => root p.1) =
    [.block, .conditional, .forLoop, .whileLoop, .doLoop, .continueLoop,
     .breakLoop, .tryCatch, .returnValue, .emitEvent, .revertError, .assembly] := rfl

/-- The simple/revert first-token collision is inhabited. No negative claim
about their full token streams is made: these two streams are different. -/
theorem simple_revert_head_collision :
    (Syn.simpleStmt (k := .body) (.exprStmt (.ident "revert"))).toks [] =
      some [.ident "revert", .punct .semi] ∧
    (Syn.revert (k := .body) (.ident "Err") (.positional .nil)).toks [] =
      some [.ident "revert", .ident "Err", .punct .lparen, .punct .rparen, .punct .semi] := by
  decide +kernel

/-- A first-token collision does not force simple and revert roots equal. -/
theorem simple_revert_roots_differ :
    root (Syn.simpleStmt (k := .body) (.exprStmt (.ident "revert"))) ≠
    root (Syn.revert (k := .body) (.ident "Err") (.positional .nil)) := by
  intro h
  cases h

/-- Arbitrary common prefixes cannot belong to distinct fixed roots. -/
theorem break_continue_prefixes_differ (L M N P : List Choice)
    (xs ys : List (List Tok)) (rest tail : List Tok)
    (hb : (Syn.breakStmt (u := false)).yield L = some (xs, M))
    (hc : (Syn.continueStmt (u := false)).yield N = some (ys, P)) :
    xs.flatten ++ rest ≠ ys.flatten ++ tail := by
  intro he
  have roots := nonSimple_root_of_equal_prefix .breakStmt .continueStmt
    (by intro h; cases h) (by intro h; cases h) L M N P xs ys rest tail hb hc he
  cases roots

theorem nonempty_layout_and_suffix_head :
    (Syn.returnStmt (k := .body) .none).yield [.frags [1]] =
      some ([[.kw .return_, .punct .semi]], [.frags [1]]) ∧
    (([.kw .return_, .punct .semi] : List Tok) ++ [Tok.kw .else_]).head? =
      some (.kw .return_) := by
  decide +kernel

#print axioms nonempty_layout_and_suffix_head
#print axioms fixed_root_controls_checked
#print axioms fixed_root_controls_inventory
#print axioms simple_revert_head_collision
#print axioms simple_revert_roots_differ
#print axioms break_continue_prefixes_differ
end Solidity.Frontend.StatementGrammarH28
