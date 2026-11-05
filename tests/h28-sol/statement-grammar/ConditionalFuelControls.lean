import Solidity.Frontend.StatementGrammarH28.ConditionalFuel

/-! Universal positive width/depth and actual parser refusal controls. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def fuelOpen (k : SCtx) : Syn (.stmt k) :=
  .ifStmt (.lit (.bool true)) (.blockStmt (.block .nil)) .none

def fuelWords : List Tok :=
  [.kw .if_, .punct .lparen, .bool true, .punct .rparen, .punct .lbrace, .punct .rbrace]

theorem fuel_open_relation (k : SCtx) : BooleanStatements (fuelOpen k) fuelWords 1 :=
  .ifNone (.loops (.block .nil))

def fuelItems (k : SCtx) : Nat → Syn (.list (.item k))
  | 0 => .nil
  | n + 1 => .cons (.stmtItem (fuelOpen k)) (fuelItems k n)

def fuelParts : Nat → List (List Tok)
  | 0 => []
  | n + 1 => fuelWords :: fuelParts n

theorem positive_width_bound (k : SCtx) (width : Nat) :
    BooleanListBound (fuelItems k (width + 1)) (fuelParts (width + 1)) 8 := by
  induction width with
  | zero => exact .cons (fuel_open_relation k) .nil
  | succ width ih => exact .cons (fuel_open_relation k) ih

theorem arbitrary_width_block_parse (k : SCtx) (width extra : Nat) (s : St) :
    block (extra + 9) k (blockInput (fuelParts (width + 1)).flatten s) =
      .ok (.block (fuelItems k (width + 1)), s) :=
  boolean_list_block_coverage (positive_width_bound k width) extra s

theorem arbitrary_width_statement_parse (k : SCtx) (width extra : Nat) (s : St) :
    stmt (extra + 10) k (blockInput (fuelParts (width + 1)).flatten s) =
      .ok (.blockStmt (.block (fuelItems k (width + 1))), s) :=
  boolean_list_block_stmt_coverage (positive_width_bound k width) extra s

theorem arbitrary_width_unchecked_parse (l : Bool) (width extra : Nat) (s : St) :
    item (extra + 10) ⟨l, false⟩ (uncheckedInput (fuelParts (width + 1)).flatten s) =
      .ok (.uncheckedItem (.block (fuelItems ⟨l, true⟩ (width + 1))), s) :=
  boolean_list_unchecked_coverage (positive_width_bound ⟨l, true⟩ width) extra s

theorem closing_brace_preserves_else (k : SCtx) (width extra : Nat) (s : St) :
    block (extra + 9) k
      (blockInput (fuelParts (width + 1)).flatten (locatedInput [.kw .else_] s)) =
      .ok (.block (fuelItems k (width + 1)), locatedInput [.kw .else_] s) :=
  arbitrary_width_block_parse k width extra _

def depthStatement (k : SCtx) : Nat → Syn (.stmt k)
  | 0 => .blockStmt (.block .nil)
  | d + 1 => .ifStmt (.lit (.bool false)) (depthStatement k d) .none

def depthWords : Nat → List Tok
  | 0 => braces []
  | d + 1 => [.kw .if_, .punct .lparen, .bool false, .punct .rparen] ++ depthWords d

theorem arbitrary_depth_relation (k : SCtx) (d : Nat) :
    BooleanStatements (depthStatement k d) (depthWords d) d := by
  induction d with
  | zero => exact .loops (.block .nil)
  | succ d ih => exact .ifNone ih

theorem arbitrary_depth_bound (k : SCtx) (d : Nat) :
    BooleanListBound (.cons (.stmtItem (depthStatement k d)) .nil) [depthWords d] (d + 7) := by
  simpa only [Nat.max_zero] using
    (BooleanListBound.cons (arbitrary_depth_relation k d) (BooleanListBound.nil (k := k)))

theorem arbitrary_depth_block_parse (k : SCtx) (d extra : Nat) (s : St) :
    block (extra + d + 8) k (blockInput (depthWords d) s) =
      .ok (.block (.cons (.stmtItem (depthStatement k d)) .nil), s) := by
  have h := boolean_list_block_coverage (arbitrary_depth_bound k d) extra s
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, Nat.add_assoc] using h

theorem empty_block_minimal (k : SCtx) (s : St) :
    block 1 k (blockInput [] s) = .ok (.block .nil, s) :=
  boolean_list_block_coverage (BooleanListBound.nil (k := k)) 0 s

theorem zero_block_fuel_refuses (k : SCtx) (s : St) :
    block 0 k (blockInput fuelWords s) ≠ .ok (.block (fuelItems k 1), s) := by
  intro bad
  cases bad

theorem zero_list_loop_refuses (k : SCtx) (s : St) :
    (match manyAux (blockLeafStep 9 k) 0 (leafInput fuelWords s) with
      | .error _ => true | .ok _ => false) = true := by rfl

#print axioms fuel_open_relation
#print axioms positive_width_bound
#print axioms arbitrary_width_block_parse
#print axioms arbitrary_width_statement_parse
#print axioms arbitrary_width_unchecked_parse
#print axioms closing_brace_preserves_else
#print axioms arbitrary_depth_relation
#print axioms arbitrary_depth_bound
#print axioms arbitrary_depth_block_parse
#print axioms empty_block_minimal
#print axioms zero_block_fuel_refuses
#print axioms zero_list_loop_refuses
end Solidity.Frontend.StatementGrammarH28
