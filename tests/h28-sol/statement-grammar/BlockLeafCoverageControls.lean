import Solidity.Frontend.StatementGrammarH28.BlockLeafCoverage

/-! Arbitrary-length and inhabited block/list fuel controls. The theorem
inputs use synthetic offset-zero locations, not a lexer/source certificate. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def repeatedReturns (k : SCtx) : Nat → Syn (.list (.item k))
  | 0 => .nil
  | n + 1 => .cons (.stmtItem (.returnStmt .none)) (repeatedReturns k n)

def returnWords : Nat → List Tok
  | 0 => []
  | n + 1 => .kw .return_ :: .punct .semi :: returnWords n

theorem repeated_returns_relation (k : SCtx) (n : Nat) :
    LeafItems (repeatedReturns k n) (returnWords n) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .returnCons ih

def mixedLeaves (u : Bool) : Syn (.list (.item ⟨true, u⟩)) :=
  .cons (.stmtItem (.returnStmt .none))
    (.cons (.stmtItem .breakStmt) (.cons (.stmtItem .continueStmt) .nil))

def mixedLeafWords : List Tok :=
  [.kw .return_, .punct .semi, .kw .break_, .punct .semi, .kw .continue_, .punct .semi]

theorem mixed_leaves_relation (u : Bool) : LeafItems (mixedLeaves u) mixedLeafWords :=
  .returnCons (.breakCons (.continueCons .nil))

def blockLeafSuffix : St := ⟨[atToken (.kw .else_) 80 84], [.attrs [.vis]], 90⟩

example (count : Nat) (k : SCtx) :
    block 4 k (blockInput (returnWords count) blockLeafSuffix) =
      .ok (Syn.block (repeatedReturns k count), blockLeafSuffix) :=
  leaf_block_coverage (repeated_returns_relation k count) 0 blockLeafSuffix

example : block 4 .body (blockInput (returnWords 80) blockLeafSuffix) =
    .ok (Syn.block (repeatedReturns .body 80), blockLeafSuffix) :=
  leaf_block_coverage (repeated_returns_relation .body 80) 0 blockLeafSuffix

example : block 4 ⟨true, false⟩ (blockInput mixedLeafWords blockLeafSuffix) =
    .ok (Syn.block (mixedLeaves false), blockLeafSuffix) :=
  leaf_block_coverage (mixed_leaves_relation false) 0 blockLeafSuffix

example : stmt 5 ⟨true, true⟩ (blockInput mixedLeafWords blockLeafSuffix) =
    .ok (Syn.blockStmt (Syn.block (mixedLeaves true)), blockLeafSuffix) :=
  leaf_block_stmt_coverage (mixed_leaves_relation true) 0 blockLeafSuffix

example : item 5 ⟨true, false⟩ (uncheckedInput mixedLeafWords blockLeafSuffix) =
    .ok (Syn.uncheckedItem (Syn.block (mixedLeaves true)), blockLeafSuffix) :=
  leaf_unchecked_coverage (mixed_leaves_relation true) 0 blockLeafSuffix

example : item 5 .body (uncheckedInput (returnWords 3) blockLeafSuffix) =
    .ok (Syn.uncheckedItem (Syn.block (repeatedReturns ⟨false, true⟩ 3)), blockLeafSuffix) :=
  leaf_unchecked_coverage (repeated_returns_relation ⟨false, true⟩ 3) 0 blockLeafSuffix

example (n : Nat) : item (n + 1) ⟨true, true⟩ (uncheckedInput mixedLeafWords blockLeafSuffix) =
    .error ⟨0, "nested unchecked block"⟩ := unchecked_nested_refused n true _ _

example (n count : Nat) (k : SCtx) :
    manyAux (blockLeafStep (n + 3) k) (itemCount (repeatedReturns k count))
      (leafInput (returnWords count) blockLeafSuffix) = .error ⟨0, "no progress"⟩ :=
  leaf_items_many_underfuel (repeated_returns_relation k count) n blockLeafSuffix

example : manyAux (blockLeafStep 3 ⟨true, false⟩) 3
    (leafInput mixedLeafWords blockLeafSuffix) = .error ⟨0, "no progress"⟩ := by
  simpa only [mixedLeaves, itemCount] using
    leaf_items_many_underfuel (mixed_leaves_relation false) 0 blockLeafSuffix

example (count : Nat) (k : SCtx) :
    (Syn.block (repeatedReturns k count)).toks [] = some (braces (returnWords count)) :=
  leaf_block_toks (repeated_returns_relation k count)

#print axioms repeated_returns_relation
#print axioms mixed_leaves_relation
end Solidity.Frontend.StatementGrammarH28
