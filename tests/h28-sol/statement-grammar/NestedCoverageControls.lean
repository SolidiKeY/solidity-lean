import Solidity.Frontend.StatementGrammarH28.NestedCoverage

/-! Universal arbitrary-depth and inhabited recursive mixed controls. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def towerItems (k : SCtx) : Nat → Syn (.list (.item k))
  | 0 => .nil
  | n + 1 => .cons (.stmtItem (.blockStmt (.block (towerItems k n)))) .nil

def towerTokens : Nat → List Tok
  | 0 => []
  | n + 1 => braces (towerTokens n)

theorem tower_nested (k : SCtx) (n : Nat) :
    NestedItems (towerItems k n) (towerTokens n) (n * 3) := by
  induction n with
  | zero => exact .nil
  | succ n ih =>
    simpa only [towerItems, towerTokens, Nat.max_zero, Nat.succ_mul, List.append_nil] using
      (NestedItems.blockCons ih (NestedItems.nil (k := k)))

theorem arbitrary_depth_block_coverage (k : SCtx) (n extra : Nat) (s : St) :
    block (extra + n * 3 + 4) k (blockInput (towerTokens n) s) =
      .ok (.block (towerItems k n), s) := nested_block_coverage (tower_nested k n) extra s

theorem arbitrary_depth_unchecked_coverage (l : Bool) (n extra : Nat) (s : St) :
    item (extra + n * 3 + 5) ⟨l, false⟩ (uncheckedInput (towerTokens n) s) =
      .ok (.uncheckedItem (.block (towerItems ⟨l, true⟩ n)), s) :=
  nested_unchecked_coverage (tower_nested ⟨l, true⟩ n) extra s

def recursiveMixed : Syn (.list (.item ⟨true, false⟩)) :=
  .cons (.stmtItem (.blockStmt (.block (.cons (.stmtItem (.returnStmt .none)) .nil))))
    (.cons (.uncheckedItem (.block
      (.cons (.stmtItem (.blockStmt (.block
        (.cons (.stmtItem .breakStmt) (.cons (.stmtItem .continueStmt) .nil))))) .nil))) .nil)

def recursiveMixedTokens : List Tok :=
  braces [.kw .return_, .punct .semi] ++
    (.kw .unchecked :: braces (braces [.kw .break_, .punct .semi, .kw .continue_, .punct .semi]))

theorem recursive_mixed_nested : NestedItems recursiveMixed recursiveMixedTokens 5 :=
  .blockCons (.returnCons .nil) (.uncheckedCons (.blockCons (.breakCons (.continueCons .nil)) .nil) .nil)

theorem recursive_mixed_parse (n : Nat) (s : St) :
    block (n + 9) ⟨true, false⟩ (blockInput recursiveMixedTokens s) =
      .ok (.block recursiveMixed, s) := nested_block_coverage recursive_mixed_nested n s

theorem recursive_mixed_yield (L : List Choice) :
    (Syn.block recursiveMixed).yield L = some ([braces recursiveMixedTokens], L) :=
  nested_block_yield recursive_mixed_nested L

theorem recursive_mixed_boundary (L : List Choice) :
    BlockBoundary (Syn.block recursiveMixed) L L recursiveMixedTokens :=
  nested_block_boundary recursive_mixed_nested L

theorem nested_unchecked_still_refused (n : Nat) (l : Bool) (depth : Nat) (s : St) :
    item (n + 1) ⟨l, true⟩ (uncheckedInput (towerTokens depth) s) =
      .error ⟨0, "nested unchecked block"⟩ := unchecked_nested_refused n l _ s

theorem one_nested_block_underfuel (k : SCtx) (s : St) :
    block 3 k (blockInput (towerTokens 1) s) = .error ⟨0, "nesting too deep"⟩ := by
  rfl

def suffixLayout : St :=
  ⟨[atToken (.kw .else_) 7 11], [.frags [2]], 15⟩

theorem recursive_mixed_suffix_layout :
    block 9 ⟨true, false⟩ (blockInput recursiveMixedTokens suffixLayout) =
      .ok (.block recursiveMixed, suffixLayout) := recursive_mixed_parse 0 suffixLayout

#print axioms tower_nested
#print axioms arbitrary_depth_block_coverage
#print axioms arbitrary_depth_unchecked_coverage
#print axioms recursive_mixed_nested
#print axioms recursive_mixed_parse
#print axioms recursive_mixed_yield
#print axioms recursive_mixed_boundary
#print axioms nested_unchecked_still_refused
#print axioms one_nested_block_underfuel
#print axioms recursive_mixed_suffix_layout
end Solidity.Frontend.StatementGrammarH28
