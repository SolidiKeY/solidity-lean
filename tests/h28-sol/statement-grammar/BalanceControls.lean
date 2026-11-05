import Solidity.Frontend.StatementGrammarH28.Balance

/-! Nonempty intrinsic block boundaries and nested/negative token controls. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def returnTokens : List Tok := [.kw .return_, .punct .semi]

theorem return_tokens_balanced : BraceBalanced returnTokens :=
  .append (.token (.kw .return_) (by decide) (by decide))
    (.token (.punct .semi) (by decide) (by decide))

def returnBlock (k : SCtx) : Syn (.block k) :=
  .block (.cons (.stmtItem (.returnStmt .none)) .nil)

theorem return_block_boundary (k : SCtx) (L : List Choice) :
    BlockBoundary (returnBlock k) L L returnTokens := ⟨rfl, return_tokens_balanced⟩

def nestedReturnBlock (k : SCtx) : Syn (.block k) :=
  .block (.cons (.stmtItem (.blockStmt (returnBlock k))) .nil)

theorem nested_return_boundary (k : SCtx) (L : List Choice) :
    BlockBoundary (nestedReturnBlock k) L L (braces returnTokens) :=
  ⟨rfl, .wrap return_tokens_balanced⟩

def uncheckedEmptyBlock (l : Bool) : Syn (.block ⟨l, false⟩) :=
  .block (.cons (.uncheckedItem (.block .nil)) .nil)

theorem unchecked_empty_boundary (l : Bool) (L : List Choice) :
    BlockBoundary (uncheckedEmptyBlock l) L L
      ([.kw .unchecked] ++ braces []) :=
  ⟨rfl, .append (.token (.kw .unchecked) (by decide) (by decide)) (.wrap .empty)⟩

example (suffix : List Tok) :
    closeSuffix 0 (braces returnTokens ++ (.punct .rbrace :: suffix)) = some suffix :=
  close_after_balanced (.wrap return_tokens_balanced) suffix

/-- Equal counts are insufficient: an early closing brace is still invalid. -/
theorem early_close_not_balanced :
    ¬ BraceBalanced [.punct .rbrace, .punct .lbrace] := by
  intro h
  have bad : some ([.punct .lbrace] : List Tok) = none := balanced_scan_frame h 0 []
  cases bad

example {xs ys suffix rest : List Tok}
    (hx : BraceBalanced xs) (hy : BraceBalanced ys)
    (h : braces xs ++ suffix = braces ys ++ rest) : xs = ys ∧ suffix = rest :=
  balanced_braced_split hx hy h

example (xss yss : List (List Tok))
    (hx : ∀ xs ∈ xss, BraceBalanced xs) (hy : ∀ ys ∈ yss, BraceBalanced ys)
    (h : (xss.map braces).flatten = (yss.map braces).flatten) : xss = yss :=
  balanced_braced_list_unique xss yss hx hy h

#print axioms return_tokens_balanced
#print axioms return_block_boundary
#print axioms nested_return_boundary
#print axioms unchecked_empty_boundary
#print axioms early_close_not_balanced
end Solidity.Frontend.StatementGrammarH28
