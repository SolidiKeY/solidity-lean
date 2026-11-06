import Solidity.Frontend.StatementGrammarH28.FramedItemList
import Solidity.Source.Ctor

/-! Both item constructors have real successful yields and exact mixed block
segmentation controls; inner blocks contain unrestricted compound statements. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def itemFrameCtx : SCtx := ⟨true, false⟩

def mixedFramedItems : Syn (.list (.item itemFrameCtx)) :=
  .cons (.stmtItem (.simpleStmt (.exprStmt (.ident "x")))) (.cons (.uncheckedItem (.block (.cons (.stmtItem (.ifStmt (.ident "c") (.returnStmt .none) .none)) .nil))) (.cons (.stmtItem (.blockStmt (.block (.cons (.stmtItem (.tryStmt (.call (.ident "g") (.positional .nil)) .nil (.block .nil) (.catchPlain (.block .nil)) .nil)) .nil)))) (.cons (.stmtItem (.returnStmt (.some (.lit (.str [59,125]))))) (.cons (.stmtItem .continueStmt) (.cons (.stmtItem .breakStmt) (.cons (.stmtItem (.emit (.ident "E") (.positional .nil))) (.cons (.stmtItem (.revert (.ident "E") (.positional .nil))) (.nil))))))))

theorem mixed_items_inhabited : FramedItems mixedFramedItems := by
  simp only [mixedFramedItems, FramedItems_nil, FramedItems_cons,
    FramedItem_stmtItem, FramedItem_uncheckedItem, FramedStatement, root_simpleStmt, root_blockStmt, root_returnStmt, root_continueStmt,
    root_breakStmt, root_emit, root_revert, SemiRoot,
    or_true, true_or, and_true, true_and]

def mixedFramedItemTokens : List (List Tok) :=
  [[.ident "x", .punct .semi],
   [.kw .unchecked, .punct .lbrace, .kw .if_, .punct .lparen, .ident "c",
    .punct .rparen, .kw .return_, .punct .semi, .punct .rbrace],
   [.punct .lbrace, .kw .try_, .ident "g", .punct .lparen, .punct .rparen,
    .punct .lbrace, .punct .rbrace, .kw .catch_, .punct .lbrace, .punct .rbrace,
    .punct .rbrace],
   [.kw .return_, .str [59,125], .punct .semi],
   [.kw .continue_, .punct .semi], [.kw .break_, .punct .semi],
   [.kw .emit, .ident "E", .punct .lparen, .punct .rparen, .punct .semi],
   [.ident "revert", .ident "E", .punct .lparen, .punct .rparen, .punct .semi]]

theorem mixed_items_actual_yield :
    mixedFramedItems.yield [.frags [2], .attrs []] =
      some (mixedFramedItemTokens, [.attrs []]) := by decide +kernel

def actualItemCtors {k : SCtx} (xs : Syn (.list (.item k))) : List Ctor :=
  (g0ListValues xs).map (fun x => x.ctor)

theorem both_item_constructors_observed :
    (actualItemCtors mixedFramedItems).eraseDups = [.stmtItem, .uncheckedItem] := by
  simp only [actualItemCtors, mixedFramedItems, g0ListValues_nil, g0ListValues_cons,
    List.map_cons, List.map_nil]
  decide +kernel

theorem arbitrary_matching_item_segments {j : SCtx}
    (other : Syn (.list (.item j))) (L M : List Choice) (parts : List (List Tok))
    (hy : other.yield L = some (parts, M))
    (he : mixedFramedItemTokens.flatten = parts.flatten) :
    mixedFramedItemTokens = parts :=
  framed_item_list_split mixedFramedItems other mixed_items_inhabited
    [.frags [2], .attrs []] [.attrs []] L M mixedFramedItemTokens parts
    mixed_items_actual_yield hy he

theorem arbitrary_matching_block_segments {j : SCtx}
    (other : Syn (.list (.item j))) (L M : List Choice) (parts : List (List Tok))
    (rest tail : List Tok) (hy : other.yield L = some (parts, M))
    (he : braces mixedFramedItemTokens.flatten ++ rest = braces parts.flatten ++ tail) :
    mixedFramedItemTokens = parts ∧ rest = tail :=
  framed_block_item_segments mixedFramedItems other mixed_items_inhabited
    [.frags [2], .attrs []] [.attrs []] L M mixedFramedItemTokens parts rest tail
    mixed_items_actual_yield hy he

theorem unchecked_keyword_identifier_distinct :
    (Syn.stmtItem (Syn.simpleStmt (k := itemFrameCtx)
      (.exprStmt (.ident "unchecked")))).yield [] =
      some ([[.ident "unchecked", .punct .semi]], []) ∧
    (Syn.uncheckedItem (l := true) (.block .nil)).yield [] =
      some ([[.kw .unchecked, .punct .lbrace, .punct .rbrace]], []) ∧
    (.ident "unchecked" : Tok) ≠ .kw .unchecked := by decide +kernel

theorem do_while_item_not_in_source_fragment :
    ¬ FramedItem (Syn.stmtItem (Syn.doWhile (l := true) (u := false)
      (.returnStmt .none) (.lit (.bool true)))) := by
  intro h
  rcases h with h | h <;> cases h

#print axioms mixed_items_inhabited
#print axioms mixed_items_actual_yield
#print axioms both_item_constructors_observed
#print axioms arbitrary_matching_item_segments
#print axioms arbitrary_matching_block_segments
#print axioms unchecked_keyword_identifier_distinct
#print axioms do_while_item_not_in_source_fragment
end Solidity.Frontend.StatementGrammarH28
