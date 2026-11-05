import Solidity.Frontend.StatementGrammarH28.ConditionalList

/-! Arbitrary-width positive and inhabited negative intrinsic list controls. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def openListHead (k : SCtx) : Syn (.stmt k) :=
  .ifStmt (.lit (.bool true)) (.blockStmt (.block .nil)) .none

def openListWords : List Tok :=
  [.kw .if_, .punct .lparen, .bool true, .punct .rparen, .punct .lbrace, .punct .rbrace]

theorem open_list_head_relation (k : SCtx) : BooleanStatements (openListHead k) openListWords 1 :=
  .ifNone (.loops (.block .nil))

def wideList (k : SCtx) : Nat → Syn (.list (.item k))
  | 0 => .nil
  | n + 1 => .cons (.stmtItem (openListHead k)) (wideList k n)

def wideParts : Nat → List (List Tok)
  | 0 => []
  | n + 1 => openListWords :: wideParts n

theorem arbitrary_width_relation (k : SCtx) (n : Nat) :
    BooleanItemList (wideList k n) (wideParts n) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .cons (open_list_head_relation k) ih

theorem arbitrary_width_actual_yield (k : SCtx) (n : Nat) (L : List Choice) :
    (wideList k n).yield L = some (wideParts n, L) :=
  boolean_item_list_yield (arbitrary_width_relation k n) L

theorem arbitrary_width_block_yield (k : SCtx) (n : Nat) (L : List Choice) :
    (Syn.block (wideList k n)).yield L = some ([braces (wideParts n).flatten], L) :=
  boolean_item_block_yield (arbitrary_width_relation k n) L

theorem arbitrary_width_block_split (k : SCtx) (n : Nat)
    {ys : Syn (.list (.item k))} {qs : List (List Tok)} {rest tail : List Tok}
    (hy : BooleanItemList ys qs)
    (he : braces (wideParts n).flatten ++ rest = braces qs.flatten ++ tail) :
    wideList k n = ys ∧ wideParts n = qs ∧ rest = tail :=
  boolean_item_block_prefix_unique (arbitrary_width_relation k n) hy he

theorem arbitrary_width_actual_unique (k : SCtx) (n : Nat)
    {ys : Syn (.list (.item k))} {qs : List (List Tok)}
    (hy : BooleanItemList ys qs) (dy : ys.Derives (wideParts n).flatten) :
    wideList k n = ys ∧ wideParts n = qs :=
  boolean_item_list_yield_unique (arbitrary_width_relation k n) hy
    ((boolean_item_list_derives_iff (arbitrary_width_relation k n) _).mpr rfl) dy

theorem no_else_only_list (k : SCtx) (xs : Syn (.list (.item k))) :
    ¬ BooleanItemList xs [[.kw .else_]] := by
  intro h
  have bad := boolean_item_list_no_else h (⟨[], [], 0⟩ : St) (by intro bad; cases bad)
  exact bad rfl

theorem no_empty_statement_segment {k : SCtx} (x : Syn (.stmt k))
    (xs : Syn (.list (.item k))) (parts : List (List Tok)) :
    ¬ BooleanItemList (.cons (.stmtItem x) xs) ([] :: parts) := by
  intro h
  cases h with
  | cons hh ht => exact boolean_statement_tokens_nonempty hh rfl

theorem next_if_supplies_frame (k : SCtx) (s : St) :
    StatementFrame (openListHead k) (locatedInput openListWords s) :=
  Or.inr (boolean_statement_no_else_input (open_list_head_relation k) s)

#print axioms open_list_head_relation
#print axioms arbitrary_width_relation
#print axioms arbitrary_width_actual_yield
#print axioms arbitrary_width_block_yield
#print axioms arbitrary_width_block_split
#print axioms arbitrary_width_actual_unique
#print axioms no_else_only_list
#print axioms no_empty_statement_segment
#print axioms next_if_supplies_frame
end Solidity.Frontend.StatementGrammarH28
