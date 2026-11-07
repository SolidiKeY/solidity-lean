import Solidity.Frontend.StatementGrammarH28.NestedUnique

/-! Inhabited actual derivations and universal negative uniqueness controls. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def returnItems : Syn (.list (.item ⟨true, false⟩)) :=
  .cons (.stmtItem (.returnStmt .none)) .nil

def breakItems : Syn (.list (.item ⟨true, false⟩)) :=
  .cons (.stmtItem .breakStmt) .nil

def uniqueNestedItems : Syn (.list (.item ⟨true, false⟩)) :=
  .cons (.stmtItem (.blockStmt (.block returnItems)))
    (.cons (.uncheckedItem (.block (.cons (.stmtItem .continueStmt) .nil))) .nil)

def uniqueNestedTokens : List Tok :=
  braces [.kw .return_, .punct .semi] ++
    (.kw .unchecked :: braces [.kw .continue_, .punct .semi])

theorem return_items_relation : NestedItems returnItems [.kw .return_, .punct .semi] 0 :=
  .returnCons .nil

theorem break_items_relation : NestedItems breakItems [.kw .break_, .punct .semi] 0 :=
  .breakCons .nil

theorem unique_nested_relation : NestedItems uniqueNestedItems uniqueNestedTokens 3 :=
  .blockCons (.returnCons .nil) (.uncheckedCons (.continueCons .nil) .nil)

theorem unique_nested_positive :
    (Syn.block uniqueNestedItems).Derives (braces uniqueNestedTokens) :=
  ⟨[], nested_block_toks unique_nested_relation⟩

/-- Any represented tree deriving this inhabited example's tokens is exactly
that example. Both the positive derivation and universal uniqueness check. -/
theorem unique_nested_control {ys : Syn (.list (.item ⟨true, false⟩))}
    {us : List Tok} {e : Nat} (hy : NestedItems ys us e)
    (dy : (Syn.block ys).Derives (braces uniqueNestedTokens)) : ys = uniqueNestedItems :=
  nested_block_yield_unique hy unique_nested_relation dy unique_nested_positive

theorem return_break_positive :
    (Syn.block returnItems).Derives (braces [.kw .return_, .punct .semi]) ∧
    (Syn.block breakItems).Derives (braces [.kw .break_, .punct .semi]) :=
  ⟨⟨[], nested_block_toks return_items_relation⟩,
   ⟨[], nested_block_toks break_items_relation⟩⟩

theorem return_break_no_common_yield (words : List Tok) :
    ¬ ((Syn.block returnItems).Derives words ∧ (Syn.block breakItems).Derives words) := by
  intro ⟨dr, db⟩
  have trees := nested_block_yield_unique return_items_relation break_items_relation dr db
  cases trees

theorem distinct_layouts_same_yield_segments :
    (Syn.block uniqueNestedItems).yield [] = some ([braces uniqueNestedTokens], []) ∧
    (Syn.block uniqueNestedItems).yield [.frags [2]] =
      some ([braces uniqueNestedTokens], [.frags [2]]) :=
  ⟨nested_block_yield unique_nested_relation [], nested_block_yield unique_nested_relation _⟩

theorem nested_prefix_suffix_control {ys : Syn (.list (.item ⟨true, false⟩))}
    {us tail : List Tok} {e : Nat} (hy : NestedItems ys us e)
    (he : braces uniqueNestedTokens ++ [.kw .else_] = braces us ++ tail) :
    uniqueNestedItems = ys ∧ [.kw .else_] = tail :=
  nested_block_prefix_unique unique_nested_relation hy he

/-- Residual layout is preserved by yield but prevents toks success. -/
theorem nonempty_layout_toks_none :
    (Syn.block uniqueNestedItems).toks [.frags [2]] = none := by
  unfold Syn.toks
  rw [nested_block_yield unique_nested_relation]

#print axioms nonempty_layout_toks_none
#print axioms return_items_relation
#print axioms break_items_relation
#print axioms unique_nested_relation
#print axioms unique_nested_positive
#print axioms unique_nested_control
#print axioms return_break_positive
#print axioms return_break_no_common_yield
#print axioms distinct_layouts_same_yield_segments
#print axioms nested_prefix_suffix_control
end Solidity.Frontend.StatementGrammarH28
