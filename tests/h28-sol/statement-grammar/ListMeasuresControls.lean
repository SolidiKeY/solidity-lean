import Solidity.Frontend.StatementGrammarH28.ListMeasures
import Solidity.Source.Ctor

namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def measureStatements : List (Syn (.stmt ⟨true, false⟩)) :=
  [.blockStmt (.block .nil), .simpleStmt (.exprStmt (.ident "x")),
   .ifStmt (.ident "c") (.returnStmt .none) (.some (.returnStmt .none)),
   .forStmt .none .none .none (.blockStmt (.block .nil)),
   .whileStmt (.ident "c") (.breakStmt),
   .doWhile (.continueStmt) (.ident "c"), .continueStmt, .breakStmt,
   .tryStmt (.ident "f") .nil (.block .nil) (.catchPlain (.block .nil)) .nil,
   .returnStmt (.some (.ident "x")), .emit (.ident "E") (.positional .nil),
   .revert (.ident "E") (.positional .nil), .assembly false [] .nil]

def measureStatementList : Syn (.list (.stmt ⟨true,false⟩)) :=
  measureStatements.foldr Syn.cons .nil

def measureItemList : Syn (.list (.item ⟨true,false⟩)) :=
  measureStatements.foldr (fun s rest => .cons (.stmtItem s) rest)
    (.cons (.uncheckedItem (.block .nil)) .nil)

def measureCheck {c : Cat} (xs : Syn (.list c)) (L : List Choice) : Bool :=
  match xs.yield L with
  | some (parts, []) => parts.length == g0ListLength xs &&
      decide (g0ListLength xs ≤ parts.flatten.length) &&
      parts.all (fun ts => !ts.isEmpty)
  | _ => false

theorem measure_all_statement_constructor_inventory :
    measureStatements.map Syn.ctor =
      [.blockStmt, .simpleStmt, .ifStmt, .forStmt, .whileStmt, .doWhile,
       .continueStmt, .breakStmt, .tryStmt, .returnStmt, .emit, .revert, .assembly] := rfl

theorem measure_all_statement_item_constructors_inhabited :
    g0ListLength measureStatementList = 13 ∧ measureCheck measureStatementList [] = true ∧
    g0ListLength measureItemList = 14 ∧ measureCheck measureItemList [] = true := by
  decide +kernel

def measureLayoutItems : Syn (.list (.item .body)) :=
  .cons (.stmtItem (.simpleStmt (.declVar
    (.varDecl (.fnType .nil (.some .internal) (.some .view) .nil) .none "fp") .none)))
  (.cons (.stmtItem (.returnStmt (.some (.lit (.str [101,108,115,101]))))) .nil)

theorem measure_fragment_attribute_layout_is_not_element_count :
    measureCheck measureLayoutItems [.attrs [.mutab, .vis], .frags [1,3]] = true ∧
    g0ListLength measureLayoutItems = 2 := by decide +kernel

theorem measure_failed_layout_is_not_success :
    measureLayoutItems.yield [] = none ∧
    measureCheck measureLayoutItems [] = false := by decide +kernel

def measureWideItems : Nat → Syn (.list (.item .body))
  | 0 => .nil
  | n + 1 => .cons (.stmtItem (.returnStmt .none)) (measureWideItems n)

theorem measure_arbitrary_width_count (n : Nat) : g0ListLength (measureWideItems n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change g0ListLength (measureWideItems n) + 1 = n + 1
    rw [ih]

theorem measure_arbitrary_width_yield (n : Nat) (L : List Choice) :
    (measureWideItems n).yield L = some (List.replicate n [.kw .return_, .punct .semi], L) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact list_yield_cons_of (.stmtItem (.returnStmt .none)) (measureWideItems n)
      L L L [[.kw .return_, .punct .semi]]
      (List.replicate n [.kw .return_, .punct .semi]) rfl ih

theorem measure_arbitrary_width_actual_budget (n : Nat) (L : List Choice) (s : St) :
    n + 1 ≤ (locatedInput (List.replicate n [.kw .return_, .punct .semi]).flatten s).ts.length + 1 := by
  have h := item_list_many_iteration_budget (measureWideItems n) L L _
    (measure_arbitrary_width_yield n L) s
  rw [measure_arbitrary_width_count] at h
  exact h

theorem measure_empty_lists_and_one_stop :
    measureCheck (Syn.nil (c := .stmt .body)) [] = true ∧
    measureCheck (Syn.nil (c := .item .body)) [] = true ∧
    g0ListLength (Syn.nil (c := .item .body)) + 1 = 1 := by decide +kernel

/-- Generic lists may contain present elements with empty yields. The generic
nonempty-element premise is therefore necessary; it is not silently omitted. -/
theorem measure_generic_empty_element_counterexample :
    (Syn.cons (Syn.none (c := .expr)) .nil).yield [] = some ([[]], []) ∧
    g0ListLength (Syn.cons (Syn.none (c := .expr)) .nil) = 1 ∧
    ([[]] : List (List Tok)).flatten.length = 0 := by decide +kernel

theorem measure_list_closure_preserves_empty_chunk :
    measureCheck (Syn.cons (Syn.none (c := .expr)) .nil) [] = false := by decide +kernel

#print axioms measure_all_statement_constructor_inventory
#print axioms measure_all_statement_item_constructors_inhabited
#print axioms measure_fragment_attribute_layout_is_not_element_count
#print axioms measure_failed_layout_is_not_success
#print axioms measure_arbitrary_width_count
#print axioms measure_arbitrary_width_yield
#print axioms measure_arbitrary_width_actual_budget
#print axioms measure_empty_lists_and_one_stop
#print axioms measure_generic_empty_element_counterexample
#print axioms measure_list_closure_preserves_empty_chunk
end Solidity.Frontend.StatementGrammarH28
