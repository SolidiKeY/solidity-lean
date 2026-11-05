import Solidity.Frontend.StatementGrammarH28.FixtureData
import Solidity.Frontend.StatementGrammarH28.BlockLeafCoverage
import Solidity.Frontend.StatementGrammarH28.FramedItemList

/-! Unchanged public observer contracts and exact constructor equations.
The 45 existing case proofs remain the parser acceptance/refusal controls. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

#check fixtureListCtors
#check functionBodyCtors
#check topBodyCtors
#check fixtureBodyCtors
#check root
#check itemCount
#check itemsAsList
#check FramedStatement
#check FramedStatements
#check FramedItem
#check FramedItems

theorem g0_typed_list_empty_and_cons {c : Cat} (x : Syn c) (xs : Syn (.list c)) :
    g0ListCell (.cons x xs) = some (x,xs) ∧
    g0ListValues (.cons x xs) = x :: g0ListValues xs ∧
    g0ListLength (.cons x xs) = g0ListLength xs + 1 := ⟨rfl,rfl,rfl⟩

theorem g0_zero_fuel_still_empty {c : Cat} (f : Syn c → List Ctor) (xs : Syn (.list c)) :
    fixtureListCtors f 0 xs = [] := rfl

theorem g0_fuel_exhaustion_is_not_success :
    fixtureListCtors (fun e : Syn .expr => [e.ctor]) 0
      (.cons (.ident "x") (.cons (.ident "y") .nil)) = [] ∧
    fixtureListCtors (fun e : Syn .expr => [e.ctor]) 1
      (.cons (.ident "x") (.cons (.ident "y") .nil)) = [.ident] ∧
    fixtureListCtors (fun e : Syn .expr => [e.ctor]) 2
      (.cons (.ident "x") (.cons (.ident "y") .nil)) = [.ident,.ident] := by
  decide +kernel

def g0Function (name : String) : Syn (.part false) :=
  .function (.ident name) .nil .none .none .nil false .none .nil
    (.some (.block (.cons (.stmtItem (.returnStmt .none)) .nil)))

theorem g0_actual_function_body_and_name_refusal :
    functionBodyCtors (g0Function "f") =
      [.block,.cons,.stmtItem,.returnStmt,.none,.nil] ∧
    functionBodyCtors (g0Function "g") = [] := by decide +kernel

theorem g0_contract_and_unit_budget_identity
    (abstract : Bool) (name : String) (layout : Syn (.opt .expr))
    (bases : Syn (.list .inherit)) (parts : Syn (.list (.part false)))
    (tops : Syn (.list .top)) :
    topBodyCtors (.contract abstract name layout bases parts) =
      fixtureListCtors functionBodyCtors 64 parts ∧
    fixtureBodyCtors (.unit tops) = fixtureListCtors topBodyCtors 64 tops := ⟨rfl,rfl⟩

theorem g0_root_and_guards_keep_intrinsic_context {l u : Bool}
    (b : Syn (.stmt ⟨true,u⟩)) (c : Syn .expr) :
    root (Syn.doWhile (l := l) b c) = .doLoop ∧
    FramedStatements (Syn.nil (c := .stmt ⟨l,u⟩)) = True ∧
    FramedItems (Syn.nil (c := .item ⟨l,u⟩)) = True := ⟨rfl,rfl,rfl⟩

theorem g0_guard_cons_equations {k : SCtx} (s : Syn (.stmt k))
    (ss : Syn (.list (.stmt k))) (x : Syn (.item k)) (xs : Syn (.list (.item k))) :
    FramedStatements (.cons s ss) = (FramedStatement s ∧ FramedStatements ss) ∧
    FramedItems (.cons x xs) = (FramedItem x ∧ FramedItems xs) := ⟨rfl,rfl⟩

#print axioms g0_typed_list_empty_and_cons
#print axioms g0_zero_fuel_still_empty
#print axioms g0_fuel_exhaustion_is_not_success
#print axioms g0_actual_function_body_and_name_refusal
#print axioms g0_contract_and_unit_budget_identity
#print axioms g0_root_and_guards_keep_intrinsic_context
#print axioms g0_guard_cons_equations
end Solidity.Frontend.StatementGrammarH28
