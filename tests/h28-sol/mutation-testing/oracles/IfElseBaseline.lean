import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

/-! Inhabited concrete instances of the production `ifElseSplit`: one `if`
whose condition is `true` and one whose condition is `false`, each with one
empty branch and one reverting branch, so the branches are not joinable. -/
namespace H28.IfElseBaseline
open Solidity

def C : Contract := { vars := [] }
def σ : State C [] := .init C
def stmtTrue : Stmt C [] [] := .ite (.simple (.bool true)) .nil (.cons .revert .nil)
def stmtFalse : Stmt C [] [] := .ite (.simple (.bool false)) (.cons .revert .nil) .nil
def intendedTrue : Premise C [] [] :=
  .split .block (.isBool (.lit true) true) (.isBool (.lit true) false) .nil (.cons .revert .nil)
def intendedFalse : Premise C [] [] :=
  .split .block (.isBool (.lit false) true) (.isBool (.lit false) false) (.cons .revert .nil) .nil

/-- `if (true) {} else { revert(); }` under both original polarities. -/
theorem source_link : Taclet C 0 .diamond stmtTrue intendedTrue := .ifElseSplit

/-- `if (false) { revert(); } else {}` under both original polarities. -/
theorem source_link_false : Taclet C 0 .diamond stmtFalse intendedFalse := .ifElseSplit

/-- The concrete typed input exists, rather than an empty relation. -/
theorem input_inhabited : Nonempty (State C []) := ⟨σ⟩

/-- Both runs take their empty branch and succeed, independently of the rule. -/
theorem runs_succeed : stmtTrue.runR σ = .ok ⟨σ, List.prefix_refl _⟩ ∧
    stmtFalse.runR σ = .ok ⟨σ, List.prefix_refl _⟩ := by
  constructor <;> rfl

#print axioms source_link
#print axioms source_link_false
#print axioms input_inhabited
#print axioms runs_succeed
set_option pp.fullNames true
#check @source_link
#check @source_link_false
#check @runs_succeed
end H28.IfElseBaseline
