import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

/-! An inhabited concrete require(false) instance of the production rule. -/
namespace H28.GuardFalseBaseline
open Solidity

def C : Contract := { vars := [] }
def σ : State C [] := .init C
def statement : Stmt C [] [] := .require (.simple (.bool false))
def intended : Premise C [] [] :=
  .split .capture (.isBool (.lit false) true) (.isBool (.lit false) false)
    .nil (.cons .revert .nil)

/-- `require(false)` uses both original branch polarities. -/
theorem source_link : Taclet C 0 .diamond statement intended := .requireSimple

/-- The concrete typed input exists, rather than an empty relation. -/
theorem input_inhabited : Nonempty (State C []) := ⟨σ⟩

/-- The interpreter's concrete reverting run is independent of the rule. -/
theorem reverting_run : statement.runR σ = .error .revert := by rfl

#print axioms source_link
#print axioms input_inhabited
#print axioms reverting_run
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @reverting_run
end H28.GuardFalseBaseline
