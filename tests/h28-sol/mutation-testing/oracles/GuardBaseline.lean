import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

/-! An inhabited concrete require(true) instance of the production rule. -/
namespace H28.GuardBaseline
open Solidity

def C : Contract := { vars := [] }
def σ : State C [] := .init C
def statement : Stmt C [] [] := .require (.simple (.bool true))
def intended : Premise C [] [] :=
  .split .capture (.isBool (.lit true) true) (.isBool (.lit true) false)
    .nil (.cons .revert .nil)

/-- `require(true)` uses both original branch polarities. -/
theorem source_link : Taclet C 0 .diamond statement intended := .requireSimple

/-- The concrete typed input exists, rather than an empty relation. -/
theorem input_inhabited : Nonempty (State C []) := ⟨σ⟩

/-- The interpreter's concrete successful run is independent of the rule. -/
theorem successful_run : statement.runR σ = .ok ⟨σ, List.prefix_refl _⟩ := by rfl

#print axioms source_link
#print axioms input_inhabited
#print axioms successful_run
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @successful_run
end H28.GuardBaseline
