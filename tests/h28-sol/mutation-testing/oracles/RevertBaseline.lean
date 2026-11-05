import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

/-! Independent known-kill baseline: a reverting diamond closes to false. -/
namespace H28.RevertBaseline
open Solidity

def C : Contract := { vars := [] }
def σ : State C [] := .init C
def statement : Stmt C [] [] := .revert
def intended : Premise C [] [] := .done false

/-- The original concrete rule instance. -/
theorem source_link : Taclet C 0 .diamond statement intended := .revertDiamond
/-- An inhabited concrete state. -/
theorem input_inhabited : Nonempty (State C []) := ⟨σ⟩
/-- The typed run independently reverts. -/
theorem reverting_run : statement.runR σ = .error .revert := by rfl

#print axioms source_link
#print axioms input_inhabited
#print axioms reverting_run
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @reverting_run
end H28.RevertBaseline
