import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

/-! An inhabited concrete instance of the production `LeanTaclet.transferDiamond`
(closes to `false`) at an unfunded transfer, which really reverts. -/
namespace H28.TransferDiamondBaseline
open Solidity

def C : Contract := { vars := [] }
def σ : State C [] := State.init C
def statement : Stmt C [] [] := .transfer (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl))
def intended : Premise C [] [] := .done false

/-- The production rule closes the diamond to `false`. -/
theorem source_link : LeanTaclet C 0 .diamond statement intended :=
  .transferDiamond (sadr := .lit 9 rfl) (se := .lit 5 rfl)

/-- The concrete typed input exists, rather than an empty relation. -/
theorem input_inhabited : Nonempty (State C []) := ⟨σ⟩

/-- The unfunded transfer reverts, independently of the rule. -/
theorem reverting_run : statement.runR σ = .error .revert := by with_unfolding_all rfl

#print axioms source_link
#print axioms input_inhabited
#print axioms reverting_run
set_option pp.fullNames true
#check @source_link
#check @reverting_run
end H28.TransferDiamondBaseline
