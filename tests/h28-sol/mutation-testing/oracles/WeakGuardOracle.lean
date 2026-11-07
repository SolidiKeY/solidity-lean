import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

/-! Deliberately incomplete observer for a runner false-pass self-test.
This oracle checks the real require run but does not constrain requireSimple's
premise. Its surviving guard mutation must stay visibly surviving even when
an independently checked regression witness proves it non-equivalent. -/
namespace H28.WeakGuardOracle
open Solidity

def C : Contract := { vars := [] }
def σ : State C [] := .init C
def statement : Stmt C [] [] := .require (.simple (.bool true))

/-- This unrelated rule remains linked; it cannot detect require mutations. -/
theorem source_link : Taclet C 0 .box (.revert : Stmt C [] []) (.done true) := .revertBox
/-- A concrete input for the real guard run. -/
theorem input_inhabited : Nonempty (State C []) := ⟨σ⟩
/-- The interpreter still executes the original program successfully. -/
theorem successful_run : statement.runR σ = .ok ⟨σ, List.prefix_refl _⟩ := by rfl

#print axioms source_link
#print axioms input_inhabited
#print axioms successful_run
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @successful_run
end H28.WeakGuardOracle
