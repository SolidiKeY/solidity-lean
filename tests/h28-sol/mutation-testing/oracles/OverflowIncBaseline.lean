import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

namespace H28.OverflowIncBaseline
open Solidity

def C : Contract := { vars := [] }
def Γ : Ctx := [.val .uint]
def maximum : PrimTy.uint.Denote := ⟨Semantics.uintBound - 1, by decide +kernel⟩
def σ : State C Γ := (State.init C).push (t := .val .uint) maximum
def statement : Stmt C Γ Γ :=
  .incDec .preInc rfl (.local .here)
def update : Upd C Γ Γ := .snoc .nil (.local .here (.val
  (.app2 (.binop .add rfl) (.pvV .here) (.app0 (.lit (p := .uint) ⟨1, rfl⟩)))))
def intended : Premise C Γ Γ := .update update

/-- The actual constructor, at an inhabited overflowing unsigned input. -/
theorem source_link : Taclet C 0 .diamond statement intended := .localIncrement
/-- The input local stores a valid maximum uint256 value. -/
theorem input_inhabited : Nonempty (State C Γ) := ⟨σ⟩
/-- Checked addition of one to uint256 maximum reverts. -/
theorem overflowing_run : statement.runR σ = .error .revert := by rfl

#print axioms source_link
#print axioms input_inhabited
#print axioms overflowing_run
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @overflowing_run
end H28.OverflowIncBaseline
