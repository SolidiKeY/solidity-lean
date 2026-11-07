import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

/-! An inhabited concrete instance of the production `binopAssignment` at
`⊕ = /`: `v = 1 / 0;` updates `v` to `1 / 0`, which, like the run, fails. -/
namespace H28.DivAssignBaseline
open Solidity

def C : Contract := { vars := [] }
def Γ : Ctx := [.val .uint]
def start : State C Γ := (State.init C).push (t := .val .uint) ⟨9, rfl⟩
def statement : Stmt C Γ Γ :=
  .assignLocal .here (.binop .div rfl rfl (.simple (.lit 1 rfl)) (.simple (.lit 0 rfl)))
def update : Upd C Γ Γ := .snoc .nil (.local .here (.val
  (Tms.Term.binopS .div rfl rfl (Simple.lit (C := C) (Γ := Γ) 1 rfl).lower (Simple.lit 0 rfl).lower)))
def intended : Premise C Γ Γ := .update update

/-- The production rule has this premise. -/
theorem source_link : Taclet C 0 .diamond statement intended := .binopAssignment

theorem input_inhabited : Nonempty (State C Γ) := ⟨start⟩

/-- The run reverts on the zero divisor. -/
theorem actual_run : statement.runR start = .error .revert := by with_unfolding_all rfl

/-- So does the production update. -/
theorem update_fails : update.globT start = none := by with_unfolding_all rfl

#print axioms source_link
#print axioms input_inhabited
#print axioms actual_run
#print axioms update_fails
set_option pp.fullNames true
#check @source_link
#check @actual_run
end H28.DivAssignBaseline
