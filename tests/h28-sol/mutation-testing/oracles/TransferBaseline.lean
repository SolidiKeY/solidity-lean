import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

/-! An inhabited concrete instance of the production `transferNoCallbackBox`:
a funded `transfer` of 5 to address 9, booked as `pay(sadr, se)`. -/
namespace H28.TransferBaseline
open Solidity

def C : Contract := { vars := [] }
def start : State C [] := { State.init C with selfBalance := ⟨10, rfl⟩ }
def statement : Stmt C [] [] := .transfer (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl))
def intended : Premise C [] [] :=
  .update (Upd.nil.snoc (UpdElem.pay (Simple.lit 9 rfl).lower (Simple.lit 5 rfl).lower))

/-- The production rule books the amount written. -/
theorem source_link : Taclet C 0 .box statement intended :=
  .transferNoCallbackBox (sadr := .lit 9 rfl) (se := .lit 5 rfl)

/-- The concrete typed input exists, rather than an empty relation. -/
theorem input_inhabited : Nonempty (State C []) := ⟨start⟩

/-- The run, independent of the rule, pays 5 and leaves balance 5. -/
theorem actual_run : statement.runR start = .ok ⟨start.pay ⟨9, rfl⟩ 5, List.prefix_refl _⟩ ∧
    (start.pay ⟨9, rfl⟩ 5).selfBalance.1 = 5 := by
  constructor <;> with_unfolding_all rfl

#print axioms source_link
#print axioms input_inhabited
#print axioms actual_run
set_option pp.fullNames true
#check @source_link
#check @actual_run
end H28.TransferBaseline
