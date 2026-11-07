import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

/-! A checked counterexample to `LeanTaclet.transferDiamond` closing to `true`
instead of `false`.  An unfunded `transfer` of 5 (balance 0) really reverts,
so no diamond formula holds of it, while the mutant's premise is `true`. -/
namespace H28.TransferDiamondTrueKill
open Solidity

def C : Contract := { vars := [] }
def σ : State C [] := State.init C
def statement : Stmt C [] [] := .transfer (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl))
def mutated : Premise C [] [] := .done true

/-- This instance links the witness to the actual mutated production rule. -/
theorem source_link : LeanTaclet C 0 .diamond statement mutated :=
  .transferDiamond (sadr := .lit 9 rfl) (se := .lit 5 rfl)

/-- A concrete inhabited input, not an assumed or empty relation. -/
theorem input_inhabited : Nonempty (State C []) := ⟨σ⟩

/-- The unfunded transfer reverts. -/
theorem reverting_run : statement.runR σ = .error .revert := by with_unfolding_all rfl

/-- The mutant premise is `true`, so it admits a true postcondition. -/
theorem premise_accepts_true : holds σ (mutated.fml .diamond .nil .nil .tt) := trivial

/-- The real reverting execution cannot satisfy a diamond. -/
theorem execution_rejects_true :
    ¬ holds σ (.modal .diamond (.cons statement .nil) .nil .tt) := by
  with_unfolding_all change ¬ (THalt.revert = THalt.exhausted ∧ _)
  intro h
  cases h.1

/-- The linked mutated rule is semantically unsound at this inhabited input. -/
theorem checked_kill : ¬ Premise.Sound .diamond statement mutated σ := by
  intro h
  exact execution_rejects_true (h .nil .nil .tt premise_accepts_true)

#print axioms source_link
#print axioms input_inhabited
#print axioms reverting_run
#print axioms premise_accepts_true
#print axioms execution_rejects_true
#print axioms checked_kill
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @checked_kill
end H28.TransferDiamondTrueKill
