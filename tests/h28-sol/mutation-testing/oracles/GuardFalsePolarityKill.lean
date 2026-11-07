import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

/-! A checked counterexample to a require rule whose revert guard is true.
The source_link theorem compiles only against that actual mutated constructor.
The premise admits a false postcondition on require(false), while the typed run
reverts and falsifies that postcondition. No production theorem is repaired. -/
namespace H28.GuardFalsePolarityKill
open Solidity

def C : Contract := { vars := [] }
def σ : State C [] := .init C
def statement : Stmt C [] [] := .require (.simple (.bool false))
def mutated : Premise C [] [] :=
  .split .capture (.isBool (.lit false) true) (.isBool (.lit false) true)
    .nil (.cons .revert .nil)

/-- This instance links the witness to the actual mutated production rule. -/
theorem source_link : Taclet C 0 .diamond statement mutated := .requireSimple

/-- A concrete inhabited input, not an assumed or empty relation. -/
theorem input_inhabited : Nonempty (State C []) := ⟨σ⟩

/-- Both mutant antecedents are false, so the mutant admits false. -/
theorem premise_accepts_false : holds σ (mutated.fml .diamond .nil .nil .ff) := by
  change (some false = some true → _) ∧ (some false = some true → _)
  constructor <;> intro h <;> cases h

/-- The real reverting execution cannot satisfy a false postcondition. -/
theorem execution_rejects_false :
    ¬ holds σ (.modal .diamond (.cons statement .nil) .nil .ff) := by
  change ¬ (THalt.revert = THalt.exhausted ∧ _)
  intro h
  cases h.1

/-- The linked mutated rule is semantically unsound at this inhabited input. -/
theorem checked_kill : ¬ Premise.Sound .diamond statement mutated σ := by
  intro h
  exact execution_rejects_false (h .nil .nil .ff premise_accepts_false)

#print axioms source_link
#print axioms input_inhabited
#print axioms premise_accepts_false
#print axioms execution_rejects_false
#print axioms checked_kill
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @checked_kill
end H28.GuardFalsePolarityKill
