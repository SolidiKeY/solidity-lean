import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

/-! A checked counterexample to a require rule whose success guard is false.
The source_link theorem compiles only against that actual mutated constructor.
The premise admits a false postcondition on require(true), while the typed run
succeeds and falsifies that postcondition. No production theorem is repaired. -/
namespace H28.GuardTruePolarityKill
open Solidity

def C : Contract := { vars := [] }
def σ : State C [] := .init C
def statement : Stmt C [] [] := .require (.simple (.bool true))
def mutated : Premise C [] [] :=
  .split .capture (.isBool (.lit true) false) (.isBool (.lit true) false)
    .nil (.cons .revert .nil)

/-- This instance links the witness to the actual mutated production rule. -/
theorem source_link : Taclet C 0 .diamond statement mutated := .requireSimple

/-- A concrete inhabited input, not an assumed or empty relation. -/
theorem input_inhabited : Nonempty (State C []) := ⟨σ⟩

/-- Both mutant antecedents are false, so the mutant admits false. -/
theorem premise_accepts_false : holds σ (mutated.fml .diamond .nil .nil .ff) := by
  change (some true = some false → _) ∧ (some true = some false → _)
  constructor <;> intro h <;> cases h

/-- The real successful execution cannot satisfy a false postcondition. -/
theorem execution_rejects_false :
    ¬ holds σ (.modal .diamond (.cons statement .nil) .nil .ff) := by
  change ¬ ((True → False) ∧ _)
  intro h
  exact h.1 trivial

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
end H28.GuardTruePolarityKill
