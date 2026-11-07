import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

/-! A checked counterexample to `ifElseSplit` with one branch guard flipped:
`if (false) { revert(); } else {}` against the mutant whose else-branch guard is `se = true`.
Both mutant antecedents are false at the taken condition, so the premise
admits a false diamond postcondition, while the typed run succeeds. -/
namespace H28.IfElsePolarityKill
open Solidity

def C : Contract := { vars := [] }
def σ : State C [] := .init C
def statement : Stmt C [] [] := .ite (.simple (.bool false)) (.cons .revert .nil) .nil
def mutated : Premise C [] [] :=
  .split .block (.isBool (.lit false) true) (.isBool (.lit false) true) (.cons .revert .nil) .nil

/-- This instance links the witness to the actual mutated production rule. -/
theorem source_link : Taclet C 0 .diamond statement mutated := .ifElseSplit (hj := rfl)

/-- A concrete inhabited input, not an assumed or empty relation. -/
theorem input_inhabited : Nonempty (State C []) := ⟨σ⟩

/-- The typed run takes the empty branch and succeeds. -/
theorem actual_run : statement.runR σ = .ok ⟨σ, List.prefix_refl _⟩ := by rfl

/-- Both mutant antecedents are false, so the mutant admits false. -/
theorem premise_accepts_false : holds σ (mutated.fml .diamond .nil .nil .ff) := by
  change (some false = some true → _) ∧ (some false = some true → _)
  constructor <;> intro h <;> cases h

/-- The real successful execution cannot satisfy a false postcondition. -/
theorem execution_rejects_false :
    ¬ holds σ (.modal .diamond (.cons statement .nil) .nil .ff) := by
  intro h
  exact h.1 trivial

/-- The linked mutated rule is semantically unsound at this inhabited input. -/
theorem checked_kill : ¬ Premise.Sound .diamond statement mutated σ := by
  intro h
  exact execution_rejects_false (h .nil .nil .ff premise_accepts_false)

#print axioms source_link
#print axioms input_inhabited
#print axioms actual_run
#print axioms premise_accepts_false
#print axioms execution_rejects_false
#print axioms checked_kill
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @checked_kill
end H28.IfElsePolarityKill
