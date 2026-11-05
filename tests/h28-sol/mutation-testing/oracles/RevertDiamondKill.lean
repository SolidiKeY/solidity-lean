import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

/-! Independent source-linked known-kill control, distinct from guard edits. -/
namespace H28.RevertDiamondKill
open Solidity

def C : Contract := { vars := [] }
def σ : State C [] := .init C
def statement : Stmt C [] [] := .revert
def mutated : Premise C [] [] := .done true

/-- The actual mutated constructor must expose done(true). -/
theorem source_link : Taclet C 0 .diamond statement mutated := .revertDiamond
/-- The counterexample is inhabited. -/
theorem input_inhabited : Nonempty (State C []) := ⟨σ⟩
/-- The mutant closes even with a false postcondition. -/
theorem premise_accepts_false : holds σ (mutated.fml .diamond .nil .nil .ff) := by
  change True
  trivial
/-- The real revert cannot satisfy the diamond. -/
theorem execution_rejects_false :
    ¬ holds σ (.modal .diamond (.cons statement .nil) .nil .ff) := by
  change ¬ (THalt.revert = THalt.exhausted ∧ _)
  intro h
  cases h.1
/-- A checked semantic kill, not just an expected compiler error. -/
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
end H28.RevertDiamondKill
