import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

namespace H28.OverflowIncSkipKill
open Solidity

def C : Contract := { vars := [] }
def Γ : Ctx := [.val .uint]
def maximum : PrimTy.uint.Denote := ⟨Semantics.uintBound - 1, by decide +kernel⟩
def σ : State C Γ := (State.init C).push (t := .val .uint) maximum
def statement : Stmt C Γ Γ :=
  .incDec .preInc rfl (.local .here)
def update : Upd C Γ Γ := .snoc .nil (.local .here (.val (.pvV .here)))
def mutated : Premise C Γ Γ := .update update

/-- The actual constructor, at an inhabited overflowing unsigned input. -/
theorem source_link : Taclet C 0 .diamond statement mutated := .localIncrement
/-- The input local stores a valid maximum uint256 value. -/
theorem input_inhabited : Nonempty (State C Γ) := ⟨σ⟩
/-- Checked addition of one to uint256 maximum reverts. -/
theorem overflowing_run : statement.runR σ = .error .revert := by rfl

/-- The mutant update succeeds; this is not a vacuous failed-update premise. -/
theorem update_returns : update.globT σ = some σ.globG := by rfl

/-- An actual typed landing state confirms that update success is inhabited. -/
def after : State C Γ := σ

/-- The mutant really lands on its unchanged typed state. -/
theorem typed_landing : update.Lands σ σ.globG after := by
  apply Upd.lands_iff_applyV.mpr
  refine ⟨σ.locV.set .here maximum, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · intro t i
    cases i with
    | here => rfl
    | there i => nomatch i

/-- Its successful update admits a true postcondition. -/
theorem premise_accepts_true : holds σ (mutated.fml .diamond .nil .nil .tt) := by
  change update.afterT .diamond σ (fun _ => True)
  apply Upd.afterT_intro
  · intro h
    rw [update_returns] at h
    cases h
  · intro g τ h
    trivial

/-- The real overflowing execution cannot satisfy a diamond. -/
theorem execution_rejects_true :
    ¬ holds σ (.modal .diamond (.cons statement .nil) .nil .tt) := by
  change ¬ (THalt.revert = THalt.exhausted ∧ _)
  intro h
  cases h.1

/-- A source-linked, concrete semantic kill at the overflow boundary. -/
theorem checked_kill : ¬ Premise.Sound .diamond statement mutated σ := by
  intro h
  exact execution_rejects_true (h .nil .nil .tt premise_accepts_true)

#print axioms source_link
#print axioms input_inhabited
#print axioms overflowing_run
#print axioms update_returns
#print axioms typed_landing
#print axioms premise_accepts_true
#print axioms execution_rejects_true
#print axioms checked_kill
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @checked_kill
#check @typed_landing
end H28.OverflowIncSkipKill
