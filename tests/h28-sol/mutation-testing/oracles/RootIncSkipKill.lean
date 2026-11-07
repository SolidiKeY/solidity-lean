import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

/-! A checked counterexample to `storageRootIncrement` with the `± 1` step
dropped (`save(storage, gsp, gsp)`).  The storage root `x` holds the uint256
maximum: the real checked `++x` reverts, while the mutant's update applies and
lands, so its premise admits a true diamond postcondition. -/
namespace H28.RootIncSkipKill
open Solidity

def xName : Name := String.singleton 'x'
def C : Contract := { vars := [(xName, .prim .uint)] }
def maximum : PrimTy.uint.Denote := ⟨Semantics.uintBound - 1, by decide +kernel⟩
def σ : State C [] := (State.init C).withStorage (.cons (.prim maximum) .nil)
def statement : Stmt C [] [] := .incDec .preInc rfl (.root xName rfl)
def update : Upd C [] [] := Upd.nil.snoc (UpdElem.storage
  (Tms.STerm.save Tms.STerm.storage (Tms.PTerm.root xName rfl)
    (Tms.SValT.val (Tms.Term.find Tms.STerm.storage (Tms.PTerm.root xName rfl)))))
def mutated : Premise C [] [] := .update update

/-- The actual mutated constructor, at an inhabited overflowing storage root. -/
theorem source_link : Taclet C 0 .diamond statement mutated := .storageRootIncrement

/-- The input root stores a valid maximum uint256 value. -/
theorem input_inhabited : Nonempty (State C []) := ⟨σ⟩

/-- Checked addition of one to the uint256 maximum reverts. -/
theorem overflowing_run : statement.runR σ = .error .revert := by with_unfolding_all rfl

/-- The mutant update succeeds and returns the unchanged globals: not vacuous. -/
theorem update_returns : update.globT σ = some σ.globG := by with_unfolding_all rfl

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
  with_unfolding_all change ¬ (THalt.revert = THalt.exhausted ∧ _)
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
#print axioms premise_accepts_true
#print axioms execution_rejects_true
#print axioms checked_kill
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @checked_kill
end H28.RootIncSkipKill
