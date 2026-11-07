import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

namespace H28.PopSkippedKill
open Solidity

def arrayName : Name := String.singleton 'a'
def C : Contract := { vars := [(arrayName, .ref (.array (.prim .uint)))] }
def path : SPath C [] (.array (.prim .uint)) := .loc (.root arrayName rfl)
def location : Loc C [] (.prim .uint) := .index (.arr .dyn) path (.simple (.lit 0 rfl))
def empty : State C [] := .init C
def populated : State C [] := empty.withStorage (.cons
  (.array (.cons (.prim ⟨7, rfl⟩) .nil) .nil (by decide +kernel)) .nil)
def σ (b : Bool) : State C [] := if b then populated else empty
def statement : Stmt C [] [] := .pop path
def update : Upd C [] [] := .snoc .nil (.storage Tms.STerm.storage)
def premise : Premise C [] [] := .update update

theorem source_link : Taclet C 0 .diamond statement premise := .storagePopSave (darr := path) rfl rfl

def afterPositive : State C [] := empty.withStorage (.cons (.array .nil (.cons (.prim ⟨0, rfl⟩) .nil) (by decide +kernel)) .nil)

theorem input_inhabited : ∀ _b : Bool, Nonempty (State C []) := fun b => ⟨σ b⟩
theorem failing_run : statement.runR empty = .error .revert := by with_unfolding_all rfl
theorem positive_run : statement.runR populated = .ok ⟨afterPositive, List.prefix_refl _⟩ := by with_unfolding_all rfl

theorem update_returns : ∀ b : Bool, update.globT (σ b) = some (σ b).globG := by
  intro b
  cases b <;> rfl

theorem typed_landing : ∀ b : Bool, update.Lands (σ b) (σ b).globG (σ b) := by
  intro b
  apply Upd.lands_iff_applyV.mpr
  refine ⟨(σ b).locV, ?_, ?_, ?_⟩
  · cases b <;> rfl
  · rfl
  · intro t i
    nomatch i

theorem premise_accepts_true : ∀ b : Bool, holds (σ b) (premise.fml .diamond .nil .nil .tt) := by
  intro b
  change update.afterT .diamond (σ b) (fun _ => True)
  apply Upd.afterT_intro
  · intro h
    rw [update_returns b] at h
    cases h
  · intro g τ h
    trivial

theorem execution_rejects_true :
    ¬ holds empty (.modal .diamond (.cons statement .nil) .nil .tt) := by
  with_unfolding_all change ¬ (THalt.revert = THalt.exhausted ∧ _)
  intro h
  cases h.1

theorem checked_kill : ¬ Premise.Sound .diamond statement premise empty := by
  intro h
  exact execution_rejects_true (h .nil .nil .tt (premise_accepts_true false))

#print axioms source_link
#print axioms input_inhabited
#print axioms failing_run
#print axioms positive_run
#print axioms update_returns
#print axioms typed_landing
#print axioms premise_accepts_true
#print axioms execution_rejects_true
#print axioms checked_kill
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @failing_run
#check @positive_run
#check @update_returns
#check @typed_landing
#check @premise_accepts_true
#check @execution_rejects_true
#check @checked_kill
end H28.PopSkippedKill
