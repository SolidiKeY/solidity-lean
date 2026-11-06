import Solidity.Examples.Tactics.ExternalTryFormula
import Solidity.Frontend.Problems

/-!
# The original source domain does not admit a universal try witness family

This countermodel uses the actual parameter-free source precondition builder,
including the 160-bit self-address bound, and the original well-formed-storage
premise. No oracle existence or successful-decoding premise is added. A missing
entry at the nonzero receiver 7 prevents a normal witness. The callback reading
has its independent unconditional caller-revert obstruction even with an oracle.
-/

namespace Solidity.Examples.Tactics.ExternalTryUniversal
open ExternalTryWitness ExternalTryFormula
local instance : InContract := ⟨Probe⟩
open scoped Scoped

/-- Exactly the call premise generated for a parameter-free nonpayable body
that does not read msg.value; source inputs still bound address(this). -/
def sourcePre : Fml Probe [] :=
  Frontend.Problem.callPre Probe [] false [] false [] true

/-- Both original source premises, with no oracle restriction. -/
def Admissible (σ : State Probe []) : Prop :=
  holds σ sourcePre ∧ holds σ (Fml.wt Probe)

/-- The original parameter-free source-obligation shape: the call premise and
`Problem.fml`'s well-formed-storage premise, diamond and postcondition true. -/
def sourceProblem : Fml Probe [] :=
  dl!{ ‹sourcePre› → ‹Problem.fml .diamond [] probe› }

/-- The exact proposed normal family, quantified over every original admissible
state. Its final states retain their intrinsic contract and local context. -/
def NormalSourceFamily : Prop :=
  ∀ σ : State Probe [], Admissible σ →
    ∃ τ : State Probe [], Prog.runFrames σ probe .nil = .ok τ

/-- Empty oracle, nonzero receiver 7: this state is genuinely source-admissible. -/
theorem empty_oracle_admissible : Admissible (State.init Probe) := by
  constructor
  · rfl
  · exact initStorage_wt

/-- A successful concrete oracle is also admitted; the precondition has not
been tailored to the failure countermodel. -/
theorem successful_oracle_admissible : Admissible (input (.ok [⟨9, rfl⟩])) := by
  constructor
  · rfl
  · apply holds_wt.mpr
    exact holds_wt.mp (initStorage_wt (C := Probe))

/-- The requested family is false under the unchanged original assumptions. -/
theorem no_normal_source_family : ¬ NormalSourceFamily := by
  intro h
  obtain ⟨τ, hw⟩ := h (State.init Probe) empty_oracle_admissible
  exact missing_refused τ hw

/-- Even the deterministic universal source obligation is false: the original
admissible domain includes a caller revert before any catch is reached. -/
theorem deterministic_source_refused : ¬ Fml.Valid sourceProblem := by
  intro h
  have hs := h (State.init Probe)
  change holds (State.init Probe) sourcePre → holds (State.init Probe) (Fml.wt Probe) →
    holds (State.init Probe) (.modal .diamond probe .nil .tt) at hs
  have hm := hs empty_oracle_admissible.1 empty_oracle_admissible.2
  change Modality.afterRunTR .diamond (holds · (.tt : Fml Probe []))
    (Prog.runFrames (State.init Probe) probe .nil) at hm
  have hr : Prog.runFrames (State.init Probe) probe .nil = .error .revert := rfl
  rw [hr] at hm
  cases hm.1

/-- The original source callback obligation is independently false for every
invariant and either payment flag, not merely because the oracle is missing. -/
theorem callback_source_refused (I : Invariant Probe) (pay : Bool) :
    ¬ ValidC I sourceProblem pay := by
  intro h
  have hs := h (State.init Probe)
  change holdsC I.fml pay (State.init Probe) sourcePre →
    holdsC I.fml pay (State.init Probe) (Fml.wt Probe) →
    holdsC I.fml pay (State.init Probe) (.modal .diamond probe .nil .tt) at hs
  have hp : holdsC I.fml pay (State.init Probe) sourcePre :=
    (holdsC_iff_holds sourcePre (by rfl) (State.init Probe)).2 empty_oracle_admissible.1
  have no : ¬ holdsC I.fml pay (State.init Probe) (.modal .diamond probe .nil .tt) := by
    apply Counterexamples.DiamondTry.callback_diamond_false
  exact no (hs hp initStorage_wt)

/-- In particular neither original transfer profile can consume this family
as a source proof. Disabling payment callbacks does not disable try callbacks. -/
theorem source_profile_refused (ts : TransferSem Probe) : ¬ ValidT ts sourceProblem :=
  callback_source_refused ts.inv ts.pay

/-- info: 'Solidity.Examples.Tactics.ExternalTryUniversal.no_normal_source_family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms no_normal_source_family

/-- info: 'Solidity.Examples.Tactics.ExternalTryUniversal.source_profile_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_profile_refused

end Solidity.Examples.Tactics.ExternalTryUniversal
