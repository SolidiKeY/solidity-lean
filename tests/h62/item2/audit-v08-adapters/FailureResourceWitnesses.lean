import Solidity.Source.FailureResources

/-! Additive joint-premise fixtures for the frozen failure-resource laws.
These are resource-interface witnesses, not compiler/execution adequacy.
No frozen signature, resource representation or proof budget is changed. -/
namespace H62.AuditV08Adapters.FailureResourceWitnesses
open Solidity.Source.FailureResources Solidity.Roadmap.Evm

def clear : FailurePoints := noFailures (fun _ => 37)
def failed : FailurePoints where
  tx _ := .dropped
  frame _ := some 5

def before : Bound := (3, clear)
def later : Bound := (4, clear)

/-- All hypotheses of Bound.le_trans hold together on these same resources. -/
theorem trans_joint :
    ∃ a b c : Bound, a ≤ b ∧ b ≤ c :=
  ⟨before, later, later, ⟨rfl, by decide⟩, Bound.le_refl later⟩

/-- The SAME extension witnesses the premise of replacement monotonicity. -/
theorem replacement_joint :
    ∃ (r s : Bound) (_p : FailurePoints), r ≤ s :=
  ⟨before, later, failed, ⟨rfl, by decide⟩⟩

/-- Dropped-request and frame-failure premises are simultaneously realizable. -/
theorem refusal_joint :
    ∃ (p : FailurePoints) (i k cut : Nat),
      p.tx i = .dropped ∧ p.frame k = some cut :=
  ⟨failed, 2, 7, 5, rfl, rfl⟩

/-- Different schedules cannot be passed off as increased horizon. -/
theorem schedule_change_joint :
    ∃ r s : Bound, r.points ≠ s.points := by
  refine ⟨before, (4, failed), ?_⟩
  intro h
  have observed := congrArg (fun p : FailurePoints => p.tx 0) h
  change TxFate.runs 37 none = .dropped at observed
  cases observed

/-- Actual frozen refusal conclusions on the exact common witness. -/
theorem exact_refusals : ¬ NoFail failed ∧ ¬ before ≤ (4, failed) := by
  refine ⟨dropped_not_noFail (i := 2) rfl, ?_⟩
  apply Bound.not_le_of_points_ne
  intro h
  have observed := congrArg (fun p : FailurePoints => p.tx 0) h
  change TxFate.runs 37 none = .dropped at observed
  cases observed

/-- H69: the deliberate diagonal refutation is audited by impossibility,
not by fabricating a joint witness for its contradictory premises. -/
theorem no_retraction_joint_impossible :
    ¬ ∃ (extract : Nat → FailurePoints) (replace : Nat → FailurePoints → Nat),
      ∀ n p, extract (replace n p) = p := by
  rintro ⟨extract, replace, rightInverse⟩
  exact no_horizon_retraction extract replace rightInverse

/-- The resource premise predicate itself has an inhabited model. This is
not an inhabitant of the separate frozen SourceSpec producer structure. -/
theorem nofail_predicate_witness : ∃ p : FailurePoints, NoFail p :=
  ⟨clear, noFailures_noFail (fun _ => 37)⟩

/-- info: 'H62.AuditV08Adapters.FailureResourceWitnesses.trans_joint' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms trans_joint
/-- info: 'H62.AuditV08Adapters.FailureResourceWitnesses.replacement_joint' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms replacement_joint
/-- info: 'H62.AuditV08Adapters.FailureResourceWitnesses.refusal_joint' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms refusal_joint
/-- info: 'H62.AuditV08Adapters.FailureResourceWitnesses.schedule_change_joint' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms schedule_change_joint
/-- info: 'H62.AuditV08Adapters.FailureResourceWitnesses.exact_refusals' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms exact_refusals
/-- info: 'H62.AuditV08Adapters.FailureResourceWitnesses.no_retraction_joint_impossible' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms no_retraction_joint_impossible
/-- info: 'H62.AuditV08Adapters.FailureResourceWitnesses.nofail_predicate_witness' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms nofail_predicate_witness
end H62.AuditV08Adapters.FailureResourceWitnesses
