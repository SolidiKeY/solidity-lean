import Solidity.Lowering.V07.P12AssignedConditionControls

/-!
Guarded regression: initial alignment alone must not let an always-failing or
always-reverting operand satisfy the public Condition contract. Reuse the
published assignment model, relations and actual completed source run together.
A timeout at horizon zero is distinguished from completion at horizon two;
these horizons are not EVM gas or a universal noncompletion claim. This audit
covers Boolean local assignment generally and one existing concrete model,
not admission or whole compilation.
-/
namespace Solidity.H62.AuditV07.ConditionContractWitness

open Solidity.Lowering.V07 P12NextInterface
open P12Controls (C E SrcCtx TgtCtx source target mapping)
open P12AssignedConditionControls (values worlds initial producer)
open MixedAssignmentControls (globals)
open Source.SemanticsExamples (F0)

/-- Impossible reference constructors cannot inhabit an intrinsic Boolean value. -/
private theorem bool_value_exists {D : Source.Layout} (value : Source.Val D .bool) :
    ∃ choice, value = .bool choice := by
  cases value with
  | bool choice => exact ⟨choice, rfl⟩
  | memRef location address => cases location
  | storRef location path => cases location
  | cdRef location offset length => cases location

/-- Totality of a local Boolean assignment makes reject-all contracts impossible. -/
theorem assignment_condition_cannot_reject_all
    {E : Source.Env} {C : Contract} {srcΓ : Source.RCtx} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (m : ContextMap srcΓ Γ)
    (values : ValueRelation E C) (worlds : WorldRelation E C)
    (i a : Source.Idx srcΓ .bool)
    (candidate : Condition G F m values worlds (.assign (.local i) (.local a)))
    (reason : THalt) :
    ¬(∀ reached : State C Γ, candidate.operand.run reached = .error reason) := by
  intro rejects
  obtain ⟨before, reached, aligned⟩ := candidate.initial_nonempty
  obtain ⟨choice, read⟩ := bool_value_exists (before.1.get a)
  obtain ⟨out, success, _⟩ := candidate.success 2 before
    (before.1.set i (.bool choice), before.2) reached choice aligned
    (source_assign_local_run G F 0 before i a (.bool choice) read)
  rw [rejects reached] at success
  cases success

abbrev expression : Source.RExpr E SrcCtx .bool :=
  .assign (.local .here) (.local (.there .here))

def frame (checked : Bool) : Source.Fr := { F0 with checked := checked }

abbrev ModelCondition (p : Roadmap.Pipeline) (checked : Bool) :=
  Condition (globals p) (frame checked) mapping values worlds expression

/-- The producer and both success premises coexist on the same concrete inputs. -/
theorem joint_success_inputs (p : Roadmap.Pipeline) (checked : Bool) :
    ∃ (candidate : ModelCondition p checked) (fuel : Nat)
      (before after : Source.EMState E SrcCtx) (reached : State C TgtCtx) (choice : Bool),
      Aligned mapping values worlds before reached ∧
      (Source.evalE (globals p) (frame checked) fuel expression).run before =
        (.ok (.val (.bool choice)), after) := by
  exact ⟨producer p checked, 2, source,
    (source.1.set .here (.bool true), source.2), target, true, initial,
    source_assign_local_run (globals p) (frame checked) 0 source
      .here (.there .here) (.bool true) rfl⟩

/-- Every candidate satisfying the unchanged contract must succeed here. -/
theorem successful_target (p : Roadmap.Pipeline) (checked : Bool)
    (candidate : ModelCondition p checked) (fuel : Nat) :
    ∃ out : Out C target.H TgtCtx,
      candidate.operand.run target = .ok (out, .prim true) ∧
      Aligned mapping values worlds
        (source.1.set .here (.bool true), source.2) out.st :=
  candidate.success (fuel + 2) source
    (source.1.set .here (.bool true), source.2) target true initial
    (source_assign_local_run (globals p) (frame checked) fuel source
      .here (.there .here) (.bool true) rfl)

/-- Failure of any native kind conflicts with this actual successful input. -/
theorem failure_at_witness_impossible (p : Roadmap.Pipeline) (checked : Bool)
    (candidate : ModelCondition p checked) (reason : THalt) :
    candidate.operand.run target ≠ .error reason := by
  obtain ⟨out, success, _⟩ := successful_target p checked candidate 0
  rw [success]
  intro impossible
  cases impossible

/-- An always-failing/reverting substitution cannot satisfy this public contract. -/
theorem reject_all_incompatible (p : Roadmap.Pipeline) (checked : Bool)
    (candidate : ModelCondition p checked) (reason : THalt) :
    ¬(∀ reached : State C TgtCtx, candidate.operand.run reached = .error reason) := by
  exact assignment_condition_cannot_reject_all (globals p) (frame checked)
    mapping values worlds .here (.there .here) candidate reason

/-- An exhausted finite horizon is not evidence of noncompletion at every horizon. -/
theorem horizon_boundary (p : Roadmap.Pipeline) (checked : Bool) :
    (Source.evalE (globals p) (frame checked) 0 expression).run source =
      (.error .timeout, source) ∧
    ∃ (fuel : Nat) (after : Source.EMState E SrcCtx),
      (Source.evalE (globals p) (frame checked) fuel expression).run source =
        (.ok (.val (.bool true)), after) := by
  exact ⟨P12AssignedCondition.source_zero (globals p) (frame checked) source
    .here (.there .here), 2, (source.1.set .here (.bool true), source.2),
    source_assign_local_run (globals p) (frame checked) 0 source
      .here (.there .here) (.bool true) rfl⟩

#print axioms assignment_condition_cannot_reject_all
#print axioms joint_success_inputs
#print axioms successful_target
#print axioms failure_at_witness_impossible
#print axioms reject_all_incompatible
#print axioms horizon_boundary
end Solidity.H62.AuditV07.ConditionContractWitness
