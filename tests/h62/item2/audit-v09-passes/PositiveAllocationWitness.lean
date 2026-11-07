import Solidity.Backend.Passes.PositiveAllocationFailureControls

/-! Guard checking allocation capacity before an assignment changes the reached
size, or inventing a post-failure state/tail after a reached bounds failure.
Reuse existing positive-base producer and assignment certificates. -/
namespace Solidity.Backend.Passes.AuditPositiveAllocationFailure
open Evm Evm.Memory
open Solidity.Backend.Passes
open PositiveAllocationFailure

theorem joint :
    StateRepr 1 1 16 F before base (machine cursor) ∧
    AllocationInput 1 16 (selected.checked.cost after) before base (machine cursor) ∧
    statement.run after = .error .revert ∧
    AllocationInput 1 16 (selected.checked.cost before) after base Controls.nearTarget ∧
    ¬ AllocationInput 1 16 (selected.checked.cost after) after base Controls.nearTarget ∧
    (∃ tail : List Word, tail = [w[77]]) :=
  ⟨(initial cursor (by decide)).1,initial_capacity,actual_body_failure,
    Controls.stale_budget_fits,Controls.reached_budget_refused,[w[77]],rfl⟩
def stale_budget_fits := @Solidity.Backend.Passes.PositiveAllocationFailure.Controls.stale_budget_fits
def reached_budget_refused := @Solidity.Backend.Passes.PositiveAllocationFailure.Controls.reached_budget_refused
def joined_source := @Solidity.Backend.Passes.PositiveAllocationFailure.Controls.joined_source
def physical := @Solidity.Backend.Passes.PositiveAllocationFailure.Controls.physical
def initial_observations := @Solidity.Backend.Passes.PositiveAllocationFailure.Controls.initial_observations
def reached_observations := @Solidity.Backend.Passes.PositiveAllocationFailure.Controls.reached_observations
def prefix_saved_head := @Solidity.Backend.Passes.PositiveAllocationFailure.Controls.prefix_saved_head
def reached_input_refused_near_end := @Solidity.Backend.Passes.PositiveAllocationFailure.Controls.reached_input_refused_near_end
def prefix_source := @Solidity.Backend.Passes.PositiveAllocationFailure.Controls.prefix_source
def skipped_assignment_refused := @Solidity.Backend.Passes.PositiveAllocationFailure.Controls.skipped_assignment_refused

/-- info: 'Solidity.Backend.Passes.AuditPositiveAllocationFailure.joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPositiveAllocationFailure.joint

/-- info: 'Solidity.Backend.Passes.AuditPositiveAllocationFailure.stale_budget_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPositiveAllocationFailure.stale_budget_fits

/-- info: 'Solidity.Backend.Passes.AuditPositiveAllocationFailure.reached_budget_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPositiveAllocationFailure.reached_budget_refused

/-- info: 'Solidity.Backend.Passes.AuditPositiveAllocationFailure.joined_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPositiveAllocationFailure.joined_source

/-- info: 'Solidity.Backend.Passes.AuditPositiveAllocationFailure.physical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPositiveAllocationFailure.physical

/-- info: 'Solidity.Backend.Passes.AuditPositiveAllocationFailure.initial_observations' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPositiveAllocationFailure.initial_observations

/-- info: 'Solidity.Backend.Passes.AuditPositiveAllocationFailure.reached_observations' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPositiveAllocationFailure.reached_observations

/-- info: 'Solidity.Backend.Passes.AuditPositiveAllocationFailure.prefix_saved_head' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPositiveAllocationFailure.prefix_saved_head

/-- info: 'Solidity.Backend.Passes.AuditPositiveAllocationFailure.reached_input_refused_near_end' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPositiveAllocationFailure.reached_input_refused_near_end

/-- info: 'Solidity.Backend.Passes.AuditPositiveAllocationFailure.prefix_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPositiveAllocationFailure.prefix_source

/-- info: 'Solidity.Backend.Passes.AuditPositiveAllocationFailure.skipped_assignment_refused' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPositiveAllocationFailure.skipped_assignment_refused
end Solidity.Backend.Passes.AuditPositiveAllocationFailure
