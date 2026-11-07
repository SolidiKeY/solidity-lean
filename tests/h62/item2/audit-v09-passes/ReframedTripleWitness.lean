import Solidity.Backend.Passes.ReframedTripleControls

/-! Guard using a zero legacy metric as capacity for a reached allocating loop,
or silently dropping original 128/64/5 frame indices and full tail observations.
Derive the middle capacity from actual shared execution and the real Room. -/
namespace Solidity.Backend.Passes.AuditReframedTriple
open Evm Evm.Memory Evm.Compiler
open Solidity.Backend.Passes
open LoopScopeControls

theorem joint :
    (Compilation.memory preparation).Input 1 128 MemoryCallControls.base MemoryCallControls.initial MemoryCallControls.machine ∧
    prepare.run MemoryCallControls.initial = .ok prepared ∧
    wrapped.run prepared.st = .ok loopOut ∧
    consume.run loopOut.st = .ok final ∧
    (∃ (selected : Nat → Fin W) (middle : Machine),
      checked.Input 1 64 selected prepared.st middle ∧
      AllocationInput 1 64 3 prepared.st selected middle) := by
  refine ⟨LoopScopeApplication.preparation_input,prepared_source,wrapped_source,final_source,?_⟩
  obtain ⟨mb,_,_,mid,_,_,_,_,_,_,_,_,_,_,all⟩ := ReframedTripleControls.shared
  obtain ⟨_,_,_,middleInput,_,_,_,_,_,_,_⟩ := all []
  exact ⟨mb,{mid with stack := []},middleInput,
    scope_cost_allocation_input middleInput.2.2 actual_cost⟩
def middle_room := @Solidity.Backend.Passes.ReframedTripleControls.middle_room
def first_link := @Solidity.Backend.Passes.ReframedTripleControls.first_link
def second_link := @Solidity.Backend.Passes.ReframedTripleControls.second_link
def shared := @Solidity.Backend.Passes.ReframedTripleControls.shared
def wrong_zero_cost_refused := @Solidity.Backend.Passes.ReframedTripleControls.wrong_zero_cost_refused
def complete_observations := @Solidity.Backend.Passes.ReframedTripleControls.complete_observations
def saved_tail_corruption := @Solidity.Backend.Passes.ReframedTripleControls.saved_tail_corruption

/-- info: 'Solidity.Backend.Passes.AuditReframedTriple.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReframedTriple.joint

/-- info: 'Solidity.Backend.Passes.AuditReframedTriple.middle_room' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReframedTriple.middle_room

/-- info: 'Solidity.Backend.Passes.AuditReframedTriple.first_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReframedTriple.first_link

/-- info: 'Solidity.Backend.Passes.AuditReframedTriple.second_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReframedTriple.second_link

/-- info: 'Solidity.Backend.Passes.AuditReframedTriple.shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReframedTriple.shared

/-- info: 'Solidity.Backend.Passes.AuditReframedTriple.wrong_zero_cost_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReframedTriple.wrong_zero_cost_refused

/-- info: 'Solidity.Backend.Passes.AuditReframedTriple.complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReframedTriple.complete_observations

/-- info: 'Solidity.Backend.Passes.AuditReframedTriple.saved_tail_corruption' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReframedTriple.saved_tail_corruption
end Solidity.Backend.Passes.AuditReframedTriple
