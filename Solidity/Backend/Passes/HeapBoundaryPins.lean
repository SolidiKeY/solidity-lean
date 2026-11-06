import Solidity.Backend.Passes.AllocatingMiddle

/-! Exact observed standard-only heap boundary and reachable fixture guards. -/
/-- info: 'Solidity.Backend.Passes.referenceArrays_memory_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.referenceArrays_memory_link
/-- info: 'Solidity.Backend.Passes.objects_memory_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.objects_memory_link
/-- info: 'Solidity.Backend.Passes.construction_memory_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.construction_memory_link
/-- info: 'Solidity.Backend.Passes.objects_referenceArrays_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.objects_referenceArrays_link
/-- info: 'Solidity.Backend.Passes.construction_referenceArrays_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.construction_referenceArrays_link
/-- info: 'Solidity.Backend.Passes.objects_objects_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.objects_objects_link
/-- info: 'Solidity.Backend.Passes.construction_objects_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.construction_objects_link
/-- info: 'Solidity.Backend.Passes.construction_budgeted_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.construction_budgeted_link
/-- info: 'Solidity.Backend.Passes.HeapBoundaryControls.empty_heap' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapBoundaryControls.empty_heap
/-- info: 'Solidity.Backend.Passes.HeapBoundaryControls.physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapBoundaryControls.physical
/-- info: 'Solidity.Backend.Passes.HeapBoundaryControls.allocator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapBoundaryControls.allocator
/-- info: 'Solidity.Backend.Passes.HeapBoundaryControls.cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapBoundaryControls.cost
/-- info: 'Solidity.Backend.Passes.HeapBoundaryControls.input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapBoundaryControls.input
/-- info: 'Solidity.Backend.Passes.HeapBoundaryControls.allocation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapBoundaryControls.allocation_source
/-- info: 'Solidity.Backend.Passes.HeapBoundaryControls.mutation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapBoundaryControls.mutation_source
/-- info: 'Solidity.Backend.Passes.HeapBoundaryControls.observation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapBoundaryControls.observation_source
/-- info: 'Solidity.Backend.Passes.HeapBoundaryControls.reached_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapBoundaryControls.reached_link
/-- info: 'Solidity.Backend.Passes.HeapBoundaryControls.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapBoundaryControls.success
/-- info: 'Solidity.Backend.Passes.HeapBoundaryControls.source_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapBoundaryControls.source_answer
/-- info: 'Solidity.Backend.Passes.HeapObservations.source_objects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapObservations.source_objects
/-- info: 'Solidity.Backend.Passes.HeapObservations.read_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapObservations.read_source
/-- info: 'Solidity.Backend.Passes.HeapObservations.observation_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapObservations.observation_code
/-- info: 'Solidity.Backend.Passes.HeapObservations.read_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapObservations.read_shape
/-- info: 'Solidity.Backend.Passes.HeapObservations.mutation_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapObservations.mutation_code
/-- info: 'Solidity.Backend.Passes.HeapObservations.mutation_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapObservations.mutation_shape
/-- info: 'Solidity.Backend.Passes.HeapObservations.complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapObservations.complete_observations
/-- info: 'Solidity.Backend.Passes.HeapPrefix.allocation_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapPrefix.allocation_code
/-- info: 'Solidity.Backend.Passes.HeapPrefix.allocation_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapPrefix.allocation_observations
/-- info: 'Solidity.Backend.Passes.HeapApplication.observed_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapApplication.observed_success
/-- info: 'Solidity.Backend.Passes.HeapApplication.stale_map_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapApplication.stale_map_refused
/-- info: 'Solidity.Backend.Passes.HeapApplication.skipped_effect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapApplication.skipped_effect
/-- info: 'Solidity.Backend.Passes.HeapApplication.reached_source_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapApplication.reached_source_failure
/-- info: 'Solidity.Backend.Passes.HeapApplication.reached_target_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapApplication.reached_target_failure
/-- info: 'Solidity.Backend.Passes.HeapApplication.wrong_failure_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapApplication.wrong_failure_stage
/-- info: 'Solidity.Backend.Passes.HeapApplication.read_before_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapApplication.read_before_source
/-- info: 'Solidity.Backend.Passes.HeapApplication.skipped_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapApplication.skipped_target
/-- info: 'Solidity.Backend.Passes.HeapApplication.corrupted_saved_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.HeapApplication.corrupted_saved_tail
/-- info: 'Solidity.Backend.Passes.AllocatingMiddle.first_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.AllocatingMiddle.first_source
/-- info: 'Solidity.Backend.Passes.AllocatingMiddle.middle_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.AllocatingMiddle.middle_source
/-- info: 'Solidity.Backend.Passes.AllocatingMiddle.last_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.AllocatingMiddle.last_source
/-- info: 'Solidity.Backend.Passes.AllocatingMiddle.first_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.AllocatingMiddle.first_cost
/-- info: 'Solidity.Backend.Passes.AllocatingMiddle.middle_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.AllocatingMiddle.middle_cost
/-- info: 'Solidity.Backend.Passes.AllocatingMiddle.initial_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.AllocatingMiddle.initial_input
/-- info: 'Solidity.Backend.Passes.AllocatingMiddle.link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.AllocatingMiddle.link
/-- info: 'Solidity.Backend.Passes.AllocatingMiddle.reached_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.AllocatingMiddle.reached_link
/-- info: 'Solidity.Backend.Passes.AllocatingMiddle.budgeted_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.AllocatingMiddle.budgeted_shared
/-- info: 'Solidity.Backend.Passes.AllocatingMiddle.missing_default_headers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.AllocatingMiddle.missing_default_headers
