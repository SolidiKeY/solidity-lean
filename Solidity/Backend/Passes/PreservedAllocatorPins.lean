import Solidity.Backend.Passes.PreservedAllocatorNegatives

/-! Exact observed standard-only allocator-preservation application guards. -/
/-- info: 'Solidity.Backend.Passes.objects_budgeted_construction_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.objects_budgeted_construction_link
/-- info: 'Solidity.Backend.Passes.objects_budgeted_memory_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.objects_budgeted_memory_link
/-- info: 'Solidity.Backend.Passes.construction_budgeted_memory_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.construction_budgeted_memory_link
/-- info: 'Solidity.Backend.Passes.reference_ptr_objects' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.reference_ptr_objects
/-- info: 'Solidity.Backend.Passes.reference_stmt_objects' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.reference_stmt_objects
/-- info: 'Solidity.Backend.Passes.reference_prog_objects' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.reference_prog_objects
/-- info: 'Solidity.Backend.Passes.referenceObjects_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.referenceObjects_code
/-- info: 'Solidity.Backend.Passes.referenceObjects' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.referenceObjects
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorControls.suffix_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorControls.suffix_source
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorControls.suffix_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorControls.suffix_cost
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorControls.memory_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorControls.memory_cost
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorControls.object_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorControls.object_code
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorControls.suffix_codes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorControls.suffix_codes
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorControls.reached_allocator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorControls.reached_allocator
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorControls.reached_link' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorControls.reached_link
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorControls.reached_memory_link' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorControls.reached_memory_link
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorControls.shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorControls.shared
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorObservations.source_heap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorObservations.source_heap
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorObservations.old_contents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorObservations.old_contents
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorObservations.parent_contents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorObservations.parent_contents
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorObservations.fresh_contents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorObservations.fresh_contents
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorObservations.suffix_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorObservations.suffix_code
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorObservations.suffix_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorObservations.suffix_shape
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorObservations.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorObservations.complete
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorApplication.prefix_bases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorApplication.prefix_bases
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorApplication.observed_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorApplication.observed_shared
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorApplication.stale_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorApplication.stale_refused
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorNegatives.failing_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorNegatives.failing_cost
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorNegatives.failed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorNegatives.failed_source
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorNegatives.failed_link' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorNegatives.failed_link
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorNegatives.failed_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorNegatives.failed_target
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorNegatives.memory_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorNegatives.memory_shared
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorNegatives.skipped_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorNegatives.skipped_source
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorNegatives.skipped_contents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorNegatives.skipped_contents
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorNegatives.skipped_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorNegatives.skipped_target
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorNegatives.corrupted_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorNegatives.corrupted_tail
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorNegatives.bad_value_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorNegatives.bad_value_source
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorNegatives.failing_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorNegatives.failing_code
/-- info: 'Solidity.Backend.Passes.PreservedAllocatorNegatives.reached_failure_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PreservedAllocatorNegatives.reached_failure_witness
