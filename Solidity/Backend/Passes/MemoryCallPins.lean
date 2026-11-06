import Solidity.Backend.Passes.MemoryCallFailures

/-! Exact standard-only guards for expanded-call links and inhabited calls. -/
/-- info: 'Solidity.Backend.Passes.memoryCalls_memory_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.memoryCalls_memory_link
/-- info: 'Solidity.Backend.Passes.memoryCalls_budgeted_memory_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.memoryCalls_budgeted_memory_link
/-- info: 'Solidity.Backend.Passes.memory_budgeted_memoryCalls_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.memory_budgeted_memoryCalls_link
/-- info: 'Solidity.Backend.Passes.memoryCalls_budgeted_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.memoryCalls_budgeted_link
/-- info: 'Solidity.Backend.Passes.memoryCalls_nonallocating_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.memoryCalls_nonallocating_link
/-- info: 'Solidity.Backend.Passes.MemoryCallControls.push_free' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallControls.push_free
/-- info: 'Solidity.Backend.Passes.MemoryCallControls.public_recognizer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallControls.public_recognizer
/-- info: 'Solidity.Backend.Passes.MemoryCallControls.actual_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallControls.actual_public
/-- info: 'Solidity.Backend.Passes.MemoryCallControls.initial_repr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallControls.initial_repr
/-- info: 'Solidity.Backend.Passes.MemoryCallControls.first_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallControls.first_source
/-- info: 'Solidity.Backend.Passes.MemoryCallControls.second_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallControls.second_source
/-- info: 'Solidity.Backend.Passes.MemoryCallControls.final_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallControls.final_source
/-- info: 'Solidity.Backend.Passes.MemoryCallControls.costs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallControls.costs
/-- info: 'Solidity.Backend.Passes.MemoryCallControls.frame_difference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallControls.frame_difference
/-- info: 'Solidity.Backend.Passes.MemoryCallControls.input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallControls.input
/-- info: 'Solidity.Backend.Passes.MemoryCallControls.body' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallControls.body
/-- info: 'Solidity.Backend.Passes.MemoryCallControls.allocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallControls.allocation
/-- info: 'Solidity.Backend.Passes.MemoryCallControls.producer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallControls.producer
/-- info: 'Solidity.Backend.Passes.MemoryCallControls.checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallControls.checked
/-- info: 'Solidity.Backend.Passes.MemoryCallControls.consumer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallControls.consumer
/-- info: 'Solidity.Backend.Passes.MemoryCallApplication.allocation_free' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallApplication.allocation_free
/-- info: 'Solidity.Backend.Passes.MemoryCallApplication.consumer_free' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallApplication.consumer_free
/-- info: 'Solidity.Backend.Passes.MemoryCallApplication.budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallApplication.budget
/-- info: 'Solidity.Backend.Passes.MemoryCallApplication.into_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallApplication.into_call
/-- info: 'Solidity.Backend.Passes.MemoryCallApplication.after_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallApplication.after_call
/-- info: 'Solidity.Backend.Passes.MemoryCallApplication.joined_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallApplication.joined_source
/-- info: 'Solidity.Backend.Passes.MemoryCallApplication.shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallApplication.shared
/-- info: 'Solidity.Backend.Passes.MemoryCallApplication.consumer_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallApplication.consumer_cost
/-- info: 'Solidity.Backend.Passes.MemoryCallApplication.resources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallApplication.resources
/-- info: 'Solidity.Backend.Passes.MemoryCallApplication.old_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallApplication.old_reference
/-- info: 'Solidity.Backend.Passes.MemoryCallApplication.source_frame_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallApplication.source_frame_refused
/-- info: 'Solidity.Backend.Passes.MemoryCallApplication.branch_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallApplication.branch_controls
/-- info: 'Solidity.Backend.Passes.MemoryCallObservations.source_before_consume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallObservations.source_before_consume
/-- info: 'Solidity.Backend.Passes.MemoryCallObservations.source_after_consume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallObservations.source_after_consume
/-- info: 'Solidity.Backend.Passes.MemoryCallObservations.allocation_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallObservations.allocation_vector
/-- info: 'Solidity.Backend.Passes.MemoryCallObservations.call_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallObservations.call_vector
/-- info: 'Solidity.Backend.Passes.MemoryCallObservations.final_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallObservations.final_vector
/-- info: 'Solidity.Backend.Passes.MemoryCallObservations.skipped_consumer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallObservations.skipped_consumer
/-- info: 'Solidity.Backend.Passes.MemoryCallObservations.return_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallObservations.return_identity
/-- info: 'Solidity.Backend.Passes.MemoryCallObservations.old_map_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallObservations.old_map_preserved
/-- info: 'Solidity.Backend.Passes.MemoryCallObservations.selected_return_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallObservations.selected_return_base
/-- info: 'Solidity.Backend.Passes.MemoryCallObservations.old_only_keeps_old' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallObservations.old_only_keeps_old
/-- info: 'Solidity.Backend.Passes.MemoryCallObservations.stale_map_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallObservations.stale_map_refused
/-- info: 'Solidity.Backend.Passes.MemoryCallFailures.argument_free' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallFailures.argument_free
/-- info: 'Solidity.Backend.Passes.MemoryCallFailures.body_free' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallFailures.body_free
/-- info: 'Solidity.Backend.Passes.MemoryCallFailures.argument_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallFailures.argument_source
/-- info: 'Solidity.Backend.Passes.MemoryCallFailures.body_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallFailures.body_source
/-- info: 'Solidity.Backend.Passes.MemoryCallFailures.costs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallFailures.costs
/-- info: 'Solidity.Backend.Passes.MemoryCallFailures.frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallFailures.frames
/-- info: 'Solidity.Backend.Passes.MemoryCallFailures.later_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallFailures.later_cost
/-- info: 'Solidity.Backend.Passes.MemoryCallFailures.reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallFailures.reached
/-- info: 'Solidity.Backend.Passes.MemoryCallFailures.argument_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallFailures.argument_reached
/-- info: 'Solidity.Backend.Passes.MemoryCallFailures.body_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallFailures.body_reached
/-- info: 'Solidity.Backend.Passes.MemoryCallFailures.scheduled_costs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallFailures.scheduled_costs
/-- info: 'Solidity.Backend.Passes.MemoryCallFailures.source_unreachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallFailures.source_unreachable
/-- info: 'Solidity.Backend.Passes.MemoryCallFailures.wrong_failure_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallFailures.wrong_failure_stage
/-- info: 'Solidity.Backend.Passes.MemoryCallFailures.argument' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallFailures.argument
/-- info: 'Solidity.Backend.Passes.MemoryCallFailures.body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallFailures.body
/-- info: 'Solidity.Backend.Passes.MemoryCallFailures.wholeArgument' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallFailures.wholeArgument
/-- info: 'Solidity.Backend.Passes.MemoryCallFailures.wholeBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.MemoryCallFailures.wholeBody
