import Solidity.Backend.Passes.LoopCallFailures

/-! Exact observed standard-only loop/call headline and producer guards. -/
/-- info: 'Solidity.Backend.Passes.loops_budgeted_memoryCalls_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.loops_budgeted_memoryCalls_link
/-- info: 'Solidity.Backend.Passes.loop_scopes_budgeted_memoryCalls_link' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.loop_scopes_budgeted_memoryCalls_link
/-- info: 'Solidity.Backend.Passes.LoopCallControls.producer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallControls.producer
/-- info: 'Solidity.Backend.Passes.LoopCallControls.free' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallControls.free
/-- info: 'Solidity.Backend.Passes.LoopCallControls.checkedCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallControls.checkedCall
/-- info: 'Solidity.Backend.Passes.LoopCallControls.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallControls.source
/-- info: 'Solidity.Backend.Passes.LoopCallControls.cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallControls.cost
/-- info: 'Solidity.Backend.Passes.LoopCallControls.expanded_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallControls.expanded_frame
/-- info: 'Solidity.Backend.Passes.LoopCallControls.public_recognizer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallControls.public_recognizer
/-- info: 'Solidity.Backend.Passes.LoopCallControls.whole_recognizer_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallControls.whole_recognizer_refused
/-- info: 'Solidity.Backend.Passes.LoopCallControls.joined_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallControls.joined_source
/-- info: 'Solidity.Backend.Passes.LoopCallControls.receiving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallControls.receiving
/-- info: 'Solidity.Backend.Passes.LoopCallControls.private_frame_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallControls.private_frame_refused
/-- info: 'Solidity.Backend.Passes.LoopCallApplication.after_scope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallApplication.after_scope
/-- info: 'Solidity.Backend.Passes.LoopCallApplication.correlated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallApplication.correlated
/-- info: 'Solidity.Backend.Passes.LoopCallApplication.shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallApplication.shared
/-- info: 'Solidity.Backend.Passes.LoopCallObservations.target_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallObservations.target_run
/-- info: 'Solidity.Backend.Passes.LoopCallObservations.whole_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallObservations.whole_target
/-- info: 'Solidity.Backend.Passes.LoopCallObservations.final_stack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallObservations.final_stack
/-- info: 'Solidity.Backend.Passes.LoopCallObservations.whole_target_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallObservations.whole_target_tail
/-- info: 'Solidity.Backend.Passes.LoopCallObservations.complete_target_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallObservations.complete_target_vector
/-- info: 'Solidity.Backend.Passes.LoopCallObservations.skipped_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallObservations.skipped_call
/-- info: 'Solidity.Backend.Passes.LoopCallObservations.corrupt_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallObservations.corrupt_tail
/-- info: 'Solidity.Backend.Passes.LoopCallObservations.complete_source_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallObservations.complete_source_vector
/-- info: 'Solidity.Backend.Passes.LoopCallObservations.return_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallObservations.return_identity
/-- info: 'Solidity.Backend.Passes.LoopCallObservations.selected_return_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallObservations.selected_return_base
/-- info: 'Solidity.Backend.Passes.LoopCallObservations.stale_return_map_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallObservations.stale_return_map_refused
/-- info: 'Solidity.Backend.Passes.LoopCallFailures.argument' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallFailures.argument
/-- info: 'Solidity.Backend.Passes.LoopCallFailures.stale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallFailures.stale
/-- info: 'Solidity.Backend.Passes.LoopCallFailures.argument_free' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallFailures.argument_free
/-- info: 'Solidity.Backend.Passes.LoopCallFailures.stale_free' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallFailures.stale_free
/-- info: 'Solidity.Backend.Passes.LoopCallFailures.argument_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallFailures.argument_source
/-- info: 'Solidity.Backend.Passes.LoopCallFailures.stale_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallFailures.stale_source
/-- info: 'Solidity.Backend.Passes.LoopCallFailures.costs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallFailures.costs
/-- info: 'Solidity.Backend.Passes.LoopCallFailures.frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallFailures.frames
/-- info: 'Solidity.Backend.Passes.LoopCallFailures.reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallFailures.reached
/-- info: 'Solidity.Backend.Passes.LoopCallFailures.argument_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallFailures.argument_reached
/-- info: 'Solidity.Backend.Passes.LoopCallFailures.stale_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallFailures.stale_reached
/-- info: 'Solidity.Backend.Passes.LoopCallFailures.wrong_failure_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallFailures.wrong_failure_stage
/-- info: 'Solidity.Backend.Passes.LoopCallFailures.source_unreachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopCallFailures.source_unreachable
