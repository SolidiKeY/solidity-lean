import Solidity.Backend.Passes.FreshBooleanControls
import Solidity.Backend.Passes.FreshBooleanCompilation

/-! Exact observed standard-only guards for actual fresh sequencing. -/
/-- info: 'Solidity.Backend.Passes.memory_reindex_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.memory_reindex_code
/-- info: 'Solidity.Backend.Passes.memory_reindex_frag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.memory_reindex_frag
/-- info: 'Solidity.Backend.Passes.memory_reindex_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.memory_reindex_cost
/-- info: 'Solidity.Backend.Passes.memory_reindex_input_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.memory_reindex_input_iff
/-- info: 'Solidity.Backend.Passes.memory_reindex_mapped_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.memory_reindex_mapped_iff
/-- info: 'Solidity.Backend.Passes.FreshBooleanPrefix.population_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanPrefix.population_tail
/-- info: 'Solidity.Backend.Passes.FreshBooleanPrefix.initializer_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanPrefix.initializer_tail
/-- info: 'Solidity.Backend.Passes.FreshBooleanPrefix.provisioner_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanPrefix.provisioner_code
/-- info: 'Solidity.Backend.Passes.FreshBooleanPrefix.population_initializer_link' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanPrefix.population_initializer_link
/-- info: 'Solidity.Backend.Passes.FreshBooleanPrefix.initializer_receiver_link' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanPrefix.initializer_receiver_link
/-- info: 'Solidity.Backend.Passes.FreshBooleanPrefix.initialized_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanPrefix.initialized_output
/-- info: 'Solidity.Backend.Passes.FreshBooleanPrefix.provisioning_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanPrefix.provisioning_shared
/-- info: 'Solidity.Backend.Passes.FreshBooleanFailure.source_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanFailure.source_prefix
/-- info: 'Solidity.Backend.Passes.FreshBooleanFailure.source_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanFailure.source_revert
/-- info: 'Solidity.Backend.Passes.FreshBooleanFailure.source_right_revert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanFailure.source_right_revert
/-- info: 'Solidity.Backend.Passes.FreshBooleanFailure.capture_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanFailure.capture_link
/-- info: 'Solidity.Backend.Passes.FreshBooleanFailure.observation_link' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanFailure.observation_link
/-- info: 'Solidity.Backend.Passes.FreshBooleanFailure.pipeline_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanFailure.pipeline_shared
/-- info: 'Solidity.Backend.Passes.FreshBooleanFailure.fresh_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanFailure.fresh_revert
/-- info: 'Solidity.Backend.Passes.FreshBooleanFailure.fresh_failure_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanFailure.fresh_failure_witness
/-- info: 'Solidity.Backend.Passes.FreshBooleanFailure.opposite_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanFailure.opposite_source
/-- info: 'Solidity.Backend.Passes.FreshBooleanFailure.fresh_opposite_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanFailure.fresh_opposite_shared
/-- info: 'Solidity.Backend.Passes.FreshBooleanFailure.fresh_opposite_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanFailure.fresh_opposite_source
/-- info: 'Solidity.Backend.Passes.FreshBooleanFailure.prefix_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanFailure.prefix_resources
/-- info: 'Solidity.Backend.Passes.FreshBooleanControls.ordered_initial_to_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanControls.ordered_initial_to_capture
/-- info: 'Solidity.Backend.Passes.FreshBooleanControls.ordered_opposite_prefix_and_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanControls.ordered_opposite_prefix_and_terminal
/-- info: 'Solidity.Backend.Passes.FreshBooleanControls.ordered_source_prefixes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanControls.ordered_source_prefixes
/-- info: 'Solidity.Backend.Passes.FreshBooleanControls.wrong_order_complete_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanControls.wrong_order_complete_prefix
/-- info: 'Solidity.Backend.Passes.FreshBooleanControls.skipped_capture_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanControls.skipped_capture_prefix
/-- info: 'Solidity.Backend.Passes.FreshBooleanControls.corrupted_tail_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanControls.corrupted_tail_prefix
/-- info: 'Solidity.Backend.Passes.FreshBooleanControls.corrupted_tail_still_reverts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanControls.corrupted_tail_still_reverts
/-- info: 'Solidity.Backend.Passes.FreshBooleanControls.insufficient_observer_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanControls.insufficient_observer_frame
/-- info: 'Solidity.Backend.Passes.FreshBooleanControls.stale_initial_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanControls.stale_initial_map
/-- info: 'Solidity.Backend.Passes.FreshBooleanControls.ordinary_failure_not_panic_or_divergence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanControls.ordinary_failure_not_panic_or_divergence
/-- info: 'Solidity.Backend.Passes.FreshBooleanControls.reached_failure_not_target_fault' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanControls.reached_failure_not_target_fault

/-- info: 'Solidity.Backend.Passes.memory_reindex_compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.memory_reindex_compile
/-- info: 'Solidity.Backend.Passes.memory_compile_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.memory_compile_join
/-- info: 'Solidity.Backend.Passes.FreshBooleanCompilation.whole_recognized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanCompilation.whole_recognized
/-- info: 'Solidity.Backend.Passes.FreshBooleanCompilation.whole_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanCompilation.whole_code
/-- info: 'Solidity.Backend.Passes.FreshBooleanCompilation.public_whole' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanCompilation.public_whole
/-- info: 'Solidity.Backend.Passes.FreshBooleanCompilation.public_whole_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanCompilation.public_whole_code
/-- info: 'Solidity.Backend.Passes.FreshBooleanCompilation.whole_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanCompilation.whole_input
/-- info: 'Solidity.Backend.Passes.FreshBooleanCompilation.whole_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanCompilation.whole_certificate
/-- info: 'Solidity.Backend.Passes.FreshBooleanCompilation.actual_revert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanCompilation.actual_revert
/-- info: 'Solidity.Backend.Passes.FreshBooleanCompilation.actual_opposite_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FreshBooleanCompilation.actual_opposite_target
