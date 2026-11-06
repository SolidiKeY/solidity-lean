import Solidity.Backend.Passes.ValueSequenceControls

/-! Exact observed standard-only axiom pins for ordered value certificates. -/
/-- info: 'Solidity.Backend.Passes.value_pair_success_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.value_pair_success_tail
/-- info: 'Solidity.Backend.Passes.value_pair_revert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.value_pair_revert_iff
/-- info: 'Solidity.Backend.Passes.value_pair_reached_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.value_pair_reached_revert
/-- info: 'Solidity.Backend.Passes.ValueSequenceControls.first_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueSequenceControls.first_source
/-- info: 'Solidity.Backend.Passes.ValueSequenceControls.second_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueSequenceControls.second_source
/-- info: 'Solidity.Backend.Passes.ValueSequenceControls.ordered_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueSequenceControls.ordered_tail
/-- info: 'Solidity.Backend.Passes.ValueSequenceControls.emitted_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueSequenceControls.emitted_prefix
/-- info: 'Solidity.Backend.Passes.ValueSequenceControls.source_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueSequenceControls.source_order
/-- info: 'Solidity.Backend.Passes.ValueSequenceControls.consumer_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueSequenceControls.consumer_order
/-- info: 'Solidity.Backend.Passes.ValueSequenceControls.wrong_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueSequenceControls.wrong_order
/-- info: 'Solidity.Backend.Passes.ValueSequenceControls.corruption' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueSequenceControls.corruption
/-- info: 'Solidity.Backend.Passes.ValueSequenceControls.heterogeneous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueSequenceControls.heterogeneous
/-- info: 'Solidity.Backend.Passes.ValueSequenceControls.immediate_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueSequenceControls.immediate_failure
/-- info: 'Solidity.Backend.Passes.ValueSequenceControls.reached_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueSequenceControls.reached_failure
/-- info: 'Solidity.Backend.Passes.ValueSequenceControls.unchanged_memory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueSequenceControls.unchanged_memory
/-- info: 'Solidity.Backend.Passes.ValueSequenceControls.after_allocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ValueSequenceControls.after_allocation
