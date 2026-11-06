import Solidity.Backend.Passes.ReframedTerminals

/-! Exact observed standard-only CP26 headline axioms. -/
/-- info: 'Solidity.Backend.Passes.memory_state_shrink' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.memory_state_shrink
/-- info: 'Solidity.Backend.Passes.memory_shrinking_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.memory_shrinking_link
/-- info: 'Solidity.Backend.Passes.memoryCalls_shrinking_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.memoryCalls_shrinking_link
/-- info: 'Solidity.Backend.Passes.reframed_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.reframed_same
/-- info: 'Solidity.Backend.Passes.compilation_reframed_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.compilation_reframed_shared
/-- info: 'Solidity.Backend.Passes.compilation_reframed_revert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.compilation_reframed_revert_iff
/-- info: 'Solidity.Backend.Passes.compilation_reframed_fault_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.compilation_reframed_fault_iff
/-- info: 'Solidity.Backend.Passes.ReframedControls.frame_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReframedControls.frame_gap
/-- info: 'Solidity.Backend.Passes.ReframedControls.prefix_refused_at_suffix_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReframedControls.prefix_refused_at_suffix_frame
/-- info: 'Solidity.Backend.Passes.ReframedControls.physical_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReframedControls.physical_link
/-- info: 'Solidity.Backend.Passes.ReframedControls.shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReframedControls.shared
/-- info: 'Solidity.Backend.Passes.ReframedControls.bad_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReframedControls.bad_source
/-- info: 'Solidity.Backend.Passes.ReframedControls.bad_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReframedControls.bad_link
/-- info: 'Solidity.Backend.Passes.ReframedControls.reached_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReframedControls.reached_revert
/-- info: 'Solidity.Backend.Passes.ReframedControls.ordered_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReframedControls.ordered_vectors
/-- info: 'Solidity.Backend.Passes.ReframedControls.skipped_consumer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReframedControls.skipped_consumer
/-- info: 'Solidity.Backend.Passes.ReframedControls.corrupted_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReframedControls.corrupted_tail
/-- info: 'Solidity.Backend.Passes.ReframedControls.short_suffix_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReframedControls.short_suffix_frame
/-- info: 'Solidity.Backend.Passes.ReframedTerminals.Panic.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReframedTerminals.Panic.source
/-- info: 'Solidity.Backend.Passes.ReframedTerminals.Panic.link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReframedTerminals.Panic.link
/-- info: 'Solidity.Backend.Passes.ReframedTerminals.Panic.reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReframedTerminals.Panic.reached
/-- info: 'Solidity.Backend.Passes.ReframedTerminals.Immediate.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReframedTerminals.Immediate.source
/-- info: 'Solidity.Backend.Passes.ReframedTerminals.Immediate.input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReframedTerminals.Immediate.input
/-- info: 'Solidity.Backend.Passes.ReframedTerminals.Immediate.suffix_input_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReframedTerminals.Immediate.suffix_input_refused
/-- info: 'Solidity.Backend.Passes.ReframedTerminals.Immediate.link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReframedTerminals.Immediate.link
/-- info: 'Solidity.Backend.Passes.ReframedTerminals.Immediate.stops_before_unreachable_resource' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReframedTerminals.Immediate.stops_before_unreachable_resource
/-- info: 'Solidity.Backend.Passes.ReframedTerminals.Spin.link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReframedTerminals.Spin.link
/-- info: 'Solidity.Backend.Passes.ReframedTerminals.Spin.reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReframedTerminals.Spin.reached
