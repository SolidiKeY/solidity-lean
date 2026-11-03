import Solidity.Backend.Passes.TripleSuffix
import Solidity.Backend.Passes.TripleFailures

/-! Exact axiom inventory for correlated three-stage certificates. -/
/-- info: 'Solidity.Backend.Passes.memory_third_budgeted_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.memory_third_budgeted_link
/-- info: 'Solidity.Backend.Passes.compilation_triple_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.compilation_triple_success
/-- info: 'Solidity.Backend.Passes.compilation_triple_revert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.compilation_triple_revert_iff
/-- info: 'Solidity.Backend.Passes.memory_triple_resources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.memory_triple_resources
/-- info: 'Solidity.Backend.Passes.triple_source_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.triple_source_success
/-- info: 'Solidity.Backend.Passes.compilation_triple_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.compilation_triple_shared
/-- info: 'Solidity.Backend.Passes.TripleControls.initial_repr7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleControls.initial_repr7
/-- info: 'Solidity.Backend.Passes.TripleControls.prefix_input7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleControls.prefix_input7
/-- info: 'Solidity.Backend.Passes.TripleControls.capture_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleControls.capture_source
/-- info: 'Solidity.Backend.Passes.TripleControls.observe_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleControls.observe_source
/-- info: 'Solidity.Backend.Passes.TripleControls.first_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleControls.first_link
/-- info: 'Solidity.Backend.Passes.TripleControls.second_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleControls.second_link
/-- info: 'Solidity.Backend.Passes.TripleControls.fresh_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleControls.fresh_source
/-- info: 'Solidity.Backend.Passes.TripleControls.shared_resources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleControls.shared_resources
/-- info: 'Solidity.Backend.Passes.TripleControls.ordered_results' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleControls.ordered_results
/-- info: 'Solidity.Backend.Passes.TripleControls.stale_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleControls.stale_map
/-- info: 'Solidity.Backend.Passes.TripleControls.corruption' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleControls.corruption
/-- info: 'Solidity.Backend.Passes.TripleFailures.first_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleFailures.first_source
/-- info: 'Solidity.Backend.Passes.TripleFailures.first_short_circuit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleFailures.first_short_circuit
/-- info: 'Solidity.Backend.Passes.TripleFailures.second_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleFailures.second_reached
/-- info: 'Solidity.Backend.Passes.TripleFailures.third_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleFailures.third_source
/-- info: 'Solidity.Backend.Passes.TripleFailures.third_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleFailures.third_reached
/-- info: 'Solidity.Backend.Passes.TripleFailures.joined_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleFailures.joined_sources
/-- info: 'Solidity.Backend.Passes.TripleFailures.ordered_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleFailures.ordered_prefix
/-- info: 'Solidity.Backend.Passes.TripleAllocation.source_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleAllocation.source_success
/-- info: 'Solidity.Backend.Passes.TripleAllocation.source_observation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleAllocation.source_observation
/-- info: 'Solidity.Backend.Passes.TripleAllocation.allocating_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleAllocation.allocating_link
/-- info: 'Solidity.Backend.Passes.TripleAllocation.capture_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleAllocation.capture_link
/-- info: 'Solidity.Backend.Passes.TripleAllocation.resources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleAllocation.resources
/-- info: 'Solidity.Backend.Passes.TripleAllocation.ordered_results' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleAllocation.ordered_results
/-- info: 'Solidity.Backend.Passes.TripleAllocation.stale_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleAllocation.stale_new
/-- info: 'Solidity.Backend.Passes.TripleAllocation.stale_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleAllocation.stale_initial
/-- info: 'Solidity.Backend.Passes.TripleAllocation.shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleAllocation.shared
/-- info: 'Solidity.Backend.Passes.TripleSuffix.last_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleSuffix.last_source
/-- info: 'Solidity.Backend.Passes.TripleSuffix.last_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleSuffix.last_link
/-- info: 'Solidity.Backend.Passes.TripleSuffix.resources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleSuffix.resources
/-- info: 'Solidity.Backend.Passes.TripleSuffix.ordered_results' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleSuffix.ordered_results
/-- info: 'Solidity.Backend.Passes.TripleSuffix.shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.TripleSuffix.shared
