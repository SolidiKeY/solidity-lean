import Solidity.Backend.Passes.DivergenceControls
import Solidity.Backend.Passes.TerminalReflection

/-! Exact axiom pins for internal terminal divergence and reflection. -/
/-- info: 'Solidity.Backend.Passes.compilation_fault_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.compilation_fault_iff
/-- info: 'Solidity.Backend.Passes.compilation_fault_tail_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.compilation_fault_tail_iff
/-- info: 'Solidity.Backend.Passes.compilation_mapped_fault_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.compilation_mapped_fault_iff
/-- info: 'Solidity.Backend.Passes.compilation_triple_fault_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.compilation_triple_fault_iff
/-- info: 'Solidity.Backend.Passes.joined_diverge_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.joined_diverge_iff
/-- info: 'Solidity.Backend.Passes.compilation_mapped_join_fault_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.compilation_mapped_join_fault_iff
/-- info: 'Solidity.Backend.Passes.compilation_triple_join_fault_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.compilation_triple_join_fault_iff
/-- info: 'Solidity.Backend.Passes.compilation_mapped_fault_witness_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.compilation_mapped_fault_witness_iff
/-- info: 'Solidity.Backend.Passes.compilation_triple_fault_witness_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.compilation_triple_fault_witness_iff
/-- info: 'Solidity.Backend.Passes.triple_fault_associations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.triple_fault_associations
/-- info: 'Solidity.Backend.Passes.Spin.iter' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.Spin.iter
/-- info: 'Solidity.Backend.Passes.Spin.diverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.Spin.diverges
/-- info: 'Solidity.Backend.Passes.Spin.existing_program' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.Spin.existing_program
/-- info: 'Solidity.Backend.Passes.Spin.memory_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.Spin.memory_link
/-- info: 'Solidity.Backend.Passes.Spin.unreachable_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.Spin.unreachable_link
/-- info: 'Solidity.Backend.Passes.Spin.fault_all_tails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.Spin.fault_all_tails
/-- info: 'Solidity.Backend.Passes.DivergenceControls.initial_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.DivergenceControls.initial_input
/-- info: 'Solidity.Backend.Passes.DivergenceControls.immediate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.DivergenceControls.immediate
/-- info: 'Solidity.Backend.Passes.DivergenceControls.middle_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.DivergenceControls.middle_link
/-- info: 'Solidity.Backend.Passes.DivergenceControls.middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.DivergenceControls.middle
/-- info: 'Solidity.Backend.Passes.DivergenceControls.last_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.DivergenceControls.last_link
/-- info: 'Solidity.Backend.Passes.DivergenceControls.third' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.DivergenceControls.third
/-- info: 'Solidity.Backend.Passes.DivergenceControls.source_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.DivergenceControls.source_cases
/-- info: 'Solidity.Backend.Passes.DivergenceControls.left_targets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.DivergenceControls.left_targets
/-- info: 'Solidity.Backend.Passes.DivergenceControls.left_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.DivergenceControls.left_sources
/-- info: 'Solidity.Backend.Passes.DivergenceControls.revert_before_spin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.DivergenceControls.revert_before_spin
/-- info: 'Solidity.Backend.Passes.DivergenceControls.shared_prefix_maps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.DivergenceControls.shared_prefix_maps
/-- info: 'Solidity.Backend.Passes.DivergenceControls.reached_maps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.DivergenceControls.reached_maps
/-- info: 'Solidity.Backend.Passes.DivergenceControls.ordered_prefixes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.DivergenceControls.ordered_prefixes
/-- info: 'Solidity.Backend.Passes.compilation_mapped_reflect_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.compilation_mapped_reflect_success
/-- info: 'Solidity.Backend.Passes.compilation_triple_reflect_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.compilation_triple_reflect_success
/-- info: 'Solidity.Backend.Passes.terminal_reflection_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.terminal_reflection_inhabited
