import Solidity.Backend.Passes.ReachabilityControls
import Solidity.Backend.Passes.AllocatingControls
import Solidity.Backend.Passes.ReferenceControls

/-! Kernel axiom pins for the V09 compiler adapters and inhabited controls. -/
namespace Solidity.Backend.Passes

/-- info: 'Solidity.Backend.Passes.compilation_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms compilation_exact

/-- info: 'Solidity.Backend.Passes.compilation_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms compilation_success

/-- info: 'Solidity.Backend.Passes.compilation_reflect_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms compilation_reflect_success

/-- info: 'Solidity.Backend.Passes.compilation_revert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms compilation_revert_iff

/-- info: 'Solidity.Backend.Passes.compilation_input_stack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms compilation_input_stack

/-- info: 'Solidity.Backend.Passes.compilation_success_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms compilation_success_tail

/-- info: 'Solidity.Backend.Passes.compilation_sequence_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms compilation_sequence_success

/-- info: 'Solidity.Backend.Passes.compilation_sequence_revert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms compilation_sequence_revert_iff

/-- info: 'Solidity.Backend.Passes.memory_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms memory_frame

/-- info: 'Solidity.Backend.Passes.memory_extend_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms memory_extend_value

/-- info: 'Solidity.Backend.Passes.value_success_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms value_success_tail

/-- info: 'Solidity.Backend.Passes.value_revert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms value_revert_iff

/-- info: 'Solidity.Backend.Passes.Controls.whole_program_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Controls.whole_program_refused

/-- info: 'Solidity.Backend.Passes.Controls.mixed_success_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Controls.mixed_success_tail

/-- info: 'Solidity.Backend.Passes.Controls.wrong_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Controls.wrong_order

/-- info: 'Solidity.Backend.Passes.Controls.fragment_cherry_picking' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Controls.fragment_cherry_picking

/-- info: 'Solidity.Backend.Passes.LinkedControls.concrete_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LinkedControls.concrete_link

/-- info: 'Solidity.Backend.Passes.LinkedControls.linked_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LinkedControls.linked_success

/-- info: 'Solidity.Backend.Passes.LinkedControls.fresh_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LinkedControls.fresh_value

/-- info: 'Solidity.Backend.Passes.ExpressionControls.short_circuit_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ExpressionControls.short_circuit_tail

/-- info: 'Solidity.Backend.Passes.ExpressionControls.captured_pair_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ExpressionControls.captured_pair_certificate


/-- info: 'Solidity.Backend.Passes.typed_sequencing_assoc' depends on axioms: [propext] -/
#guard_msgs in #print axioms typed_sequencing_assoc
/-- info: 'Solidity.Backend.Passes.compilation_sequence_associative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms compilation_sequence_associative
/-- info: 'Solidity.Backend.Passes.LinkedControls.left_stage_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LinkedControls.left_stage_failure

/-- info: 'Solidity.Backend.Passes.Controls.accepted_stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Controls.accepted_stages
/-- info: 'Solidity.Backend.Passes.Controls.compiler_not_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Controls.compiler_not_empty
/-- info: 'Solidity.Backend.Passes.LinkedControls.right_stage_source_revert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms LinkedControls.right_stage_source_revert
/-- info: 'Solidity.Backend.Passes.ExpressionControls.selected_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExpressionControls.selected_failure
/-- info: 'Solidity.Backend.Passes.ReachabilityControls.fresh_state_reaches_fixture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ReachabilityControls.fresh_state_reaches_fixture
/-- info: 'Solidity.Backend.Passes.ReachabilityControls.concrete_tail_independence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ReachabilityControls.concrete_tail_independence
/-- info: 'Solidity.Backend.Passes.ReachabilityControls.reachable_nontrivial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ReachabilityControls.reachable_nontrivial

/-- info: 'Solidity.Backend.Passes.mapped_output_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mapped_output_iff
/-- info: 'Solidity.Backend.Passes.memory_nonallocating_mapped_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memory_nonallocating_mapped_link
/-- info: 'Solidity.Backend.Passes.memory_budgeted_mapped_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memory_budgeted_mapped_link
/-- info: 'Solidity.Backend.Passes.compilation_mapped_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms compilation_mapped_success
/-- info: 'Solidity.Backend.Passes.memory_mapped_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memory_mapped_success
/-- info: 'Solidity.Backend.Passes.memory_sequence_resources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memory_sequence_resources
/-- info: 'Solidity.Backend.Passes.compilation_mapped_revert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms compilation_mapped_revert_iff
/-- info: 'Solidity.Backend.Passes.AllocatingControls.allocating_composition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms AllocatingControls.allocating_composition
/-- info: 'Solidity.Backend.Passes.AllocatingControls.stale_map_impossible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms AllocatingControls.stale_map_impossible
/-- info: 'Solidity.Backend.Passes.AllocatingControls.reached_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AllocatingControls.reached_failure
/-- info: 'Solidity.Backend.Passes.AllocatingControls.populated_allocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms AllocatingControls.populated_allocation
/-- info: 'Solidity.Backend.Passes.ReferenceControls.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ReferenceControls.certificate
/-- info: 'Solidity.Backend.Passes.ReferenceControls.both_source_branches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ReferenceControls.both_source_branches
/-- info: 'Solidity.Backend.Passes.ReferenceControls.both_target_branches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ReferenceControls.both_target_branches
/-- info: 'Solidity.Backend.Passes.ReferenceControls.wrong_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ReferenceControls.wrong_order
/-- info: 'Solidity.Backend.Passes.ReferenceControls.reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ReferenceControls.reachable

end Solidity.Backend.Passes
