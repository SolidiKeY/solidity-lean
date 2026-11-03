import Solidity.Backend.Passes.RevertControls

/-! Exact axiom pins for reached coarse-revert prefix witnesses. -/
/-- info: 'Solidity.Backend.Passes.compilation_mapped_revert_witness_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.compilation_mapped_revert_witness_iff
/-- info: 'Solidity.Backend.Passes.compilation_triple_revert_witness_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.compilation_triple_revert_witness_iff
/-- info: 'Solidity.Backend.Passes.compilation_triple_revert_witness_left_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.compilation_triple_revert_witness_left_iff
/-- info: 'Solidity.Backend.Passes.revert_associations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.revert_associations
/-- info: 'Solidity.Backend.Passes.joined_halt_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.joined_halt_iff
/-- info: 'Solidity.Backend.Passes.terminal_failure_errors_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.terminal_failure_errors_iff
/-- info: 'Solidity.Backend.Passes.joined_terminal_failure_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.joined_terminal_failure_iff
/-- info: 'Solidity.Backend.Passes.compilation_mapped_join_revert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.compilation_mapped_join_revert_iff
/-- info: 'Solidity.Backend.Passes.compilation_triple_join_revert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.compilation_triple_join_revert_iff
/-- info: 'Solidity.Backend.Passes.RevertControls.panic_recognized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.RevertControls.panic_recognized
/-- info: 'Solidity.Backend.Passes.RevertControls.panic_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.RevertControls.panic_source
/-- info: 'Solidity.Backend.Passes.RevertControls.panic_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.RevertControls.panic_link
/-- info: 'Solidity.Backend.Passes.RevertControls.panic_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.RevertControls.panic_reached
/-- info: 'Solidity.Backend.Passes.RevertControls.immediate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.RevertControls.immediate
/-- info: 'Solidity.Backend.Passes.RevertControls.middle_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.RevertControls.middle_witness
/-- info: 'Solidity.Backend.Passes.RevertControls.middle_triple_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.RevertControls.middle_triple_witness
/-- info: 'Solidity.Backend.Passes.RevertControls.third_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.RevertControls.third_witness
/-- info: 'Solidity.Backend.Passes.RevertControls.shared_revert_maps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.RevertControls.shared_revert_maps
/-- info: 'Solidity.Backend.Passes.RevertControls.source_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.RevertControls.source_cases
/-- info: 'Solidity.Backend.Passes.RevertControls.left_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.RevertControls.left_sources
/-- info: 'Solidity.Backend.Passes.RevertControls.left_targets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.RevertControls.left_targets
/-- info: 'Solidity.Backend.Passes.RevertControls.ordered_prefixes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.RevertControls.ordered_prefixes
/-- info: 'Solidity.Backend.Passes.RevertControls.wrong_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.RevertControls.wrong_stage
/-- info: 'Solidity.Backend.Passes.RevertControls.stale_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.RevertControls.stale_map
/-- info: 'Solidity.Backend.Passes.RevertControls.skipped_effect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.RevertControls.skipped_effect
/-- info: 'Solidity.Backend.Passes.RevertControls.recapture_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.RevertControls.recapture_negative
/-- info: 'Solidity.Backend.Passes.RevertControls.recapture_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.RevertControls.recapture_source
/-- info: 'Solidity.Backend.Passes.RevertControls.recapture_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.RevertControls.recapture_ordered
/-- info: 'Solidity.Backend.Passes.RevertControls.prefix_not_reverted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.RevertControls.prefix_not_reverted
/-- info: 'Solidity.Backend.Passes.RevertControls.coarse_not_source_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.RevertControls.coarse_not_source_identity
/-- info: 'Solidity.Backend.Passes.RevertControls.divergence_separate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.RevertControls.divergence_separate
/-- info: 'Solidity.Backend.Passes.RevertControls.ordinary_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.RevertControls.ordinary_witness
/-- info: 'Solidity.Backend.Passes.RevertControls.asserting_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.RevertControls.asserting_witness
