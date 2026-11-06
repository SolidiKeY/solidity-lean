import Solidity.Backend.Passes.PublishedValueControls
import Solidity.Backend.Passes.PublishedMixedCapture

/-! Exact observed standard-only published-application guards. -/
/-- info: 'Solidity.Backend.Passes.PublishedValues.encode_wrap_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValues.encode_wrap_sub
/-- info: 'Solidity.Backend.Passes.PublishedValues.sub_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValues.sub_result
/-- info: 'Solidity.Backend.Passes.PublishedValues.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValues.source
/-- info: 'Solidity.Backend.Passes.PublishedValues.suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValues.suffix
/-- info: 'Solidity.Backend.Passes.PublishedValues.operands' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValues.operands
/-- info: 'Solidity.Backend.Passes.PublishedValues.mixed_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValues.mixed_run
/-- info: 'Solidity.Backend.Passes.PublishedValues.symbolic_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValues.symbolic_value
/-- info: 'Solidity.Backend.Passes.PublishedValues.represented_word' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValues.represented_word
/-- info: 'Solidity.Backend.Passes.PublishedValues.checked_application' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValues.checked_application
/-- info: 'Solidity.Backend.Passes.PublishedValues.decode_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValues.decode_code
/-- info: 'Solidity.Backend.Passes.PublishedValueControls.represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValueControls.represented
/-- info: 'Solidity.Backend.Passes.PublishedValueControls.physical_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValueControls.physical_input
/-- info: 'Solidity.Backend.Passes.PublishedValueControls.intrinsic_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValueControls.intrinsic_value
/-- info: 'Solidity.Backend.Passes.PublishedValueControls.physical_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValueControls.physical_value
/-- info: 'Solidity.Backend.Passes.PublishedValueControls.instructions' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValueControls.instructions
/-- info: 'Solidity.Backend.Passes.PublishedValueControls.bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValueControls.bytes
/-- info: 'Solidity.Backend.Passes.PublishedValueControls.byte_roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValueControls.byte_roundtrip
/-- info: 'Solidity.Backend.Passes.PublishedValueControls.numeric_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValueControls.numeric_tail
/-- info: 'Solidity.Backend.Passes.PublishedValueControls.wrong_environment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValueControls.wrong_environment
/-- info: 'Solidity.Backend.Passes.PublishedValueControls.wrong_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValueControls.wrong_order
/-- info: 'Solidity.Backend.Passes.PublishedValueControls.self_balance_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValueControls.self_balance_refused
/-- info: 'Solidity.Backend.Passes.PublishedValueControls.actual_prefix_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValueControls.actual_prefix_capacity
/-- info: 'Solidity.Backend.Passes.PublishedValueControls.capacity_negative' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValueControls.capacity_negative
/-- info: 'Solidity.Backend.Passes.PublishedValueControls.reached_guard_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValueControls.reached_guard_prefix
/-- info: 'Solidity.Backend.Passes.PublishedValueControls.reached_guard' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValueControls.reached_guard
/-- info: 'Solidity.Backend.Passes.PublishedValueControls.guard_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValueControls.guard_bytes
/-- info: 'Solidity.Backend.Passes.PublishedValueControls.guard_is_not_division' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValueControls.guard_is_not_division
/-- info: 'Solidity.Backend.Passes.PublishedValueControls.ignored_guard' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValueControls.ignored_guard
/-- info: 'Solidity.Backend.Passes.PublishedValueControls.actual_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValueControls.actual_observation
/-- info: 'Solidity.Backend.Passes.PublishedValueControls.intrinsic_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValueControls.intrinsic_failure
/-- info: 'Solidity.Backend.Passes.PublishedValueControls.coarse_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValueControls.coarse_failure
/-- info: 'Solidity.Backend.Passes.PublishedMixedCapture.reached_environment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedMixedCapture.reached_environment
/-- info: 'Solidity.Backend.Passes.PublishedMixedCapture.expression_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedMixedCapture.expression_source
/-- info: 'Solidity.Backend.Passes.PublishedMixedCapture.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedMixedCapture.program_source
/-- info: 'Solidity.Backend.Passes.PublishedMixedCapture.link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedMixedCapture.link
/-- info: 'Solidity.Backend.Passes.PublishedMixedCapture.reached_composition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedMixedCapture.reached_composition
/-- info: 'Solidity.Backend.Passes.PublishedMixedCapture.numeric_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedMixedCapture.numeric_tail
/-- info: 'Solidity.Backend.Passes.PublishedMixedCapture.ordered_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedMixedCapture.ordered_observations
/-- info: 'Solidity.Backend.Passes.PublishedValues.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedValues.certificate
/-- info: 'Solidity.Backend.Passes.PublishedMixedCapture.numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.PublishedMixedCapture.numeric
