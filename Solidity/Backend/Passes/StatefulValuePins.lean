import Solidity.Backend.Passes.StatefulCaptureControls
import Solidity.Backend.Passes.StatefulModularControls

/-! Exact standard-only guards for state-dependent published value applications. -/
/-- info: 'Solidity.Backend.Passes.StatefulCaptureControls.capture_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulCaptureControls.capture_source
/-- info: 'Solidity.Backend.Passes.StatefulCaptureControls.declaration_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulCaptureControls.declaration_source
/-- info: 'Solidity.Backend.Passes.StatefulCaptureControls.initial_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulCaptureControls.initial_input
/-- info: 'Solidity.Backend.Passes.StatefulCaptureControls.reached_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulCaptureControls.reached_application
/-- info: 'Solidity.Backend.Passes.StatefulCaptureControls.ordered_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulCaptureControls.ordered_capture
/-- info: 'Solidity.Backend.Passes.StatefulCaptureControls.ordered_without_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulCaptureControls.ordered_without_capture
/-- info: 'Solidity.Backend.Passes.StatefulCaptureControls.afterInvocation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulCaptureControls.afterInvocation
/-- info: 'Solidity.Backend.Passes.StatefulChecked.binary_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulChecked.binary_success
/-- info: 'Solidity.Backend.Passes.StatefulChecked.binary_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulChecked.binary_failure
/-- info: 'Solidity.Backend.Passes.StatefulChecked.unary_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulChecked.unary_success
/-- info: 'Solidity.Backend.Passes.StatefulChecked.unary_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulChecked.unary_failure
/-- info: 'Solidity.Backend.Passes.StatefulDivision.physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulDivision.physical
/-- info: 'Solidity.Backend.Passes.StatefulDivision.uint_division' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulDivision.uint_division
/-- info: 'Solidity.Backend.Passes.StatefulDivision.uint_remainder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulDivision.uint_remainder
/-- info: 'Solidity.Backend.Passes.StatefulDivision.int_remainder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulDivision.int_remainder
/-- info: 'Solidity.Backend.Passes.StatefulDivision.int_division' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulDivision.int_division
/-- info: 'Solidity.Backend.Passes.StatefulModular.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulModular.source
/-- info: 'Solidity.Backend.Passes.StatefulModular.operands' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulModular.operands
/-- info: 'Solidity.Backend.Passes.StatefulModular.component' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulModular.component
/-- info: 'Solidity.Backend.Passes.StatefulModular.failure_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulModular.failure_iff
/-- info: 'Solidity.Backend.Passes.StatefulModular.certificate_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulModular.certificate_refused
/-- info: 'Solidity.Backend.Passes.StatefulModularControls.source_results' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulModularControls.source_results
/-- info: 'Solidity.Backend.Passes.StatefulModularControls.operand_words' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulModularControls.operand_words
/-- info: 'Solidity.Backend.Passes.StatefulModularControls.addition_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulModularControls.addition_application
/-- info: 'Solidity.Backend.Passes.StatefulModularControls.multiplication_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulModularControls.multiplication_application
/-- info: 'Solidity.Backend.Passes.StatefulModularControls.zero_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulModularControls.zero_application
/-- info: 'Solidity.Backend.Passes.StatefulModularControls.whole_compiler_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulModularControls.whole_compiler_refused
/-- info: 'Solidity.Backend.Passes.StatefulModularControls.actual_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulModularControls.actual_bytes
/-- info: 'Solidity.Backend.Passes.StatefulModularControls.ignoring_zero_guard' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulModularControls.ignoring_zero_guard
/-- info: 'Solidity.Backend.Passes.StatefulSpecialControls.signed_second_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulSpecialControls.signed_second_source
/-- info: 'Solidity.Backend.Passes.StatefulSpecialControls.source_results' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulSpecialControls.source_results
/-- info: 'Solidity.Backend.Passes.StatefulSpecialControls.uDiv_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulSpecialControls.uDiv_application
/-- info: 'Solidity.Backend.Passes.StatefulSpecialControls.uMod_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulSpecialControls.uMod_application
/-- info: 'Solidity.Backend.Passes.StatefulSpecialControls.iMod_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulSpecialControls.iMod_application
/-- info: 'Solidity.Backend.Passes.StatefulSpecialControls.iDiv_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulSpecialControls.iDiv_application
/-- info: 'Solidity.Backend.Passes.StatefulSpecialControls.zero_division' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulSpecialControls.zero_division
/-- info: 'Solidity.Backend.Passes.StatefulSpecialControls.signed_overflow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulSpecialControls.signed_overflow
/-- info: 'Solidity.Backend.Passes.StatefulSpecialControls.distinct_failure_bytes' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulSpecialControls.distinct_failure_bytes
/-- info: 'Solidity.Backend.Passes.StatefulSpecialControls.body_bytes' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulSpecialControls.body_bytes
/-- info: 'Solidity.Backend.Passes.StatefulValueControls.wrapping_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueControls.wrapping_source
/-- info: 'Solidity.Backend.Passes.StatefulValueControls.comparison_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueControls.comparison_source
/-- info: 'Solidity.Backend.Passes.StatefulValueControls.signed_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueControls.signed_source
/-- info: 'Solidity.Backend.Passes.StatefulValueControls.negated_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueControls.negated_source
/-- info: 'Solidity.Backend.Passes.StatefulValueControls.operand_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueControls.operand_words
/-- info: 'Solidity.Backend.Passes.StatefulValueControls.wrapping_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueControls.wrapping_application
/-- info: 'Solidity.Backend.Passes.StatefulValueControls.comparison_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueControls.comparison_application
/-- info: 'Solidity.Backend.Passes.StatefulValueControls.cast_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueControls.cast_application
/-- info: 'Solidity.Backend.Passes.StatefulValueControls.negation_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueControls.negation_application
/-- info: 'Solidity.Backend.Passes.StatefulValueControls.actual_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueControls.actual_bytes
/-- info: 'Solidity.Backend.Passes.StatefulValueControls.empty_cast_component' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueControls.empty_cast_component
/-- info: 'Solidity.Backend.Passes.StatefulValueControls.ordered_memory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueControls.ordered_memory
/-- info: 'Solidity.Backend.Passes.StatefulValueControls.wrapping_after_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueControls.wrapping_after_capture
/-- info: 'Solidity.Backend.Passes.StatefulValueControls.not_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueControls.not_closed
/-- info: 'Solidity.Backend.Passes.StatefulValueControls.checked_binary_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueControls.checked_binary_success
/-- info: 'Solidity.Backend.Passes.StatefulValueControls.wrappingInvocation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueControls.wrappingInvocation
/-- info: 'Solidity.Backend.Passes.StatefulValueControls.comparisonInvocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueControls.comparisonInvocation
/-- info: 'Solidity.Backend.Passes.StatefulValueControls.checkedInvocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueControls.checkedInvocation
/-- info: 'Solidity.Backend.Passes.StatefulValueNegatives.nine_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueNegatives.nine_source
/-- info: 'Solidity.Backend.Passes.StatefulValueNegatives.underflow_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueNegatives.underflow_application
/-- info: 'Solidity.Backend.Passes.StatefulValueNegatives.minimum_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueNegatives.minimum_input
/-- info: 'Solidity.Backend.Passes.StatefulValueNegatives.minimum_operand_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueNegatives.minimum_operand_source
/-- info: 'Solidity.Backend.Passes.StatefulValueNegatives.minimum_negation_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueNegatives.minimum_negation_application
/-- info: 'Solidity.Backend.Passes.StatefulValueNegatives.ignored_negation_guard' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueNegatives.ignored_negation_guard
/-- info: 'Solidity.Backend.Passes.StatefulValueNegatives.negation_guard_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueNegatives.negation_guard_bytes
/-- info: 'Solidity.Backend.Passes.StatefulValueNegatives.false_guard_taken' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueNegatives.false_guard_taken
/-- info: 'Solidity.Backend.Passes.StatefulValueNegatives.eager_guard_refused' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueNegatives.eager_guard_refused
/-- info: 'Solidity.Backend.Passes.StatefulValueNegatives.skipped_rhs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueNegatives.skipped_rhs
/-- info: 'Solidity.Backend.Passes.StatefulValueNegatives.reached_rhs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueNegatives.reached_rhs
/-- info: 'Solidity.Backend.Passes.StatefulValueNegatives.failed_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueNegatives.failed_left
/-- info: 'Solidity.Backend.Passes.StatefulValueNegatives.eager_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueNegatives.eager_failure
/-- info: 'Solidity.Backend.Passes.StatefulValueNegatives.reversed_numeric' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueNegatives.reversed_numeric
/-- info: 'Solidity.Backend.Passes.StatefulValueNegatives.capacity_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueNegatives.capacity_refused
/-- info: 'Solidity.Backend.Passes.StatefulValueNegatives.operand_corruption' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueNegatives.operand_corruption
/-- info: 'Solidity.Backend.Passes.StatefulValueNegatives.minimum_reached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueNegatives.minimum_reached
/-- info: 'Solidity.Backend.Passes.StatefulValueNegatives.minimum_prefix_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueNegatives.minimum_prefix_failure
/-- info: 'Solidity.Backend.Passes.StatefulValueNegatives.underflowInvocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValueNegatives.underflowInvocation
/-- info: 'Solidity.Backend.Passes.StatefulValues.binary_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValues.binary_source
/-- info: 'Solidity.Backend.Passes.StatefulValues.unary_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValues.unary_source
/-- info: 'Solidity.Backend.Passes.StatefulValues.operands' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValues.operands
/-- info: 'Solidity.Backend.Passes.StatefulValues.binary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValues.binary
/-- info: 'Solidity.Backend.Passes.StatefulValues.unary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValues.unary
/-- info: 'Solidity.Backend.Passes.StatefulValues.binary_revert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValues.binary_revert_iff
/-- info: 'Solidity.Backend.Passes.StatefulValues.left_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValues.left_revert
/-- info: 'Solidity.Backend.Passes.StatefulValues.right_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValues.right_revert
/-- info: 'Solidity.Backend.Passes.StatefulValues.short_taken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulValues.short_taken
