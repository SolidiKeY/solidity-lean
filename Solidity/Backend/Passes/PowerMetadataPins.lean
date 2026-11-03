import Solidity.Backend.Passes.StatefulPowerControls
import Solidity.Backend.Passes.ResolvedMetadataControls

/-! Exact observed standard-only guards for signed-power and metadata applications. -/
/-- info: 'Solidity.Backend.Passes.StatefulPower.operands' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulPower.operands
/-- info: 'Solidity.Backend.Passes.StatefulPower.source_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulPower.source_success
/-- info: 'Solidity.Backend.Passes.StatefulPower.application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulPower.application
/-- info: 'Solidity.Backend.Passes.StatefulPower.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulPower.success
/-- info: 'Solidity.Backend.Passes.StatefulPower.failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulPower.failure
/-- info: 'Solidity.Backend.Passes.StatefulPowerControls.source_result' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulPowerControls.source_result
/-- info: 'Solidity.Backend.Passes.StatefulPowerControls.successful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulPowerControls.successful
/-- info: 'Solidity.Backend.Passes.StatefulPowerControls.component' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulPowerControls.component
/-- info: 'Solidity.Backend.Passes.StatefulPowerControls.original_capacities' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulPowerControls.original_capacities
/-- info: 'Solidity.Backend.Passes.StatefulPowerControls.operand_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulPowerControls.operand_words
/-- info: 'Solidity.Backend.Passes.StatefulPowerControls.ordered_memory' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulPowerControls.ordered_memory
/-- info: 'Solidity.Backend.Passes.StatefulPowerControls.ordered_after_power' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulPowerControls.ordered_after_power
/-- info: 'Solidity.Backend.Passes.StatefulPowerControls.after_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulPowerControls.after_source
/-- info: 'Solidity.Backend.Passes.StatefulPowerControls.reached_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulPowerControls.reached_capture
/-- info: 'Solidity.Backend.Passes.StatefulPowerControls.skipped_capture_wrong' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulPowerControls.skipped_capture_wrong
/-- info: 'Solidity.Backend.Passes.StatefulPowerControls.overflow_result' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulPowerControls.overflow_result
/-- info: 'Solidity.Backend.Passes.StatefulPowerControls.overflow_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulPowerControls.overflow_failure
/-- info: 'Solidity.Backend.Passes.StatefulPowerControls.overflow_component' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulPowerControls.overflow_component
/-- info: 'Solidity.Backend.Passes.StatefulPowerControls.reached_overflow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulPowerControls.reached_overflow
/-- info: 'Solidity.Backend.Passes.StatefulPowerControls.ignored_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulPowerControls.ignored_sign
/-- info: 'Solidity.Backend.Passes.StatefulPowerControls.capacity_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulPowerControls.capacity_refused
/-- info: 'Solidity.Backend.Passes.StatefulPowerControls.actual_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulPowerControls.actual_bytes
/-- info: 'Solidity.Backend.Passes.StatefulPowerControls.invocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulPowerControls.invocation
/-- info: 'Solidity.Backend.Passes.StatefulPowerControls.overflowInvocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.StatefulPowerControls.overflowInvocation
/-- info: 'Solidity.Backend.Passes.ResolvedMetadata.physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ResolvedMetadata.physical
/-- info: 'Solidity.Backend.Passes.ResolvedMetadata.after_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ResolvedMetadata.after_value
/-- info: 'Solidity.Backend.Passes.ResolvedMetadata.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ResolvedMetadata.certificate
/-- info: 'Solidity.Backend.Passes.ResolvedMetadata.symbolic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ResolvedMetadata.symbolic
/-- info: 'Solidity.Backend.Passes.ResolvedMetadataControls.resolved' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ResolvedMetadataControls.resolved
/-- info: 'Solidity.Backend.Passes.ResolvedMetadataControls.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ResolvedMetadataControls.source
/-- info: 'Solidity.Backend.Passes.ResolvedMetadataControls.target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ResolvedMetadataControls.target
/-- info: 'Solidity.Backend.Passes.ResolvedMetadataControls.declaration_after_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ResolvedMetadataControls.declaration_after_hash
/-- info: 'Solidity.Backend.Passes.ResolvedMetadataControls.reached_physical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ResolvedMetadataControls.reached_physical
/-- info: 'Solidity.Backend.Passes.ResolvedMetadataControls.actual_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ResolvedMetadataControls.actual_bytes
/-- info: 'Solidity.Backend.Passes.ResolvedMetadataControls.wrong_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ResolvedMetadataControls.wrong_alignment
/-- info: 'Solidity.Backend.Passes.ResolvedMetadataControls.wrong_selector' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ResolvedMetadataControls.wrong_selector
/-- info: 'Solidity.Backend.Passes.ResolvedMetadataControls.missing_refused' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ResolvedMetadataControls.missing_refused
/-- info: 'Solidity.Backend.Passes.ResolvedMetadataControls.push_capacity_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ResolvedMetadataControls.push_capacity_refused
/-- info: 'Solidity.Backend.Passes.ResolvedMetadataControls.ordered_bytes' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ResolvedMetadataControls.ordered_bytes
/-- info: 'Solidity.Backend.Passes.ResolvedMetadataControls.metadata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ResolvedMetadataControls.metadata
/-- info: 'Solidity.Backend.Passes.ResolvedMetadataControls.combined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ResolvedMetadataControls.combined
