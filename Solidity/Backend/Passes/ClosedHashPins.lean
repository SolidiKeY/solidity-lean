import Solidity.Backend.Passes.ClosedValueControls
import Solidity.Backend.Passes.ReachedHash

/-! Exact observed standard-only closed-value and reached-hash guards. -/
/-- info: 'Solidity.Backend.Passes.ClosedValues.represented_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ClosedValues.represented_word
/-- info: 'Solidity.Backend.Passes.ClosedValues.application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ClosedValues.application
/-- info: 'Solidity.Backend.Passes.ClosedValues.prefix_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ClosedValues.prefix_capacity
/-- info: 'Solidity.Backend.Passes.ClosedValues.bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ClosedValues.bytes
/-- info: 'Solidity.Backend.Passes.ClosedValueControls.signed_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ClosedValueControls.signed_application
/-- info: 'Solidity.Backend.Passes.ClosedValueControls.boolean_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ClosedValueControls.boolean_application
/-- info: 'Solidity.Backend.Passes.ClosedValueControls.signed_reference_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ClosedValueControls.signed_reference_prefix
/-- info: 'Solidity.Backend.Passes.ClosedValueControls.ordered_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ClosedValueControls.ordered_memory
/-- info: 'Solidity.Backend.Passes.ClosedValueControls.signed_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ClosedValueControls.signed_bytes
/-- info: 'Solidity.Backend.Passes.ClosedValueControls.bool_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ClosedValueControls.bool_bytes
/-- info: 'Solidity.Backend.Passes.ClosedValueControls.noncanonical_bool' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ClosedValueControls.noncanonical_bool
/-- info: 'Solidity.Backend.Passes.ClosedValueControls.capacity_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ClosedValueControls.capacity_negative
/-- info: 'Solidity.Backend.Passes.ClosedValueControls.corrupted_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ClosedValueControls.corrupted_tail
/-- info: 'Solidity.Backend.Passes.ClosedValueControls.signedInvocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ClosedValueControls.signedInvocation
/-- info: 'Solidity.Backend.Passes.ClosedValueControls.booleanInvocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ClosedValueControls.booleanInvocation
/-- info: 'Solidity.Backend.Passes.ReachedHash.evaluated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReachedHash.evaluated
/-- info: 'Solidity.Backend.Passes.ReachedHash.input' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReachedHash.input
/-- info: 'Solidity.Backend.Passes.ReachedHash.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReachedHash.source
/-- info: 'Solidity.Backend.Passes.ReachedHash.target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReachedHash.target
/-- info: 'Solidity.Backend.Passes.ReachedHash.bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReachedHash.bytes
/-- info: 'Solidity.Backend.Passes.ReachedHash.ordered_bytes' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReachedHash.ordered_bytes
/-- info: 'Solidity.Backend.Passes.ReachedHash.stale_refused' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReachedHash.stale_refused
/-- info: 'Solidity.Backend.Passes.ReachedHash.source_path_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReachedHash.source_path_failure
/-- info: 'Solidity.Backend.Passes.ReachedHash.hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReachedHash.hash
/-- info: 'Solidity.Backend.Passes.ReachedHash.combined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReachedHash.combined
