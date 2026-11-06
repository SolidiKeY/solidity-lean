import Solidity.Backend.Passes.SourceAdditionValueControls

/-- info: 'Solidity.Backend.Passes.SourceAdditionValue.execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.SourceAdditionValue.execution
/-- info: 'Solidity.Backend.Passes.SourceAdditionValue.Controls.actual_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.SourceAdditionValue.Controls.actual_target
/-- info: 'Solidity.Backend.Passes.SourceAdditionValue.Controls.complete_observations' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.SourceAdditionValue.Controls.complete_observations
/-- info: 'Solidity.Backend.Passes.SourceAdditionValue.Controls.saved_tail_wrong' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.SourceAdditionValue.Controls.saved_tail_wrong
/-- info: 'Solidity.Backend.Passes.SourceAdditionValue.Controls.actual_unmasked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.SourceAdditionValue.Controls.actual_unmasked
/-- info: 'Solidity.Backend.Passes.SourceAdditionValue.Controls.actual_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.SourceAdditionValue.Controls.actual_nonzero
