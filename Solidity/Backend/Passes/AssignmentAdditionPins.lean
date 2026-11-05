import Solidity.Backend.Passes.AssignmentAdditionControls

/-- info: 'Solidity.Backend.Passes.AssignmentAdditionPass.reached_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.AssignmentAdditionPass.reached_value
/-- info: 'Solidity.Backend.Passes.AssignmentAdditionPass.execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.AssignmentAdditionPass.execution
/-- info: 'Solidity.Backend.Passes.AssignmentAdditionPass.Controls.application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.AssignmentAdditionPass.Controls.application
/-- info: 'Solidity.Backend.Passes.AssignmentAdditionPass.Controls.emitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.AssignmentAdditionPass.Controls.emitted
/-- info: 'Solidity.Backend.Passes.AssignmentAdditionPass.Controls.source_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.AssignmentAdditionPass.Controls.source_execution
/-- info: 'Solidity.Backend.Passes.AssignmentAdditionPass.Controls.complete_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.AssignmentAdditionPass.Controls.complete_observations
/-- info: 'Solidity.Backend.Passes.AssignmentAdditionPass.Controls.different_pipelines' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.AssignmentAdditionPass.Controls.different_pipelines
/-- info: 'Solidity.Backend.Passes.AssignmentAdditionPass.Controls.stale_rhs_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.AssignmentAdditionPass.Controls.stale_rhs_refused
/-- info: 'Solidity.Backend.Passes.AssignmentAdditionPass.Controls.short_frame_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.AssignmentAdditionPass.Controls.short_frame_refused
/-- info: 'Solidity.Backend.Passes.AssignmentAdditionPass.Controls.corrupted_saved_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.AssignmentAdditionPass.Controls.corrupted_saved_tail
