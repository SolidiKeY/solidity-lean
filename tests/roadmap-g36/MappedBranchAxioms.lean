import Solidity.Backend.StructuredFlow.MappedBranchControls

/-- info: 'Solidity.Backend.StructuredFlow.MappedBranch.condition' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedBranch.condition

/-- info: 'Solidity.Backend.StructuredFlow.MappedBranch.emit' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedBranch.emit

/-- info: 'Solidity.Backend.StructuredFlow.MappedBranch.program' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedBranch.program

/-- info: 'Solidity.Backend.StructuredFlow.MappedBranch.code_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedBranch.code_exact

/-- info: 'Solidity.Backend.StructuredFlow.MappedBranch.condition_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedBranch.condition_run

/-- info: 'Solidity.Backend.StructuredFlow.MappedBranch.condition_represented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedBranch.condition_represented

/-- info: 'Solidity.Backend.StructuredFlow.MappedBranch.true_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedBranch.true_run

/-- info: 'Solidity.Backend.StructuredFlow.MappedBranch.true_pending_skip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedBranch.true_pending_skip

/-- info: 'Solidity.Backend.StructuredFlow.MappedBranch.admitted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedBranch.admitted

/-- info: 'Solidity.Backend.StructuredFlow.MappedBranch.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedBranch.correct

/-- info: 'Solidity.Backend.StructuredFlow.MappedBranch.Controls.left' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedBranch.Controls.left

/-- info: 'Solidity.Backend.StructuredFlow.MappedBranch.Controls.right' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedBranch.Controls.right

/-- info: 'Solidity.Backend.StructuredFlow.MappedBranch.Controls.core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedBranch.Controls.core

/-- info: 'Solidity.Backend.StructuredFlow.MappedBranch.Controls.emitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedBranch.Controls.emitted

/-- info: 'Solidity.Backend.StructuredFlow.MappedBranch.Controls.bad_emitted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedBranch.Controls.bad_emitted

/-- info: 'Solidity.Backend.StructuredFlow.MappedBranch.Controls.exitObservation' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedBranch.Controls.exitObservation

/-- info: 'Solidity.Backend.StructuredFlow.MappedBranch.Controls.condition_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedBranch.Controls.condition_code

/-- info: 'Solidity.Backend.StructuredFlow.MappedBranch.Controls.arm_codes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedBranch.Controls.arm_codes

/-- info: 'Solidity.Backend.StructuredFlow.MappedBranch.Controls.emitted_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedBranch.Controls.emitted_code

/-- info: 'Solidity.Backend.StructuredFlow.MappedBranch.Controls.checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedBranch.Controls.checked

/-- info: 'Solidity.Backend.StructuredFlow.MappedBranch.Controls.typed_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedBranch.Controls.typed_run

/-- info: 'Solidity.Backend.StructuredFlow.MappedBranch.Controls.frame_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedBranch.Controls.frame_observation

/-- info: 'Solidity.Backend.StructuredFlow.MappedBranch.Controls.wrong_capture_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedBranch.Controls.wrong_capture_refused

/-- info: 'Solidity.Backend.StructuredFlow.MappedBranch.Controls.pending_exit_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedBranch.Controls.pending_exit_exact

/-- info: 'Solidity.Backend.StructuredFlow.MappedBranch.Controls.short_exit_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedBranch.Controls.short_exit_refused

/-- info: 'Solidity.Backend.StructuredFlow.MappedBranch.Controls.unsupported_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedBranch.Controls.unsupported_refused
