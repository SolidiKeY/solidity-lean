import Solidity.Backend.StructuredFlow.MappedConditionControls

/-- info: 'Solidity.Backend.StructuredFlow.MappedCondition.emit' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedCondition.emit

/-- info: 'Solidity.Backend.StructuredFlow.MappedCondition.after' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedCondition.after

/-- info: 'Solidity.Backend.StructuredFlow.MappedCondition.code_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedCondition.code_exact

/-- info: 'Solidity.Backend.StructuredFlow.MappedCondition.admitted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedCondition.admitted

/-- info: 'Solidity.Backend.StructuredFlow.MappedCondition.run_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedCondition.run_exact

/-- info: 'Solidity.Backend.StructuredFlow.MappedCondition.postSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedCondition.postSim

/-- info: 'Solidity.Backend.StructuredFlow.MappedCondition.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedCondition.correct

/-- info: 'Solidity.Backend.StructuredFlow.MappedCondition.Controls.C' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedCondition.Controls.C

/-- info: 'Solidity.Backend.StructuredFlow.MappedCondition.Controls.mapping' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedCondition.Controls.mapping

/-- info: 'Solidity.Backend.StructuredFlow.MappedCondition.Controls.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedCondition.Controls.initial

/-- info: 'Solidity.Backend.StructuredFlow.MappedCondition.Controls.machine' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedCondition.Controls.machine

/-- info: 'Solidity.Backend.StructuredFlow.MappedCondition.Controls.caller' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedCondition.Controls.caller

/-- info: 'Solidity.Backend.StructuredFlow.MappedCondition.Controls.loaded' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedCondition.Controls.loaded

/-- info: 'Solidity.Backend.StructuredFlow.MappedCondition.Controls.snapshot' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedCondition.Controls.snapshot

/-- info: 'Solidity.Backend.StructuredFlow.MappedCondition.Controls.frame' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedCondition.Controls.frame

/-- info: 'Solidity.Backend.StructuredFlow.MappedCondition.Controls.wrongCapture' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedCondition.Controls.wrongCapture

/-- info: 'Solidity.Backend.StructuredFlow.MappedCondition.Controls.represented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedCondition.Controls.represented

/-- info: 'Solidity.Backend.StructuredFlow.MappedCondition.Controls.checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedCondition.Controls.checked

/-- info: 'Solidity.Backend.StructuredFlow.MappedCondition.Controls.post_representation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedCondition.Controls.post_representation

/-- info: 'Solidity.Backend.StructuredFlow.MappedCondition.Controls.nonzero_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedCondition.Controls.nonzero_frame

/-- info: 'Solidity.Backend.StructuredFlow.MappedCondition.Controls.self_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedCondition.Controls.self_alias

/-- info: 'Solidity.Backend.StructuredFlow.MappedCondition.Controls.stale_capture_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedCondition.Controls.stale_capture_refused

/-- info: 'Solidity.Backend.StructuredFlow.MappedCondition.Controls.wrong_base_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.MappedCondition.Controls.wrong_base_refused
