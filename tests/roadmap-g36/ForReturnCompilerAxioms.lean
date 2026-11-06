import Solidity.Backend.StructuredFlow.ForReturnCompilerControls

/-- info: 'Solidity.Backend.StructuredFlow.ForReturnCompiler.emit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.ForReturnCompiler.emit

/-- info: 'Solidity.Backend.StructuredFlow.ForReturnCompiler.code_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.ForReturnCompiler.code_exact

/-- info: 'Solidity.Backend.StructuredFlow.ForReturnCompiler.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.ForReturnCompiler.correct

/-- info: 'Solidity.Backend.StructuredFlow.ForReturnCompiler.Controls.joined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.ForReturnCompiler.Controls.joined

/-- info: 'Solidity.Backend.StructuredFlow.ForReturnCompiler.Controls.observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.ForReturnCompiler.Controls.observed

/-- info: 'Solidity.Backend.StructuredFlow.ForReturnCompiler.Controls.nonzero_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.ForReturnCompiler.Controls.nonzero_frame

/-- info: 'Solidity.Backend.StructuredFlow.ForReturnCompiler.Controls.wrong_flag_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.ForReturnCompiler.Controls.wrong_flag_refused

/-- info: 'Solidity.Backend.StructuredFlow.ForReturnCompiler.Controls.wrong_base_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.ForReturnCompiler.Controls.wrong_base_refused

/-- info: 'Solidity.Backend.StructuredFlow.ForReturnCompiler.Controls.true_not_fallthrough' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.ForReturnCompiler.Controls.true_not_fallthrough

/-- info: 'Solidity.Backend.StructuredFlow.ForReturnCompiler.Controls.false_not_return' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.StructuredFlow.ForReturnCompiler.Controls.false_not_return
