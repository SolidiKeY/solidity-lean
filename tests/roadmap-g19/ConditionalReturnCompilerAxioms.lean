import Solidity.Backend.StructuredFlow.ConditionalReturnCompilerControls

/-- info: 'Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.emit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.emit

/-- info: 'Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.correct

/-- info: 'Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.Controls.core' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.Controls.core

/-- info: 'Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.Controls.emitted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.Controls.emitted

/-- info: 'Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.Controls.snapshot' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.Controls.snapshot

/-- info: 'Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.Controls.joined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.Controls.joined

/-- info: 'Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.Controls.prefix_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.Controls.prefix_typed

/-- info: 'Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.Controls.prefix_observed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.Controls.prefix_observed

/-- info: 'Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.Controls.emitted_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.Controls.emitted_split

/-- info: 'Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.Controls.capture_snapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.Controls.capture_snapshot

/-- info: 'Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.Controls.observed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.Controls.observed

/-- info: 'Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.Controls.wrong_donor_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.Controls.wrong_donor_refused

/-- info: 'Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.Controls.wrong_flag_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.Controls.wrong_flag_refused
