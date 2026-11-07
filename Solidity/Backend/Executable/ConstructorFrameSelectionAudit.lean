import Solidity.Backend.Executable.ConstructorFrameSelection

/-! Scoped native-frame audit; no Source admission or fetched-EVM claim. -/
#check @Solidity.Backend.Executable.ConstructorFrameSelection.endpoint
/-- info: 'Solidity.Backend.Executable.ConstructorFrameSelection.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Executable.ConstructorFrameSelection.endpoint
/-- info: 'Solidity.Backend.Executable.ConstructorFrameSelection.wrong_order' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Executable.ConstructorFrameSelection.wrong_order
/-- info: 'Solidity.Backend.Executable.ConstructorFrameSelection.preserved_contents' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Executable.ConstructorFrameSelection.preserved_contents
