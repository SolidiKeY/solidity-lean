import Solidity.Backend.Executable.CreationReturnInterfaceV1Controls

/-! Type and axiom observations of the H26 interface, not a producer instance. -/
#check @Solidity.Backend.Executable.CreationReturnInterfaceV1.Producer.returned_address
#check @Solidity.Backend.Executable.CreationReturnInterfaceV1.Producer.same_returns
/-- info: 'Solidity.Backend.Executable.CreationReturnInterfaceV1.Producer.returned_address' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Executable.CreationReturnInterfaceV1.Producer.returned_address
/-- info: 'Solidity.Backend.Executable.CreationReturnInterfaceV1.Producer.same_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Executable.CreationReturnInterfaceV1.Producer.same_returns
/-- info: 'Solidity.Backend.Executable.CreationReturnInterfaceV1.Controls.not_reverted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Executable.CreationReturnInterfaceV1.Controls.not_reverted
