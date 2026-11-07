import Solidity.Backend.Executable.CreationReturnPartitionControls

/-! Scoped kernel-byte classification audit, not Source provenance. -/
#check @Solidity.Backend.Executable.CreationReturnPartition.partition
#check @Solidity.Backend.Executable.CreationReturnPartition.cross_exclusive
/-- info: 'Solidity.Backend.Executable.CreationReturnPartition.partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Executable.CreationReturnPartition.partition
/-- info: 'Solidity.Backend.Executable.CreationReturnPartition.cross_exclusive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Executable.CreationReturnPartition.cross_exclusive
/-- info: 'Solidity.Backend.Executable.CreationReturnPartition.Controls.boundaries' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Executable.CreationReturnPartition.Controls.boundaries
/-- info: 'Solidity.Backend.Executable.CreationReturnPartition.Controls.no_argument_at_return_end' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Executable.CreationReturnPartition.Controls.no_argument_at_return_end
