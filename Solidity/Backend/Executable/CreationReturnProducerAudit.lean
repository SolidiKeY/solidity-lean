import Solidity.Backend.Executable.CreationReturnProducerControls

/-! Kernel constructor-return interface discharge, not Source/CREATE closure. -/
#check @Solidity.Backend.Executable.CreationReturnProducer.producer
#check @Solidity.Backend.Executable.CreationReturnProducer.returned_equal_iff
/-- info: 'Solidity.Backend.Executable.CreationReturnProducer.producer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Executable.CreationReturnProducer.producer
/-- info: 'Solidity.Backend.Executable.CreationReturnProducer.link_congr' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Executable.CreationReturnProducer.link_congr
/-- info: 'Solidity.Backend.Executable.CreationReturnProducer.returned_equal_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Executable.CreationReturnProducer.returned_equal_iff
/-- info: 'Solidity.Backend.Executable.CreationReturnProducer.Controls.unused_same_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Executable.CreationReturnProducer.Controls.unused_same_return
/-- info: 'Solidity.Backend.Executable.CreationReturnProducer.Controls.referenced_difference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Executable.CreationReturnProducer.Controls.referenced_difference
