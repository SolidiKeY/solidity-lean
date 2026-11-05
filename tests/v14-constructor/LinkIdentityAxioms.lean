import Solidity.Backend.Executable.CreationLinkIdentityControls

/-- info: 'Solidity.Backend.Executable.CreationLinkIdentity.sites_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Executable.CreationLinkIdentity.sites_read

/-- info: 'Solidity.Backend.Executable.CreationLinkIdentity.runtime_address' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Executable.CreationLinkIdentity.runtime_address

/-- info: 'Solidity.Backend.Executable.CreationLinkIdentity.returned_address' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Executable.CreationLinkIdentity.returned_address

/-- info: 'Solidity.Backend.Executable.CreationLinkIdentity.same_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Executable.CreationLinkIdentity.same_returns

/-- info: 'Solidity.Backend.Executable.CreationLinkIdentity.Controls.wrong_link_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Executable.CreationLinkIdentity.Controls.wrong_link_return
