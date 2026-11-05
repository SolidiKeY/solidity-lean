import Solidity.Backend.Passes.CheckedAdditionReachedOverflowControls

namespace Solidity.Backend.Passes.CheckedAdditionReachedOverflow
/-- info: 'Solidity.Backend.Passes.CheckedAdditionReachedOverflow.reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reached
/-- info: 'Solidity.Backend.Passes.CheckedAdditionReachedOverflow.Controls.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.joint
/-- info: 'Solidity.Backend.Passes.CheckedAdditionReachedOverflow.Controls.prefix_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.prefix_run
/-- info: 'Solidity.Backend.Passes.CheckedAdditionReachedOverflow.Controls.physical_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.physical_terminal
/-- info: 'Solidity.Backend.Passes.CheckedAdditionReachedOverflow.Controls.wrong_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.wrong_order
end Solidity.Backend.Passes.CheckedAdditionReachedOverflow
