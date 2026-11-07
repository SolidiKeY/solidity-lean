import Solidity.Backend.Passes.CheckedAdditionSequenceSuccessControls

namespace Solidity.Backend.Passes.CheckedAdditionSequenceSuccess
/-- info: 'Solidity.Backend.Passes.CheckedAdditionSequenceSuccess.intrinsic_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms intrinsic_success
/-- info: 'Solidity.Backend.Passes.CheckedAdditionSequenceSuccess.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms success
/-- info: 'Solidity.Backend.Passes.CheckedAdditionSequenceSuccess.guard_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms guard_exact
/-- info: 'Solidity.Backend.Passes.CheckedAdditionSequenceSuccess.Controls.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.joint
/-- info: 'Solidity.Backend.Passes.CheckedAdditionSequenceSuccess.Controls.whole_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.whole_run
end Solidity.Backend.Passes.CheckedAdditionSequenceSuccess
