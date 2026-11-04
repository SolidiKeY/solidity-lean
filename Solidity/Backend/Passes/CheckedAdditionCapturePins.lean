import Solidity.Backend.Passes.CheckedAdditionCaptureControls

namespace Solidity.Backend.Passes.CheckedAdditionCapture
/-- info: 'Solidity.Backend.Passes.CheckedAdditionCapture.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms success
/-- info: 'Solidity.Backend.Passes.CheckedAdditionCapture.overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms overflow
/-- info: 'Solidity.Backend.Passes.CheckedAdditionCapture.Controls.capture_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.capture_run
/-- info: 'Solidity.Backend.Passes.CheckedAdditionCapture.Controls.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.joint
/-- info: 'Solidity.Backend.Passes.CheckedAdditionCapture.Controls.jointOverflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.jointOverflow
end Solidity.Backend.Passes.CheckedAdditionCapture
