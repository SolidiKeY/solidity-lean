import Solidity.Backend.Passes.MemoryJoinedOutputControls

namespace Solidity.Backend.Passes.MemoryJoinedOutput
/-- info: 'Solidity.Backend.Passes.MemoryJoinedOutput.compose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compose
/-- info: 'Solidity.Backend.Passes.MemoryJoinedOutput.public_compose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms public_compose
/-- info: 'Solidity.Backend.Passes.MemoryJoinedOutput.Controls.public_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.public_shared
/-- info: 'Solidity.Backend.Passes.MemoryJoinedOutput.Controls.public_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.public_failure
end Solidity.Backend.Passes.MemoryJoinedOutput
