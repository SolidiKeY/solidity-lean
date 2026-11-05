import Solidity.Backend.Passes.MemoryJoinFrameControls

namespace Solidity.Backend.Passes.MemoryJoinFrame
/-- info: 'Solidity.Backend.Passes.MemoryJoinFrame.frame_join' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms frame_join
/-- info: 'Solidity.Backend.Passes.MemoryJoinFrame.input_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms input_iff
/-- info: 'Solidity.Backend.Passes.MemoryJoinFrame.left_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms left_input
/-- info: 'Solidity.Backend.Passes.MemoryJoinFrame.boundary_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boundary_link
/-- info: 'Solidity.Backend.Passes.MemoryJoinFrame.public_admission' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms public_admission
/-- info: 'Solidity.Backend.Passes.MemoryJoinFrame.Controls.admitted_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.admitted_execution
/-- info: 'Solidity.Backend.Passes.MemoryJoinFrame.Controls.scoped_slot_reuse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.scoped_slot_reuse
/-- info: 'Solidity.Backend.Passes.MemoryJoinFrame.Controls.unreachable_frame_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.unreachable_frame_refused
/-- info: 'Solidity.Backend.Passes.MemoryJoinFrame.Controls.unreachable_other_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.unreachable_other_fields
end Solidity.Backend.Passes.MemoryJoinFrame
