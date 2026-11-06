import Solidity.Backend.Passes.MemoryJoinedAllocationControls

namespace Solidity.Backend.Passes.MemoryJoinedAllocation
/-- info: 'Solidity.Backend.Passes.MemoryJoinedAllocation.suffix_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms suffix_source
/-- info: 'Solidity.Backend.Passes.MemoryJoinedAllocation.joined_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joined_source
/-- info: 'Solidity.Backend.Passes.MemoryJoinedAllocation.execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms execution
/-- info: 'Solidity.Backend.Passes.MemoryJoinedAllocation.Controls.whole_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.whole_tail
/-- info: 'Solidity.Backend.Passes.MemoryJoinedAllocation.Controls.complete_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.complete_result
/-- info: 'Solidity.Backend.Passes.MemoryJoinedAllocation.Controls.stale_initial_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.stale_initial_map
end Solidity.Backend.Passes.MemoryJoinedAllocation
