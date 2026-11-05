import Solidity.Backend.Passes.MemoryJoinCostControls

namespace Solidity.Backend.Passes.MemoryJoinCost
/-- info: 'Solidity.Backend.Passes.MemoryJoinCost.cost_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cost_join
/-- info: 'Solidity.Backend.Passes.MemoryJoinCost.successful_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms successful_prefix
/-- info: 'Solidity.Backend.Passes.MemoryJoinCost.failed_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms failed_prefix
/-- info: 'Solidity.Backend.Passes.MemoryJoinCost.public_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms public_join
/-- info: 'Solidity.Backend.Passes.MemoryJoinCost.suffix_allocation_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms suffix_allocation_input
/-- info: 'Solidity.Backend.Passes.MemoryJoinCost.Controls.reached_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.reached_budget
/-- info: 'Solidity.Backend.Passes.MemoryJoinCost.Controls.failed_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.failed_public
end Solidity.Backend.Passes.MemoryJoinCost
