import Solidity.Backend.Passes.MemoryScopeControls
import Solidity.Backend.Passes.MemoryScopeAllocation

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.code

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.cost

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.input

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.output

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.source_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.source_success

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.source_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.source_error

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.target_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.target_error

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.shared

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.Controls.scoped_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.Controls.scoped_accepted

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.Controls.dropped_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.Controls.dropped_context

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.Controls.suffix_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.Controls.suffix_source

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.Controls.reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.Controls.reached

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.Controls.complete_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.Controls.complete_observations

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.Controls.wrong_joined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.Controls.wrong_joined

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.Controls.wrong_context_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.Controls.wrong_context_cell

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.Controls.old_private_word_not_cleared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.Controls.old_private_word_not_cleared

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.Controls.reached_source_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.Controls.reached_source_revert

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.Controls.reached_target_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.Controls.reached_target_revert

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.Allocation.source_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.Allocation.source_run

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.Allocation.body_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.Allocation.body_cost

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.Allocation.scope_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.Allocation.scope_cost

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.Allocation.initial_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.Allocation.initial_input

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.Allocation.shared_allocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.Allocation.shared_allocation

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.Allocation.scoped_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.Allocation.scoped_source

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.Allocation.positive_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.Allocation.positive_cost

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.Controls.joined_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.Controls.joined_source

/-- info: 'Solidity.Backend.Passes.MemoryScopeBoundary.Controls.completed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryScopeBoundary.Controls.completed

