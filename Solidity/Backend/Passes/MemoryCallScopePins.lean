import Solidity.Backend.Passes.MemoryCallScopeObservations
import Solidity.Backend.Passes.MemoryCallScopeFailures

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.frag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.frag

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.code

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.need' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.need

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.cost

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.scope_free' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.scope_free

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.input

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.input_back' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.input_back

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.input_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.input_iff

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.output

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.shared

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls.scope_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls.scope_source

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls.suffix_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls.suffix_source

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls.joined_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls.joined_source

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls.shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls.shared

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls.reached_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls.reached_cost

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls.suffix_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls.suffix_cost

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls.costs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls.costs

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls.private_frame_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls.private_frame_refused

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.Observations.scope_source_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.Observations.scope_source_vector

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.Observations.final_source_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.Observations.final_source_vector

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.Observations.scoped_target_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.Observations.scoped_target_vector

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.Observations.final_target_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.Observations.final_target_vector

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.Observations.wrong_context_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.Observations.wrong_context_vector

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.Observations.wrong_context_differs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.Observations.wrong_context_differs

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.Observations.skipped_suffix_differs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.Observations.skipped_suffix_differs

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.Observations.corrupted_tail_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.Observations.corrupted_tail_refused

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.Observations.saved_tail_not_erased' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.Observations.saved_tail_not_erased

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.Failures.reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.Failures.reached

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.Failures.argument_case' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.Failures.argument_case

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.Failures.body_case' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.Failures.body_case

/-- info: 'Solidity.Backend.Passes.MemoryCallScopeBoundary.Failures.distinct_costs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.MemoryCallScopeBoundary.Failures.distinct_costs

