import Solidity.Backend.Passes.AxiomPins
import Solidity.Backend.Passes.ContinuationPins
import Solidity.Backend.Passes.FixedBooleanPins
import Solidity.Backend.Passes.FreshBooleanPins
import Solidity.Backend.Passes.LoopPins
import Solidity.Backend.Passes.MemoryCallPins
import Solidity.Backend.Passes.RevertPins
import Solidity.Backend.Passes.TriplePins
import Solidity.Backend.Passes.ValueContextPins
import Solidity.Backend.Passes.ReframedTriplePins
import Solidity.Backend.Passes.LoopReframedFailureControls
import Solidity.Backend.Passes.LoopReframedCompletion

/-! Standard-axiom pins for the recovered compiler-transport proof components. -/

/-- info: 'Solidity.Backend.Passes.LoopReframedFailureControls.before_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.LoopReframedFailureControls.before_source

/-- info: 'Solidity.Backend.Passes.LoopReframedFailureControls.after_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.LoopReframedFailureControls.after_source

/-- info: 'Solidity.Backend.Passes.LoopReframedFailureControls.after_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.LoopReframedFailureControls.after_link

/-- info: 'Solidity.Backend.Passes.LoopReframedFailureControls.reached_prefix_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.LoopReframedFailureControls.reached_prefix_failure

/-- info: 'Solidity.Backend.Passes.LoopReframedFailureControls.joined_source_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.LoopReframedFailureControls.joined_source_failure

/-- info: 'Solidity.Backend.Passes.LoopReframedFailureControls.before_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.LoopReframedFailureControls.before_target

/-- info: 'Solidity.Backend.Passes.LoopReframedFailureControls.before_target_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.LoopReframedFailureControls.before_target_tail

/-- info: 'Solidity.Backend.Passes.LoopReframedFailureControls.wrong_order_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.LoopReframedFailureControls.wrong_order_target

/-- info: 'Solidity.Backend.Passes.LoopReframedFailureControls.wrong_order_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.LoopReframedFailureControls.wrong_order_source

/-- info: 'Solidity.Backend.Passes.LoopReframedFailureControls.wrong_order_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.LoopReframedFailureControls.wrong_order_distinct

/-- info: 'Solidity.Backend.Passes.LoopReframedFailureControls.complete_wrong_order_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.LoopReframedFailureControls.complete_wrong_order_vector

/-- info: 'Solidity.Backend.Passes.LoopReframedFailureControls.corrupt_saved_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.LoopReframedFailureControls.corrupt_saved_tail

/-- info: 'Solidity.Backend.Passes.LoopReframedFailureControls.insufficient_guard_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.LoopReframedFailureControls.insufficient_guard_frame

/-- info: 'Solidity.Backend.Passes.LoopReframedFailureControls.stale_guard_input_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.LoopReframedFailureControls.stale_guard_input_refused

/-- info: 'Solidity.Backend.Passes.LoopReframedFailureControls.ordinary_revert_separate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.LoopReframedFailureControls.ordinary_revert_separate

/-- info: 'Solidity.Backend.Passes.compilation_reframed_revert_witness_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.compilation_reframed_revert_witness_iff

/-- info: 'Solidity.Backend.Passes.compilation_reframed_reached_revert_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.compilation_reframed_reached_revert_shared

/-- info: 'Solidity.Backend.Passes.compilation_reframed_reached_fault_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.compilation_reframed_reached_fault_shared

/-- info: 'Solidity.Backend.Passes.LoopReframedCompletion.canonical_completion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.LoopReframedCompletion.canonical_completion

/-- info: 'Solidity.Backend.Passes.LoopReframedCompletion.shared_completion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.LoopReframedCompletion.shared_completion

/-- info: 'Solidity.Backend.Passes.LoopReframedCompletion.old_references_and_zero_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.LoopReframedCompletion.old_references_and_zero_cost

/-- info: 'Solidity.Backend.Passes.LoopReframedCompletion.final_new_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.LoopReframedCompletion.final_new_identity

/-- info: 'Solidity.Backend.Passes.LoopReframedCompletion.selected_final_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.LoopReframedCompletion.selected_final_base

/-- info: 'Solidity.Backend.Passes.LoopReframedCompletion.stale_final_map_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.LoopReframedCompletion.stale_final_map_refused

/-- info: 'Solidity.Backend.Passes.LoopReframedCompletion.insufficient_consumer_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.LoopReframedCompletion.insufficient_consumer_frame

/-- info: 'Solidity.Backend.Passes.LoopReframedCompletion.complete_final_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.LoopReframedCompletion.complete_final_vector

/-- info: 'Solidity.Backend.Passes.LoopReframedCompletion.corrupt_saved_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.LoopReframedCompletion.corrupt_saved_tail
