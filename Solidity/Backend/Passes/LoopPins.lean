import Solidity.Backend.Passes.LoopPrefixControls
import Solidity.Backend.Passes.LoopAllocatingSuffix

/-! Exact observed standard-only guards for loop pass applications. -/
/-- info: 'Solidity.Backend.Passes.scope_cost_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.scope_cost_prefix
/-- info: 'Solidity.Backend.Passes.scope_cost_allocation_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.scope_cost_allocation_input
/-- info: 'Solidity.Backend.Passes.loops_memory_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.loops_memory_link
/-- info: 'Solidity.Backend.Passes.loops_budgeted_memory_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.loops_budgeted_memory_link
/-- info: 'Solidity.Backend.Passes.loops_success_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.loops_success_shared
/-- info: 'Solidity.Backend.Passes.loop_scopes_memory_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.loop_scopes_memory_link
/-- info: 'Solidity.Backend.Passes.loop_scopes_budgeted_memory_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.loop_scopes_budgeted_memory_link
/-- info: 'Solidity.Backend.Passes.loop_scopes_success_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.loop_scopes_success_shared
/-- info: 'Solidity.Backend.Passes.loop_scopes_triple_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.loop_scopes_triple_shared
/-- info: 'Solidity.Backend.Passes.LoopScopeControls.preparation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeControls.preparation
/-- info: 'Solidity.Backend.Passes.LoopScopeControls.prepared_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeControls.prepared_source
/-- info: 'Solidity.Backend.Passes.LoopScopeControls.conditionCompiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeControls.conditionCompiled
/-- info: 'Solidity.Backend.Passes.LoopScopeControls.bodyCompiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeControls.bodyCompiled
/-- info: 'Solidity.Backend.Passes.LoopScopeControls.body_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeControls.body_source
/-- info: 'Solidity.Backend.Passes.LoopScopeControls.body_stops' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeControls.body_stops
/-- info: 'Solidity.Backend.Passes.LoopScopeControls.loopCompiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeControls.loopCompiled
/-- info: 'Solidity.Backend.Passes.LoopScopeControls.enclosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeControls.enclosed
/-- info: 'Solidity.Backend.Passes.LoopScopeControls.checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeControls.checked
/-- info: 'Solidity.Backend.Passes.LoopScopeControls.condition_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeControls.condition_initial
/-- info: 'Solidity.Backend.Passes.LoopScopeControls.condition_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeControls.condition_final
/-- info: 'Solidity.Backend.Passes.LoopScopeControls.iteration_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeControls.iteration_source
/-- info: 'Solidity.Backend.Passes.LoopScopeControls.wrapped_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeControls.wrapped_source
/-- info: 'Solidity.Backend.Passes.LoopScopeControls.suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeControls.suffix
/-- info: 'Solidity.Backend.Passes.LoopScopeControls.final_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeControls.final_source
/-- info: 'Solidity.Backend.Passes.LoopScopeControls.costs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeControls.costs
/-- info: 'Solidity.Backend.Passes.LoopScopeControls.body_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeControls.body_cost
/-- info: 'Solidity.Backend.Passes.LoopScopeControls.public_recognizer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeControls.public_recognizer
/-- info: 'Solidity.Backend.Passes.LoopScopeControls.frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeControls.frames
/-- info: 'Solidity.Backend.Passes.LoopScopeControls.iteration_stmt_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeControls.iteration_stmt_source
/-- info: 'Solidity.Backend.Passes.LoopScopeControls.block_stmt_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeControls.block_stmt_source
/-- info: 'Solidity.Backend.Passes.LoopScopeControls.reached_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeControls.reached_prefix
/-- info: 'Solidity.Backend.Passes.LoopScopeControls.actual_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeControls.actual_cost
/-- info: 'Solidity.Backend.Passes.LoopScopeControls.legacy_metric_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeControls.legacy_metric_zero
/-- info: 'Solidity.Backend.Passes.LoopScopeApplication.budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeApplication.budget
/-- info: 'Solidity.Backend.Passes.LoopScopeApplication.preparation_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeApplication.preparation_input
/-- info: 'Solidity.Backend.Passes.LoopScopeApplication.room' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeApplication.room
/-- info: 'Solidity.Backend.Passes.LoopScopeApplication.into_scope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeApplication.into_scope
/-- info: 'Solidity.Backend.Passes.LoopScopeApplication.after_scope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeApplication.after_scope
/-- info: 'Solidity.Backend.Passes.LoopScopeApplication.joined_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeApplication.joined_source
/-- info: 'Solidity.Backend.Passes.LoopScopeApplication.shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeApplication.shared
/-- info: 'Solidity.Backend.Passes.LoopScopeApplication.suffix_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeApplication.suffix_cost
/-- info: 'Solidity.Backend.Passes.LoopScopeApplication.resources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeApplication.resources
/-- info: 'Solidity.Backend.Passes.LoopScopeObservations.before_source_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeObservations.before_source_vector
/-- info: 'Solidity.Backend.Passes.LoopScopeObservations.loop_source_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeObservations.loop_source_vector
/-- info: 'Solidity.Backend.Passes.LoopScopeObservations.final_source_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeObservations.final_source_vector
/-- info: 'Solidity.Backend.Passes.LoopScopeObservations.skipped_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeObservations.skipped_effect
/-- info: 'Solidity.Backend.Passes.LoopScopeObservations.wrong_cost_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeObservations.wrong_cost_refused
/-- info: 'Solidity.Backend.Passes.LoopScopeTrace.preparation_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeTrace.preparation_target
/-- info: 'Solidity.Backend.Passes.LoopScopeTrace.two_turns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeTrace.two_turns
/-- info: 'Solidity.Backend.Passes.LoopScopeTrace.terminal_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeTrace.terminal_ok
/-- info: 'Solidity.Backend.Passes.LoopScopeTrace.emitted_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeTrace.emitted_loop
/-- info: 'Solidity.Backend.Passes.LoopScopeTrace.loop_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeTrace.loop_target
/-- info: 'Solidity.Backend.Passes.LoopScopeTrace.suffix_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeTrace.suffix_target
/-- info: 'Solidity.Backend.Passes.LoopScopeTrace.whole_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeTrace.whole_target
/-- info: 'Solidity.Backend.Passes.LoopScopeTrace.final_stack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeTrace.final_stack
/-- info: 'Solidity.Backend.Passes.LoopScopeTrace.whole_target_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeTrace.whole_target_tail
/-- info: 'Solidity.Backend.Passes.LoopScopeTrace.preparation_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeTrace.preparation_vector
/-- info: 'Solidity.Backend.Passes.LoopScopeTrace.loop_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeTrace.loop_vector
/-- info: 'Solidity.Backend.Passes.LoopScopeTrace.final_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeTrace.final_vector
/-- info: 'Solidity.Backend.Passes.LoopScopeTrace.corrupt_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeTrace.corrupt_tail
/-- info: 'Solidity.Backend.Passes.LoopScopeTrace.actual_cursor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeTrace.actual_cursor
/-- info: 'Solidity.Backend.Passes.LoopScopeTrace.new_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeTrace.new_identity
/-- info: 'Solidity.Backend.Passes.LoopScopeTrace.selected_new_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeTrace.selected_new_base
/-- info: 'Solidity.Backend.Passes.LoopScopeTrace.stale_map_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeTrace.stale_map_refused
/-- info: 'Solidity.Backend.Passes.LoopScopeTerminal.prefix_relations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeTerminal.prefix_relations
/-- info: 'Solidity.Backend.Passes.LoopScopeTerminal.prefix_tails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeTerminal.prefix_tails
/-- info: 'Solidity.Backend.Passes.LoopScopeTerminal.reject_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeTerminal.reject_source
/-- info: 'Solidity.Backend.Passes.LoopScopeTerminal.reached_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeTerminal.reached_revert
/-- info: 'Solidity.Backend.Passes.LoopScopeTerminal.joined_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeTerminal.joined_revert
/-- info: 'Solidity.Backend.Passes.LoopScopeTerminal.direct_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeTerminal.direct_input
/-- info: 'Solidity.Backend.Passes.LoopScopeTerminal.direct_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopScopeTerminal.direct_shared
/-- info: 'Solidity.Backend.Passes.LoopPrefixControls.failureCompiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopPrefixControls.failureCompiled
/-- info: 'Solidity.Backend.Passes.LoopPrefixControls.body_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopPrefixControls.body_failure
/-- info: 'Solidity.Backend.Passes.LoopPrefixControls.failed_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopPrefixControls.failed_cost
/-- info: 'Solidity.Backend.Passes.LoopPrefixControls.loop_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopPrefixControls.loop_failure
/-- info: 'Solidity.Backend.Passes.LoopPrefixControls.scope_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopPrefixControls.scope_failure
/-- info: 'Solidity.Backend.Passes.LoopPrefixControls.failed_room' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopPrefixControls.failed_room
/-- info: 'Solidity.Backend.Passes.LoopPrefixControls.reached_body_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopPrefixControls.reached_body_failure
/-- info: 'Solidity.Backend.Passes.LoopPrefixControls.effectCompiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopPrefixControls.effectCompiled
/-- info: 'Solidity.Backend.Passes.LoopPrefixControls.effect_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopPrefixControls.effect_target
/-- info: 'Solidity.Backend.Passes.LoopPrefixControls.emitted_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopPrefixControls.emitted_failure
/-- info: 'Solidity.Backend.Passes.LoopPrefixControls.failing_body_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopPrefixControls.failing_body_target
/-- info: 'Solidity.Backend.Passes.LoopPrefixControls.condition_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopPrefixControls.condition_target
/-- info: 'Solidity.Backend.Passes.LoopPrefixControls.actual_failing_turn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopPrefixControls.actual_failing_turn
/-- info: 'Solidity.Backend.Passes.LoopPrefixControls.failing_prefix_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopPrefixControls.failing_prefix_vector
/-- info: 'Solidity.Backend.Passes.LoopPrefixControls.skipped_failure_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopPrefixControls.skipped_failure_effect
/-- info: 'Solidity.Backend.Passes.LoopPrefixControls.spinCompiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopPrefixControls.spinCompiled
/-- info: 'Solidity.Backend.Passes.LoopPrefixControls.spin_condition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopPrefixControls.spin_condition
/-- info: 'Solidity.Backend.Passes.LoopPrefixControls.spin_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopPrefixControls.spin_source
/-- info: 'Solidity.Backend.Passes.LoopPrefixControls.spin_scope_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopPrefixControls.spin_scope_source
/-- info: 'Solidity.Backend.Passes.LoopPrefixControls.reached_divergence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopPrefixControls.reached_divergence
/-- info: 'Solidity.Backend.Passes.LoopPrefixControls.distinct_failures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopPrefixControls.distinct_failures
/-- info: 'Solidity.Backend.Passes.LoopAllocatingSuffix.actual_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopAllocatingSuffix.actual_resources
/-- info: 'Solidity.Backend.Passes.LoopAllocatingSuffix.compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopAllocatingSuffix.compiled
/-- info: 'Solidity.Backend.Passes.LoopAllocatingSuffix.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopAllocatingSuffix.source
/-- info: 'Solidity.Backend.Passes.LoopAllocatingSuffix.cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopAllocatingSuffix.cost
/-- info: 'Solidity.Backend.Passes.LoopAllocatingSuffix.receiving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopAllocatingSuffix.receiving
/-- info: 'Solidity.Backend.Passes.LoopAllocatingSuffix.shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopAllocatingSuffix.shared
/-- info: 'Solidity.Backend.Passes.LoopAllocatingSuffix.target_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopAllocatingSuffix.target_run
/-- info: 'Solidity.Backend.Passes.LoopAllocatingSuffix.complete_target_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopAllocatingSuffix.complete_target_vector
/-- info: 'Solidity.Backend.Passes.LoopAllocatingSuffix.skipped_allocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopAllocatingSuffix.skipped_allocation
/-- info: 'Solidity.Backend.Passes.LoopAllocatingSuffix.complete_source_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.LoopAllocatingSuffix.complete_source_vector
