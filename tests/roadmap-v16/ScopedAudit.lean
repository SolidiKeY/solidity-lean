import Solidity.Roadmap.V16.FiniteHeapConsumer
import Solidity.Roadmap.V16.CompilerConsumer
import Solidity.Roadmap.V16.ConstructionCompilation
import Solidity.Roadmap.V16.ConstructionConsumer
import Solidity.Roadmap.V16.MemoryLoopConsumer
import Solidity.Roadmap.V16.MemoryCallConsumer
import Solidity.Roadmap.V16.CallbackControls
import Solidity.Roadmap.V16.LoopControls
import Solidity.Roadmap.V16.HashHistory
import Solidity.Roadmap.V16.SessionControls
import Solidity.Roadmap.V16.SpecificationControls

#print axioms Solidity.Roadmap.V16.Checks.combination_need
#print axioms Solidity.Roadmap.V16.Checks.combination_success
#print axioms Solidity.Roadmap.V16.Checks.loop_failure_bound
#print axioms Solidity.Roadmap.V16.Checks.loop_without_failure
#print axioms Solidity.Roadmap.V16.Checks.not_unconditional_loop_divergence
#print axioms Solidity.Roadmap.V16.Checks.revert_at_need
#print axioms Solidity.Roadmap.V16.Checks.revert_data_not_erased
#print axioms Solidity.Roadmap.V16.Checks.success_at_need
#print axioms Solidity.Roadmap.V16.Checks.success_not_revert
#print axioms Solidity.Roadmap.V16.SessionControls.allowed
#print axioms Solidity.Roadmap.V16.SessionControls.completes
#print axioms Solidity.Roadmap.V16.SessionControls.completes._proof_1_1
#print axioms Solidity.Roadmap.V16.SessionControls.composed_session_observation
#print axioms Solidity.Roadmap.V16.SessionControls.event_count
#print axioms Solidity.Roadmap.V16.SessionControls.event_count._proof_1_1
#print axioms Solidity.Roadmap.V16.SessionControls.execution._proof_1
#print axioms Solidity.Roadmap.V16.SessionControls.invalid_event_invariant
#print axioms Solidity.Roadmap.V16.SessionControls.no_credit
#print axioms Solidity.Roadmap.V16.SessionControls.no_credit._proof_1_1
#print axioms Solidity.Roadmap.V16.SessionControls.no_erasing_refinement
#print axioms Solidity.Roadmap.V16.SessionControls.no_wrong_event_refinement
#print axioms Solidity.Roadmap.V16.SpecificationControls.box_post_witness
#print axioms Solidity.Roadmap.V16.SpecificationControls.diamond_commit_witness
#print axioms Solidity.Roadmap.V16.SpecificationControls.diamond_success_witness
#print axioms Solidity.Roadmap.V16.SpecificationControls.exhausted_diamond
#print axioms Solidity.Roadmap.V16.SpecificationControls.exhausted_has_no_success
#print axioms Solidity.Roadmap.V16.SpecificationControls.exhausted_not_eligible
#print axioms Solidity.Roadmap.V16.SpecificationControls.invariant_transport_witness
#print axioms Solidity.Roadmap.V16.SpecificationControls.nilOut._proof_1
#print axioms Solidity.Roadmap.V16.TransactionControls.accepted
#print axioms Solidity.Roadmap.V16.TransactionControls.callTx._proof_1
#print axioms Solidity.Roadmap.V16.TransactionControls.commit_run
#print axioms Solidity.Roadmap.V16.TransactionControls.commit_step
#print axioms Solidity.Roadmap.V16.TransactionControls.deployTx._proof_1
#print axioms Solidity.Roadmap.V16.TransactionControls.deployTx._proof_2
#print axioms Solidity.Roadmap.V16.TransactionControls.deployed
#print axioms Solidity.Roadmap.V16.TransactionControls.event_trace
#print axioms Solidity.Roadmap.V16.TransactionControls.invalid_timestamp_invariant
#print axioms Solidity.Roadmap.V16.TransactionControls.no_failure_bound_inhabited
#print axioms Solidity.Roadmap.V16.TransactionControls.no_failure_composition
#print axioms Solidity.Roadmap.V16.TransactionControls.no_failure_divergence
#print axioms Solidity.Roadmap.V16.TransactionControls.rollback_run
#print axioms Solidity.Roadmap.V16.TransactionControls.rollback_step
#print axioms Solidity.Roadmap.V16.TransactionControls.transported_event_trace
#print axioms Solidity.Roadmap.V16.TransactionControls.wrong_event_order
#print axioms Solidity.Roadmap.V16.TransactionControls.wrong_revert_after_transport
#print axioms Solidity.Roadmap.V16.completed_stable
#print axioms Solidity.Roadmap.V16.completion_at_need
#print axioms Solidity.Roadmap.V16.composed_completion
#print axioms Solidity.Roadmap.V16.composed_need
#print axioms Solidity.Roadmap.V16.composed_observation
#print axioms Solidity.Roadmap.V16.composed_safety
#print axioms Solidity.Roadmap.V16.decoded_invariant
#print axioms Solidity.Roadmap.V16.diamond_commit
#print axioms Solidity.Roadmap.V16.event_at_need
#print axioms Solidity.Roadmap.V16.event_invariant
#print axioms Solidity.Roadmap.V16.reachable_invariant
#print axioms Solidity.Roadmap.V16.reachable_transport
#print axioms Solidity.Roadmap.V16.refinement_refl
#print axioms Solidity.Roadmap.V16.spec_box_post
#print axioms Solidity.Roadmap.V16.spec_diamond_success
#print axioms Solidity.Roadmap.V16.specification_invariant_transport
#print axioms Solidity.Roadmap.V16.trace_invariant
#print axioms Solidity.Roadmap.V16.trace_transport
#print axioms Solidity.Roadmap.V16.hash_history_tail
#print axioms Solidity.Roadmap.V16.hash_history_cross
#print axioms Solidity.Roadmap.V16.local_hash_premises_do_not_join

#print axioms Solidity.Roadmap.V16.loop_iteration_invariant
#print axioms Solidity.Roadmap.V16.loop_success_invariant
#print axioms Solidity.Roadmap.V16.forever_iteration
#print axioms Solidity.Roadmap.V16.forever_loop_fuel
#print axioms Solidity.Roadmap.V16.pending_is_not_divergence
#print axioms Solidity.Roadmap.V16.loop_revert_payload
#print axioms Solidity.Roadmap.V16.forever_loop_inhabited

#print axioms Solidity.Roadmap.V16.callback_post

#print axioms Solidity.Roadmap.V16.callback_valid_post

#print axioms Solidity.Roadmap.V16.callback_no_violation

#print axioms Solidity.Roadmap.V16.callback_frames_no_violation

#print axioms Solidity.Roadmap.V16.callback_halt

#print axioms Solidity.Roadmap.V16.CallbackControls.nil_callback_box

#print axioms Solidity.Roadmap.V16.CallbackControls.nil_callback_post

#print axioms Solidity.Roadmap.V16.CallbackControls.wrong_callback_post

#print axioms Solidity.Roadmap.V16.CallbackControls.broken_callback_execution

#print axioms Solidity.Roadmap.V16.CallbackControls.broken_callback_box

#print axioms Solidity.Roadmap.V16.CallbackControls.callback_resumes

#print axioms Solidity.Roadmap.V16.CallbackControls.resumption_changes_balance

#print axioms Solidity.Roadmap.V16.CallbackControls.resumed_post_if_modal

#print axioms Solidity.Roadmap.V16.memory_call_result

#print axioms Solidity.Roadmap.V16.memory_call_rep_iff

#print axioms Solidity.Roadmap.V16.memory_call_success

#print axioms Solidity.Roadmap.V16.memory_call_spec

#print axioms Solidity.Roadmap.V16.memory_call_failure

#print axioms Solidity.Roadmap.V16.memory_call_alias

#print axioms Solidity.Roadmap.V16.memory_call_small_frame

#print axioms Solidity.Roadmap.V16.memory_call_cursor

#print axioms Solidity.Roadmap.V16.memory_call_not_exhausted

#print axioms Solidity.Roadmap.V16.memory_call_capacity

#print axioms Solidity.Roadmap.V16.memory_call_diamond

#print axioms Solidity.Roadmap.V16.memory_call_diamond_iff

#print axioms Solidity.Roadmap.V16.memory_call_diamond_cursor

#print axioms Solidity.Roadmap.V16.memory_call_box

#print axioms Solidity.Roadmap.V16.memory_call_box_iff

#print axioms Solidity.Roadmap.V16.memory_call_box_diamond_dual

#print axioms Solidity.Roadmap.V16.loop_result

#print axioms Solidity.Roadmap.V16.loop_diamond

#print axioms Solidity.Roadmap.V16.loop_box

#print axioms Solidity.Roadmap.V16.loop_divergence

#print axioms Solidity.Roadmap.V16.scoped_loop_result

#print axioms Solidity.Roadmap.V16.scoped_loop_diamond

#print axioms Solidity.Roadmap.V16.scoped_loop_box

#print axioms Solidity.Roadmap.V16.scoped_loop_divergence

#print axioms Solidity.Roadmap.V16.loop_reconstruct

#print axioms Solidity.Roadmap.V16.loop_public_diamond

#print axioms Solidity.Roadmap.V16.scoped_loop_reconstruct

#print axioms Solidity.Roadmap.V16.scoped_loop_public_diamond
#print axioms Solidity.Roadmap.V16.construction_result
#print axioms Solidity.Roadmap.V16.construction_not_exhausted
#print axioms Solidity.Roadmap.V16.construction_diamond
#print axioms Solidity.Roadmap.V16.construction_diamond_iff
#print axioms Solidity.Roadmap.V16.construction_box
#print axioms Solidity.Roadmap.V16.construction_box_iff
#print axioms Solidity.Roadmap.V16.construction_capacity
#print axioms Solidity.Roadmap.V16.construction_diamond_cursor
#print axioms Solidity.Roadmap.V16.construction_box_diamond_dual
#print axioms Solidity.Roadmap.V16.construction_append_cert
#print axioms Solidity.Roadmap.V16.construction_reconstruct
#print axioms Solidity.Roadmap.V16.construction_public_cert
#print axioms Solidity.Roadmap.V16.constructionAppendCompiled
#print axioms Solidity.Roadmap.V16.constructionCompose
#print axioms Solidity.Roadmap.V16.construction_compile_inversion
#print axioms Solidity.Roadmap.V16.construction_compile_append
#print axioms Solidity.Roadmap.V16.construction_compile_append_link
#print axioms Solidity.Roadmap.V16.construction_certificate_code
#print axioms Solidity.Roadmap.V16.construction_certificate_fragment
#print axioms Solidity.Roadmap.V16.construction_public_append_code
#print axioms Solidity.Roadmap.V16.finite_heap_result
#print axioms Solidity.Roadmap.V16.finite_heap_not_exhausted
#print axioms Solidity.Roadmap.V16.finite_heap_diamond
#print axioms Solidity.Roadmap.V16.finite_heap_box
#print axioms Solidity.Roadmap.V16.compiler_not_exhausted
#print axioms Solidity.Roadmap.V16.compiler_diamond
#print axioms Solidity.Roadmap.V16.compiler_box_target
#print axioms Solidity.Roadmap.V16.finite_heap_failure
#print axioms Solidity.Roadmap.V16.finite_heap_diamond_iff
#print axioms Solidity.Roadmap.V16.finite_heap_box_iff
#print axioms Solidity.Roadmap.V16.finite_memory_cost
#print axioms Solidity.Roadmap.V16.finite_memory_rep_iff
#print axioms Solidity.Roadmap.V16.compiler_nonpaying_diamond
#print axioms Solidity.Roadmap.V16.compiler_source_error
