"""Portable source inventory for the held 225-row checkpoint.

These registrations are source-accounting inputs, not kernel proof evidence.
The external acceptance command separately checks the original ledger/proofs.

Authorized live statement transitions are recorded separately in
the private H145 evidence archive cited in
docs/feature-work/h62-2-audit-v09-passes.md (authorized-statement-transitions.json).
Do not relabel this frozen historical signed_refusal as signed_acceptance or
transfer its proof credit before explicit replacement-statement validation.
"""

FAMILIES = [
    ('Solidity/Backend/Passes/AllocatingControls.lean', 'Solidity.Backend.Passes.AllocatingControls', 'actual_link actual_result allocating_composition initial_repr more_link more_source populated_allocation populated_allocation_cursor prefix_input reached_cost reached_failure stale_map_impossible target_bootstrap'),
    ('Solidity/Backend/Passes/BitwiseValueContextControls.lean', 'Solidity.Backend.Passes.BitwiseValueContextControls', 'and_vector corrupted_tail dirty_refusal inhabited or_vector represented signed_refusal source_result wrong_value xor_vector'),
    ('Solidity/Backend/Passes/CaptureControls.lean', 'Solidity.Backend.Passes.CaptureControls', 'actual_capture_code after_effect_read alias_source bad_after failure_all_tails fresh_reaches generic_alias_context generic_capture generic_value_context input ordered_values shared_output source_aliases source_capture source_failure_after_effect source_success stack_corruption target_effect_before_failure value_source wrong_order wrong_recapture'),
    ('Solidity/Backend/Passes/CapturedValueStability.lean', 'Solidity.Backend.Passes.CapturedValueStability', 'captured_source edit_failure execution failure_iff_source immediate_failure input source value_shared'),
    ('Solidity/Backend/Passes/ClosedValueControls.lean', 'Solidity.Backend.Passes.ClosedValueControls', 'bool_bytes boolean_application capacity_negative corrupted_tail noncanonical_bool ordered_memory signed_application signed_bytes signed_reference_prefix'),
    ('Solidity/Backend/Passes/Controls.lean', 'Solidity.Backend.Passes.Controls', 'accepted_stages assertion_run compiler_not_empty fragment_cherry_picking memory_input mixed_success_tail nonempty_acceptance result_five sequencing_associative source_prefix_identity source_success stack_corruption staged_not_always_revert whole_program_refused wrong_order'),
    ('Solidity/Backend/Passes/ExpressionControls.lean', 'Solidity.Backend.Passes.ExpressionControls', 'captured_pair_certificate captured_pair_values conditional_seven disjunction_tail eager_order_reverts selected_failure short_circuit_tail'),
    ('Solidity/Backend/Passes/HeapBoundary.lean', 'Solidity.Backend.Passes', 'construction_budgeted_link construction_memory_link construction_objects_link construction_referenceArrays_link objects_memory_link objects_objects_link objects_referenceArrays_link referenceArrays_memory_link'),
    ('Solidity/Backend/Passes/LinkedControls.lean', 'Solidity.Backend.Passes.LinkedControls', 'assertion_source base_ge_sixteen concrete_link frame_seventeen_impossible frame_six fresh_value left_stage_failure linked_success right_stage_reverts right_stage_source_revert'),
    ('Solidity/Backend/Passes/MemoryCompilerSequence.lean', 'Solidity.Backend.Passes', 'memory_compile_join memory_compile_single_block'),
    ('Solidity/Backend/Passes/MemoryScopeControls.lean', 'Solidity.Backend.Passes.MemoryScopeBoundary.Controls', 'complete_observations completed dropped_context failing_code joined_source old_private_word_not_cleared prefix_source reached reached_source_revert reached_target_revert scope_run scoped_accepted scoped_source suffix_run suffix_source wrong_context_cell wrong_joined wrong_run'),
    ('Solidity/Backend/Passes/ReachabilityControls.lean', 'Solidity.Backend.Passes.ReachabilityControls', 'aliasA_run allocateA_run allocateB_run bottomB_run concrete_tail_independence fresh_state_reaches_fixture middleA_run reachable_nontrivial read_run writeA0_run writeA1_run writeB0_run write_run zeroValue_run'),
    ('Solidity/Backend/Passes/ReferenceControls.lean', 'Solidity.Backend.Passes.ReferenceControls', 'both_source_branches both_target_branches certificate input_repr reachable wrong_order'),
    ('Solidity/Backend/Passes/ReindexedMemory.lean', 'Solidity.Backend.Passes', 'memory_reindex_code memory_reindex_compile memory_reindex_cost memory_reindex_frag memory_reindex_input_iff memory_reindex_mapped_iff'),
    ('Solidity/Backend/Passes/SharedPair.lean', 'Solidity.Backend.Passes', 'compilation_pair_shared'),
    ('Solidity/Backend/Passes/StatefulValueControls.lean', 'Solidity.Backend.Passes.StatefulValueControls', 'actual_bytes cast_application checked_binary_success comparison_application comparison_source empty_cast_component negated_source negation_application not_closed operand_words ordered_memory signed_source wrapping_after_capture wrapping_application wrapping_source'),
    ('Solidity/Backend/Passes/StatefulValues.lean', 'Solidity.Backend.Passes.StatefulValues', 'binary binary_revert_iff binary_source left_revert operands right_revert short_taken unary unary_source'),
    ('Solidity/Backend/Passes/TripleControls.lean', 'Solidity.Backend.Passes.TripleControls', 'capture_source cell0 cell1 cell17 cell2 cell20 cell3 cell4 cell5 cell6 corruption first_link fresh_source initial_repr7 observe_source ordered_results prefix_input7 second_link shared_resources stale_map'),
    ('Solidity/Backend/Passes/ValueCertificate.lean', 'Solidity.Backend.Passes', 'value_revert_iff value_success_tail'),
    ('Solidity/Backend/Passes/ValueContextControls.lean', 'Solidity.Backend.Passes.ValueContextControls', 'core_refusal_preserved declaration_failures ordered_reference_memory ordered_scalar_memory preserved_failures recognizers_same_code reference_decl_prefix reference_run reference_source scalar_decl_prefix scalar_run scalar_source source_failures source_wrong_index target_wrong_index'),
    ('Solidity/Backend/Passes/ValueSequence.lean', 'Solidity.Backend.Passes', 'value_pair_reached_revert value_pair_revert_iff value_pair_success_tail'),
    ('Solidity/Backend/Passes/ValueSequenceControls.lean', 'Solidity.Backend.Passes.ValueSequenceControls', 'after_allocation consumer_order corruption emitted_prefix first_source heterogeneous immediate_failure literal_word ordered_tail second_source source_order unchanged_memory wrong_order'),
]

def source_inventory_keys():
    keys = [(path, prefix+'.'+name) for path,prefix,names in FAMILIES for name in names.split()]
    if len(keys) != len(set(keys)) or len(keys) != 225:
        raise ValueError("Held source inventory must have 225 distinct registrations")
    return set(keys)
