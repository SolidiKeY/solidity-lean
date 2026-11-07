#!/usr/bin/env python3
"""Mandatory external-evidence acceptance; missing artifacts are errors.

Run selected_heap_artifacts.py --acceptance after staging the manifest artifacts.
These original detailed assertions are deliberately not portable source tests.

Authorized live statement transitions are recorded separately in
tests/h62/item2/audit-v09-passes/authorized-statement-transitions.json.
Do not relabel this frozen historical signed_refusal as signed_acceptance or
transfer its proof credit before explicit replacement-statement validation.
"""
from pathlib import Path
import sys
import unittest
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT/'scripts/h62/item2/audit-v09-passes'))
import signature_boundaries as sb
from selected_heap_artifacts import artifact
from selected_heap_inventory import source_inventory_keys

class ExternalSelectedHeapAccounting(unittest.TestCase):
    def test_selected_heap_witness_has_actual_selected_membership(self):
        import json
        report = sb.frozen_report(ROOT)
        selected = {(r['path'],r['name']):r for r in report['rows']}
        mapping = json.loads(artifact('selected-heap-witness-map.json')[1].decode())
        keys = set()
        for row in mapping['covered_premise_bundles']:
            key = (row['path'],row['name'])
            self.assertIn(key,selected)
            self.assertNotIn(key,keys)
            keys.add(key)
            self.assertTrue(row['original_census_membership'])
            self.assertEqual(row['signature_sha256'],selected[key]['legacy_signature_sha256'])
        self.assertEqual(keys,{('Solidity/Backend/Passes/HeapBoundary.lean','Solidity.Backend.Passes.'+short) for short in ['objects_memory_link','referenceArrays_memory_link','construction_memory_link','objects_referenceArrays_link','objects_objects_link','construction_referenceArrays_link','construction_objects_link','construction_budgeted_link']} | {('Solidity/Backend/Passes/ReindexedMemory.lean','Solidity.Backend.Passes.memory_reindex_'+short) for short in ['code','frag','cost','input_iff','mapped_iff','compile']} | {('Solidity/Backend/Passes/MemoryCompilerSequence.lean','Solidity.Backend.Passes.memory_compile_'+short) for short in ['join','single_block']} | {('Solidity/Backend/Passes/ValueCertificate.lean','Solidity.Backend.Passes.'+short) for short in ['value_success_tail','value_revert_iff']} | {('Solidity/Backend/Passes/ValueSequence.lean','Solidity.Backend.Passes.'+short) for short in ['value_pair_success_tail','value_pair_revert_iff','value_pair_reached_revert']} | {('Solidity/Backend/Passes/SharedPair.lean','Solidity.Backend.Passes.compilation_pair_shared')} | {('Solidity/Backend/Passes/StatefulValues.lean','Solidity.Backend.Passes.StatefulValues.'+short) for short in ['binary_source','unary_source','operands','binary','unary','binary_revert_iff','left_revert','right_revert','short_taken']} | {('Solidity/Backend/Passes/ValueSequenceControls.lean','Solidity.Backend.Passes.ValueSequenceControls.'+short) for short in ['first_source','second_source','literal_word','ordered_tail','emitted_prefix','source_order','consumer_order','wrong_order','corruption','heterogeneous','immediate_failure','unchanged_memory','after_allocation']} | {('Solidity/Backend/Passes/CapturedValueStability.lean','Solidity.Backend.Passes.CapturedValueStability.'+short) for short in ['value_shared','source','input','execution','captured_source','edit_failure','immediate_failure','failure_iff_source']} | {('Solidity/Backend/Passes/ValueContextControls.lean','Solidity.Backend.Passes.ValueContextControls.'+short) for short in ['scalar_source', 'reference_source', 'scalar_run', 'reference_run', 'scalar_decl_prefix', 'reference_decl_prefix', 'preserved_failures', 'source_wrong_index', 'target_wrong_index', 'core_refusal_preserved', 'ordered_scalar_memory', 'ordered_reference_memory', 'declaration_failures', 'source_failures', 'recognizers_same_code']} | {('Solidity/Backend/Passes/BitwiseValueContextControls.lean','Solidity.Backend.Passes.BitwiseValueContextControls.'+short) for short in ['represented', 'inhabited', 'and_vector', 'or_vector', 'xor_vector', 'wrong_value', 'corrupted_tail', 'dirty_refusal', 'signed_refusal', 'source_result']} | {('Solidity/Backend/Passes/StatefulValueControls.lean','Solidity.Backend.Passes.StatefulValueControls.'+short) for short in ['wrapping_source', 'comparison_source', 'signed_source', 'negated_source', 'operand_words', 'wrapping_application', 'comparison_application', 'cast_application', 'negation_application', 'actual_bytes', 'empty_cast_component', 'ordered_memory', 'wrapping_after_capture', 'not_closed', 'checked_binary_success']} | {('Solidity/Backend/Passes/ClosedValueControls.lean','Solidity.Backend.Passes.ClosedValueControls.'+short) for short in ['signed_application', 'boolean_application', 'signed_reference_prefix', 'ordered_memory', 'signed_bytes', 'bool_bytes', 'noncanonical_bool', 'capacity_negative', 'corrupted_tail']} | {('Solidity/Backend/Passes/CaptureControls.lean','Solidity.Backend.Passes.CaptureControls.'+short) for short in ['actual_capture_code', 'source_capture', 'alias_source', 'value_source', 'source_success', 'fresh_reaches', 'input', 'generic_capture', 'generic_alias_context', 'source_aliases', 'shared_output', 'ordered_values', 'generic_value_context', 'after_effect_read', 'wrong_recapture', 'wrong_order', 'bad_after', 'source_failure_after_effect', 'target_effect_before_failure', 'failure_all_tails', 'stack_corruption']} | {('Solidity/Backend/Passes/AllocatingControls.lean','Solidity.Backend.Passes.AllocatingControls.'+short) for short in ['initial_repr', 'reached_cost', 'prefix_input', 'actual_link', 'allocating_composition', 'stale_map_impossible', 'target_bootstrap', 'actual_result', 'reached_failure', 'more_source', 'more_link', 'populated_allocation', 'populated_allocation_cursor']} | {('Solidity/Backend/Passes/TripleControls.lean','Solidity.Backend.Passes.TripleControls.'+short) for short in ['initial_repr7', 'prefix_input7', 'capture_source', 'observe_source', 'first_link', 'second_link', 'fresh_source', 'shared_resources', 'cell4', 'cell5', 'cell6', 'cell17', 'cell2', 'cell3', 'cell1', 'cell20', 'cell0', 'ordered_results', 'stale_map', 'corruption']} | {('Solidity/Backend/Passes/ReachabilityControls.lean','Solidity.Backend.Passes.ReachabilityControls.'+short) for short in ['allocateA_run', 'writeA0_run', 'writeA1_run', 'allocateB_run', 'writeB0_run', 'aliasA_run', 'bottomB_run', 'middleA_run', 'zeroValue_run', 'fresh_state_reaches_fixture', 'write_run', 'read_run', 'concrete_tail_independence', 'reachable_nontrivial']} | {('Solidity/Backend/Passes/ExpressionControls.lean','Solidity.Backend.Passes.ExpressionControls.'+short) for short in ['short_circuit_tail', 'disjunction_tail', 'selected_failure', 'eager_order_reverts', 'conditional_seven', 'captured_pair_values', 'captured_pair_certificate']} | {('Solidity/Backend/Passes/LinkedControls.lean','Solidity.Backend.Passes.LinkedControls.'+short) for short in ['assertion_source', 'concrete_link', 'linked_success', 'base_ge_sixteen', 'frame_six', 'fresh_value', 'frame_seventeen_impossible', 'right_stage_reverts', 'left_stage_failure', 'right_stage_source_revert']} | {('Solidity/Backend/Passes/Controls.lean','Solidity.Backend.Passes.Controls.'+short) for short in ['whole_program_refused', 'assertion_run', 'source_prefix_identity', 'source_success', 'memory_input', 'mixed_success_tail', 'result_five', 'staged_not_always_revert', 'wrong_order', 'stack_corruption', 'fragment_cherry_picking', 'nonempty_acceptance', 'sequencing_associative', 'accepted_stages', 'compiler_not_empty']} | {('Solidity/Backend/Passes/ReferenceControls.lean','Solidity.Backend.Passes.ReferenceControls.'+short) for short in ['input_repr', 'certificate', 'both_source_branches', 'both_target_branches', 'wrong_order', 'reachable']} | {('Solidity/Backend/Passes/MemoryScopeControls.lean','Solidity.Backend.Passes.MemoryScopeBoundary.Controls.'+short) for short in ['prefix_source', 'scoped_source', 'dropped_context', 'scoped_accepted', 'suffix_source', 'suffix_run', 'reached', 'joined_source', 'completed', 'complete_observations', 'wrong_run', 'scope_run', 'wrong_joined', 'wrong_context_cell', 'old_private_word_not_cleared', 'reached_source_revert', 'failing_code', 'reached_target_revert']})
        self.assertEqual(mapping['original_census_accounting']['covered_selected_rows_by_this_map'],len(keys))
        self.assertEqual(mapping['original_census_accounting']['remaining_selected_rows'],1259-len(keys))


    def test_closed_application_does_not_inflate_selected_coverage(self):
        import json
        mapping = json.loads(artifact('selected-heap-witness-map.json')[1].decode())
        selected = {(r['path'],r['name']) for r in sb.frozen_report(ROOT)['rows']}
        group = mapping['unselected_closed_application']
        self.assertEqual(group['covered_selected_rows'],0)
        self.assertEqual(group['prior_supplemental_rows'],19)
        self.assertEqual(len(group['rows']),4)
        self.assertEqual({r['name'].split('.')[-1] for r in group['rows']},
                         {'represented_word','application','prefix_capacity','bytes'})
        for row in group['rows']:
            self.assertNotIn((row['path'],row['name']),selected)
            self.assertFalse(row['original_census_membership'])
        self.assertEqual(mapping['original_census_accounting']['covered_selected_rows_by_this_map'],225)
        self.assertEqual(mapping['original_census_accounting']['remaining_selected_rows'],1034)


    def test_value_sequence_frontier_preserves_every_uncovered_selected_row(self):
        import json
        mapping = json.loads(artifact('selected-heap-witness-map.json')[1].decode())
        group = mapping['uncovered_value_sequence_controls']
        selected = {(r['path'],r['name']):r for r in sb.frozen_report(ROOT)['rows']}
        expected = {k for k in selected if k[0] == group['path']}
        actual = {(r['path'],r['name']) for r in group['rows']}
        self.assertEqual(actual,expected)
        self.assertEqual(len(group['rows']),13)
        self.assertEqual(len(actual),13)
        self.assertEqual(group['covered_selected_rows'],13)
        self.assertEqual(group['remaining_selected_rows'],0)
        self.assertEqual((group['explicit_tail_rows'],group['private_range_repr_rows'],
                          group['no_explicit_source_binder_rows']),(4,1,8))
        for row in group['rows']:
            self.assertEqual(row['signature_sha256'],selected[(row['path'],row['name'])]['legacy_signature_sha256'])
            if row['visibility'] == 'private':
                self.assertEqual(row['witness_status'],'kernel_checked_original_private_identity_and_joint_instance')
                self.assertTrue(row['simultaneous_witness'].endswith('PopulatedSequence.private_word_joint'))
                self.assertEqual(row['kernel_identity'],'_private.Solidity.Backend.Passes.ValueSequenceControls.0.Solidity.Backend.Passes.ValueSequenceControls.literal_word')
                self.assertEqual(row['kernel_identity_components'][5],0)
                self.assertIsInstance(row['kernel_identity_components'][5],int)
            else:
                self.assertEqual(row['witness_status'],'kernel_checked_reuse_of_original_selected_concrete_control')
                self.assertTrue(row['simultaneous_witness'].endswith('PopulatedSequence.joint_premises'))


    def test_bitwise_source_result_uses_its_own_source_tuple(self):
        import json
        mapping = json.loads(artifact('selected-heap-witness-map.json')[1].decode())
        self.assertEqual(mapping['pending_bitwise_source_result'],[])
        rows = [r for r in mapping['covered_premise_bundles']
                if r['name'] == 'Solidity.Backend.Passes.BitwiseValueContextControls.source_result']
        self.assertEqual(len(rows),1)
        row = rows[0]
        self.assertEqual(row['witness_status'],'kernel_checked_concrete_selected_source_tuple_instance')
        self.assertTrue(row['simultaneous_witness'].endswith('BitwiseSource.joint'))
        self.assertTrue(row['exercised_witness'].endswith('BitwiseSource.source_result'))
        self.assertEqual(set(row['witness_arguments']),{'E','G','F','s','n','op','limits'})
        selected = {(r['path'],r['name']):r for r in sb.frozen_report(ROOT)['rows']}
        self.assertEqual(row['signature_sha256'],selected[(row['path'],row['name'])]['legacy_signature_sha256'])
        self.assertEqual((mapping['bitwise_source_tuple']['timeout_fuel'],
                          mapping['bitwise_source_tuple']['success_fuel']),(2,3))


    def test_stateful_refutation_is_not_a_closed_certificate_premise(self):
        import json
        mapping = json.loads(artifact('selected-heap-witness-map.json')[1].decode())
        rows = [r for r in mapping['covered_premise_bundles']
                if r['name'] == 'Solidity.Backend.Passes.StatefulValueControls.not_closed']
        self.assertEqual(len(rows),1)
        row = rows[0]
        self.assertEqual(row['contract_kind'],'intentional_negative_no_closed_certificate')
        self.assertIn('¬ Nonempty (Backend.Scalar.ClosedCertificate wrapping)',row['signature'])
        self.assertTrue(row['simultaneous_witness'].endswith('StatefulApplications.joint'))
        self.assertTrue(row['exercised_witness'].endswith('StatefulApplications.not_closed'))


    def test_capture_private_source_steps_keep_original_numeric_identities(self):
        import json
        mapping = json.loads(artifact('selected-heap-witness-map.json')[1].decode())
        rows = [r for r in mapping['covered_premise_bundles']
                if r['path'] == 'Solidity/Backend/Passes/CaptureControls.lean' and r['visibility'] == 'private']
        self.assertEqual({r['name'].split('.')[-1] for r in rows},{'alias_source','value_source','bad_after'})
        for row in rows:
            self.assertEqual(row['witness_status'],'kernel_checked_original_private_identity_and_joint_instance')
            self.assertEqual(row['kernel_identity'],'_private.Solidity.Backend.Passes.CaptureControls.0.'+row['name'])
            self.assertIsInstance(row['kernel_identity_components'][5],int)
            self.assertEqual(row['kernel_identity_components'][5],0)


    def test_triple_private_cell_checks_do_not_count_observer_as_a_row(self):
        import json
        mapping = json.loads(artifact('selected-heap-witness-map.json')[1].decode())
        rows = [r for r in mapping['covered_premise_bundles']
                if r['path'] == 'Solidity/Backend/Passes/TripleControls.lean']
        private = [r for r in rows if r['visibility'] == 'private']
        self.assertEqual(len(rows),20)
        self.assertEqual({r['name'].split('.')[-1] for r in private},
                         {'cell0','cell1','cell2','cell3','cell4','cell5','cell6','cell17','cell20'})
        for row in private:
            self.assertEqual(row['kernel_identity'],'_private.Solidity.Backend.Passes.TripleControls.0.'+row['name'])
            self.assertIsInstance(row['kernel_identity_components'][5],int)
            self.assertEqual(row['kernel_identity_components'][5],0)
            self.assertTrue(row['kernel_observer'].endswith('.cell'))
        self.assertNotIn('Solidity.Backend.Passes.TripleControls.cell',{r['name'] for r in rows})


    def test_reachability_counts_private_steps_not_helper_definitions(self):
        import json
        mapping = json.loads(artifact('selected-heap-witness-map.json')[1].decode())
        rows = [r for r in mapping['covered_premise_bundles']
                if r['path'] == 'Solidity/Backend/Passes/ReachabilityControls.lean']
        self.assertEqual(len(rows),14)
        private = [r for r in rows if r['visibility'] == 'private']
        self.assertEqual({r['name'].split('.')[-1] for r in private},
                         {'allocateA_run','writeA0_run','writeA1_run','allocateB_run','writeB0_run',
                          'aliasA_run','bottomB_run','middleA_run','zeroValue_run','write_run','read_run'})
        for row in private:
            self.assertEqual(row['kernel_identity'],'_private.Solidity.Backend.Passes.ReachabilityControls.0.'+row['name'])
            self.assertIsInstance(row['kernel_identity_components'][5],int)
            self.assertEqual(row['kernel_identity_components'][5],0)
        self.assertFalse(any(r['name'].endswith('.populatedBuilder') for r in rows))


    def test_linked_private_base_bound_has_validated_empty_axiom_set(self):
        import json
        mapping = json.loads(artifact('selected-heap-witness-map.json')[1].decode())
        rows = [r for r in mapping['covered_premise_bundles']
                if r['name'] == 'Solidity.Backend.Passes.LinkedControls.base_ge_sixteen']
        self.assertEqual(len(rows),1)
        row = rows[0]
        self.assertEqual(row['witness_status'],'kernel_checked_original_private_identity_and_joint_instance')
        self.assertEqual(row['kernel_identity'],'_private.Solidity.Backend.Passes.LinkedControls.0.'+row['name'])
        self.assertIsInstance(row['kernel_identity_components'][5],int)
        self.assertEqual(row['kernel_identity_components'][5],0)
        self.assertEqual(row['kernel_axioms'],[])


    def test_portable_inventory_matches_verified_external_ledger(self):
        import json
        ledger = json.loads(artifact('selected-heap-witness-map.json')[1])
        self.assertEqual(source_inventory_keys(),{(r['path'],r['name']) for r in ledger['covered_premise_bundles']})

if __name__ == '__main__':
    unittest.main()
