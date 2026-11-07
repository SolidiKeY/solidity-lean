"""Acceptance of classification boundaries and source preservation, no Lean proof."""
import tempfile
import json
from pathlib import Path
import sys
import unittest

ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'scripts/h62/item4/generic-memorycopies'))
from census import census
from semantic_groups import build

class SemanticGroupingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.inventory=census(ROOT)
        cls.report=build(ROOT,cls.inventory)
        cls.rows={(Path(row['path']).stem,row['name']):row for row in cls.report['declarations']}

    def test_exact_declaration_bijection(self):
        original={(f['path'],d['line'],d['name']):(d['header_sha256'],d['source_region_sha256'])
                  for f in self.inventory['files'] for d in f['declarations']}
        grouped={(d['path'],d['line'],d['name']):(d['header_sha256'],d['source_region_sha256']) for d in self.report['declarations']}
        self.assertEqual(len(grouped),len(self.report['declarations']))
        self.assertEqual(grouped,original)
        self.assertEqual(len(grouped),3905)

    def test_all_modules_including_empty_aggregator(self):
        original={f['path']:f['sha256'] for f in self.inventory['files']}
        grouped={f['path']:f['file_sha256'] for f in self.report['modules']}
        self.assertEqual(grouped,original)
        self.assertEqual(len(grouped),300)
        source=next(m for m in self.report['modules'] if m['path'].endswith('/SourceInterface.lean'))
        self.assertTrue(source['aggregator'])
        self.assertEqual(source['declaration_count'],0)

    def test_every_evidence_span_matches_exact_source_bytes(self):
        sources={f['path']:(ROOT/f['path']).read_bytes() for f in self.inventory['files']}
        for row in self.report['declarations']:
            for item in row['literal_evidence']:
                self.assertEqual(sources[row['path']][item['byte_start']:item['byte_end']].decode(),item['excerpt'])

    def test_no_namespace_or_constructor_domain_conflation(self):
        modules={Path(m['path']).stem:m for m in self.report['modules']}
        self.assertEqual(modules['AliasBinding']['group'],'alias_binding')
        self.assertEqual(modules['RuntimeRebind']['group'],'allocating_rebinding')
        self.assertEqual(modules['CanonicalRebind']['group'],'allocating_rebinding')
        self.assertEqual(modules['EmptyReferenceStorage']['group'],'empty_reference_allocation')
        self.assertIn('arbitrary map-free',modules['EmptyReferenceStorage']['description'])
        self.assertEqual(modules['SourceBytes']['domains'],['source_execution'])
        self.assertIn('source_execution',modules['Premises']['domains'])
        for row in self.report['declarations']:
            self.assertNotIn('word_success_literal',row['statement_axes'])
            self.assertNotIn('source_success_literal',row['statement_axes'])
        for name in ('input','expression'):
            self.assertEqual(self.rows['AllocationPanic',name]['role'],'control_fixture')

    def test_distinct_negative_and_positive_semantics(self):
        expected={
            ('ControlsV2','default_cost_W_rejected'):'certificate_impossibility',
            ('TypedCaptureControls','invalid_bounds'):'intrinsic_option_refusal',
            ('ForwardOverlapControls','right_overlap_run'):'successful_corruption',
            ('SourceCopyHorizonControls','mapping_refusal'):'source_stuck_unchanged',
            ('SourceCopyHorizonControls','partial_timeout'):'source_timeout_partial_allocation',
            ('SourceStoredReferencesControls','horizon_refusal'):'source_timeout_unchanged',
            ('NestedMemoryLoopControls','saturated_completed_suffix'):'success_at_saturation',
            ('EmptyReferenceStorageControls','unread_storage_run'):'success_despite_unread_storage',
            ('CheckedDefaultControls','unfittable_selected'):'inhabited_selector',
            ('CheckedFixedMemoryControls','huge_code_only_refusal'):'code_only_target_revert',
            ('EmptyReferenceStorageControls','wrong_header_not_represented'):'invalid_representation_premise',
            ('SnapshotPathControls','long_schedule'):'long_operation_schedule',
            ('SnapshotPathInterface','SnapshotPathFailure'):'successful_prefix_and_intrinsic_refusal',
        }
        for key,category in expected.items():
            self.assertEqual(self.rows[key]['curated_semantics']['category'],category)
        self.assertNotIn('revert_literal',self.rows['TypedCaptureControls','invalid_bounds']['statement_axes'])

    def test_multiclaim_and_alias_retention(self):
        for name in ('guard_reads_cursor','header_selects_capacity'):
            stem='CheckedMemoryArrayControls' if name=='guard_reads_cursor' else 'CheckedStorageArrayControls'
            row=self.rows[stem,name]
            self.assertEqual(row['curated_semantics']['category'],'mixed_success_and_target_revert')
            self.assertIn('revert_literal',row['statement_axes'])
        actual=self.rows['MemoryPathCopyControls','actual_binding']
        for axis in ('bare_ok_literal','heap_ownership','payload_observation','allocator_observation','local_or_stack_observation'):
            self.assertIn(axis,actual['statement_axes'])
        self.assertIn(actual['id'],self.report['retained_alias_identity_ids'])
        self.assertEqual(self.rows['TypedCaptureControls','reference_identities']['curated_semantics']['category'],'shallow_identity_overwrite')
        self.assertIn(self.rows['MemoryCopyDemandControls','initial_sharing']['id'],self.report['retained_alias_identity_ids'])
        self.assertIn(self.rows['MemoryCopyDemandControls','copied_children_are_distinct']['id'],self.report['retained_alias_identity_ids'])

    def test_legacy_negative_signals_are_retained_without_result_inference(self):
        negative=[d for d in self.report['declarations'] if d['legacy_negative_name_signal']]
        self.assertEqual(len(negative),402)
        self.assertLessEqual({d['id'] for d in negative},set(self.report['retained_refusal_related_ids']))
        self.assertIn('bare_ok_literal',self.rows['EmptyReferenceStorageControls','unread_storage_run']['statement_axes'])

    def test_new_family_requires_explicit_registration(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            family=root/'Solidity/Backend/MemoryCopies'
            family.mkdir(parents=True)
            (family/'UnregisteredControls.lean').write_text('theorem test : True := by trivial')
            with self.assertRaisesRegex(ValueError,'unregistered family'):
                build(root,census(root))

if __name__=='__main__': unittest.main()
