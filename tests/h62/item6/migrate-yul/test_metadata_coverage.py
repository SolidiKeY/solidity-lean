"""Synthetic ledger controls; actual saved observations are re-sealed separately."""
import copy
import importlib.util
import json
import pathlib
import sys
import tempfile
import unittest
from unittest.mock import patch

scripts = pathlib.Path(__file__).resolve().parents[4] / 'scripts/h62/item6/migrate-yul'
sys.path.insert(0, str(scripts))
spec = importlib.util.spec_from_file_location('coverage_test', scripts / 'metadata-coverage.py')
coverage = importlib.util.module_from_spec(spec)
spec.loader.exec_module(coverage)

class MetadataCoverage(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = pathlib.Path(self.tmp.name)
        self.job = dict(module='Example', kernel_declarations=0, kernel_summary='unused')
        self.plan = dict(modules=[self.job], baseline=str(self.root))
        self.path = self.root / 'observation.json'
        self.raw = self.root / 'raw.jsonl'
        self.raw.write_text('synthetic raw; not Lean evidence')
        self.probe = self.root / 'probe.json'
        self.probe_data = dict(head=coverage.planner.BASE, repository=str(self.root),
            census_sha256=coverage.planner.CENSUS_SHA256,
            lean='797c613eb9b6d4ec95db23e3e00af9ac6657f24b', probe_sources_before={})
        self.probe.write_text(json.dumps(self.probe_data))
        self.sealed = dict(module='Example', raw=str(self.raw), probe=str(self.probe),
            raw_sha256=coverage.sha(self.raw), probe_sha256=coverage.sha(self.probe),
            footer=dict(declarations=0, classes=0, instances=0, defaults=0),
            migration_acceptance=False)
        self.path.write_text(json.dumps(self.sealed))

    def test_pending_modules_are_retained(self):
        result = coverage.make_ledger(self.plan, [], {})
        self.assertEqual((result['observed_modules'], result['pending_modules']), (0, 1))
        self.assertEqual(result['modules'][0]['status'], 'pending')
        self.assertFalse(result['migration_acceptance'])

    def test_duplicate_observation_rejected(self):
        with patch.object(coverage, 'seal_observation', return_value=dict(status='observed')):
            with self.assertRaisesRegex(ValueError, 'duplicate observed module'):
                coverage.make_ledger(self.plan, [self.path, self.path], {})

    def test_fixture_outside_original_scope_rejected(self):
        self.path.write_text(json.dumps(dict(module='DeclarationMetadataFixture')))
        with self.assertRaisesRegex(ValueError, 'outside original scope'):
            coverage.make_ledger(self.plan, [self.path], {})

    def test_order_and_unique_coverage(self):
        second = self.root / 'second.json'
        second.write_text(json.dumps(dict(module='Other')))
        self.plan['modules'].append(dict(module='Other', kernel_declarations=5))
        with patch.object(coverage, 'seal_observation', return_value=dict(status='observed')):
            one = coverage.make_ledger(self.plan, [self.path, second], {})
            two = coverage.make_ledger(self.plan, [second, self.path], {})
        self.assertEqual(one, two)
        self.assertEqual((one['observed_modules'], one['pending_modules']), (2, 0))
        self.assertFalse(one['migration_acceptance'])

    def seal(self, expected=None, declarations=0):
        with patch.object(coverage.metadata, 'seal', return_value=expected or self.sealed), \
                patch.object(coverage.metadata, 'check_original_coverage',
                             return_value=dict(declarations=declarations)):
            return coverage.seal_observation(self.path, self.job, self.plan, {})

    def test_raw_reseal_mismatch_rejected(self):
        stale = copy.deepcopy(self.sealed)
        stale['footer']['instances'] = 1
        with self.assertRaisesRegex(ValueError, 'differs from raw reseal'):
            self.seal(stale)

    def test_unknown_acceptance_claim_rejected(self):
        record = dict(self.sealed, semantic_equivalence=True)
        self.path.write_text(json.dumps(record))
        with self.assertRaisesRegex(ValueError, 'unknown observation fields'):
            self.seal()

    def test_wrong_original_probe_rejected(self):
        self.probe_data['head'] = 'different-source'
        self.probe.write_text(json.dumps(self.probe_data))
        self.sealed['probe_sha256'] = coverage.sha(self.probe)
        self.path.write_text(json.dumps(self.sealed))
        with self.assertRaisesRegex(ValueError, 'source/toolchain mismatch'):
            self.seal()

    def test_original_declaration_count_mismatch_rejected(self):
        with self.assertRaisesRegex(ValueError, 'count differs'):
            self.seal(declarations=1)

    def test_changed_bound_input_rejected(self):
        bindings = {}
        coverage.read_bound(self.path, bindings)
        self.path.write_text(json.dumps(dict(module='changed')))
        with self.assertRaisesRegex(ValueError, 'input changed'):
            coverage.read_bound(self.path, bindings)

    def test_final_source_change_rejected_before_output(self):
        source = self.root / 'source.lean'
        source.write_text('original source')
        output = self.root / 'output.json'
        def plan_with_source(path, bindings):
            bindings[source] = coverage.sha(source)
            return self.plan
        def changed_during_collection(*args):
            source.write_text('changed source')
            return {}
        argv = ['coverage', '--plan', 'unused', '--output', str(output)]
        with patch.object(sys, 'argv', argv), \
                patch.object(coverage, 'load_plan', side_effect=plan_with_source), \
                patch.object(coverage, 'make_ledger', side_effect=changed_during_collection):
            with self.assertRaisesRegex(ValueError, 'inputs changed'):
                coverage.main()
        self.assertFalse(output.exists())

if __name__ == '__main__': unittest.main()
