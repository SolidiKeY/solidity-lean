"""Finite planning controls; no Lean execution or metadata evidence."""
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
spec = importlib.util.spec_from_file_location('metadata_plan', scripts / 'plan-old-metadata.py')
plan = importlib.util.module_from_spec(spec)
spec.loader.exec_module(plan)

class MetadataPlan(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = pathlib.Path(self.tmp.name)
        self.source = self.root / 'Empty.lean'
        self.source.write_text('-- a module may register imported declarations\n')
        self.summary = self.root / 'summary.json'
        self.summary.write_text(json.dumps(dict(module='Empty', declarations=[],
            header=dict(expected_constants=0))))
        self.census = dict(yul_modules=['Empty'], modules=dict(Empty=dict(
            path='Empty.lean', sha256=plan.interfaces.digest(self.source))))
        self.inventory = dict(base=plan.BASE, status='pass', migration_acceptance=False,
            original_census_sha256='test-census', module_count=1,
            selected_for_verification=1, modules=[dict(module='Empty', declarations=0,
                summary=str(self.summary), summary_sha256=plan.interfaces.digest(self.summary))])

    def run_plan(self):
        return plan.make_plan(self.census, self.inventory, 'test-census', self.root)

    def test_empty_module_requires_query_and_deterministic_plan(self):
        first = self.run_plan()
        self.assertEqual(first, self.run_plan())
        self.assertEqual(first['queries_required'], 1)
        self.assertEqual(first['queries_performed'], 0)
        self.assertTrue(first['modules'][0]['query_required'])
        self.assertFalse(first['modules'][0]['query_performed'])
        self.assertFalse(first['migration_acceptance'])

    def test_duplicate_or_missing_module_rejected(self):
        for names in [[], ['Empty', 'Empty'], ['Other']]:
            with self.subTest(names=names):
                self.census['yul_modules'] = names
                with self.assertRaises(ValueError): self.run_plan()

    def test_provenance_and_counts_rejected(self):
        original = copy.deepcopy(self.inventory)
        for key, value in [('base','wrong'), ('status','partial'),
                ('migration_acceptance',True), ('module_count',True),
                ('selected_for_verification',0), ('original_census_sha256','wrong')]:
            self.inventory = copy.deepcopy(original)
            self.inventory[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError): self.run_plan()

    def test_source_or_summary_drift_rejected(self):
        for file in [self.source, self.summary]:
            before = file.read_bytes()
            file.write_bytes(before + b' ')
            with self.subTest(file=file), self.assertRaises(ValueError): self.run_plan()
            file.write_bytes(before)

    def test_rehashed_wrong_module_or_count_rejected(self):
        for module, count in [('Other',0), ('Empty',1)]:
            self.summary.write_text(json.dumps(dict(module=module, declarations=[],
                header=dict(expected_constants=count))))
            self.inventory['modules'][0]['summary_sha256'] = plan.interfaces.digest(self.summary)
            with self.subTest(module=module,count=count), self.assertRaises(ValueError): self.run_plan()

    def test_invalid_declaration_count_rejected(self):
        for count in [True, -1, 1, '0']:
            self.inventory['modules'][0]['declarations'] = count
            with self.subTest(count=count), self.assertRaises(ValueError): self.run_plan()

    def test_relative_summary_path_resolves_against_baseline(self):
        self.inventory['modules'][0]['summary'] = 'summary.json'
        result = self.run_plan()
        self.assertEqual(result['modules'][0]['kernel_summary'], str(self.summary.resolve()))

    def test_summary_parsed_from_captured_hashed_bytes(self):
        original_read = pathlib.Path.read_bytes
        reads = []
        def read_and_replace(path):
            data = original_read(path)
            if path == self.summary:
                reads.append(path)
                # Simulate mutation after the read: parsing must use captured bytes.
                path.write_text('invalid JSON after captured bytes')
            return data
        with patch.object(pathlib.Path, 'read_bytes', read_and_replace):
            result = self.run_plan()
        self.assertEqual(reads, [self.summary])
        self.assertEqual(result['modules'][0]['module'], 'Empty')
        # make_plan is an in-memory stage; main's final recheck rejects this drift.
        self.assertNotEqual(plan.interfaces.digest(self.summary),
                            self.inventory['modules'][0]['summary_sha256'])

    def test_cli_rejects_inputs_changed_during_planning(self):
        # Only bypass production size/pin for this finite input-race control.
        census_path = self.root / 'census.json'
        inventory_path = self.root / 'inventory.json'
        output = self.root / 'out.json'
        production_names = [f'Module{i}' for i in range(1774)]
        census_path.write_text(json.dumps(dict(yul_modules=production_names, modules=self.census['modules'])))
        inventory_path.write_text('{}')
        argv = ['plan', '--census', str(census_path), '--inventory', str(inventory_path),
                '--baseline', str(self.root), '--output', str(output)]
        for changed in [census_path, inventory_path, self.source, self.summary]:
            before = changed.read_bytes()
            def changed_plan(*args):
                changed.write_bytes(before + b' ')
                return dict(modules=[dict(kernel_summary=str(self.summary),
                    kernel_summary_sha256=self.inventory['modules'][0]['summary_sha256'])])
            with self.subTest(changed=changed), patch.object(sys, 'argv', argv), \
                    patch.object(plan, 'CENSUS_SHA256', plan.interfaces.digest(census_path)), \
                    patch.object(plan, 'make_plan', side_effect=changed_plan):
                with self.assertRaisesRegex(ValueError, 'inputs changed'):
                    plan.main()
            self.assertFalse(output.exists())
            changed.write_bytes(before)

if __name__ == '__main__': unittest.main()
