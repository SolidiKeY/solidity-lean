import importlib.util
import pathlib
import sys
import hashlib
import json
import tempfile
from unittest.mock import patch
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'scripts/h55/shared-fixtures'))
import check_baseline_modules

spec = importlib.util.spec_from_file_location('compare', ROOT / 'scripts/h55/shared-fixtures/compare_source_exec.py')
compare = importlib.util.module_from_spec(spec)
spec.loader.exec_module(compare)


class ComparisonTests(unittest.TestCase):
    def setUp(self):
        self.key = ('module', 'name')
        self.row = {'typeExpr': 'T', 'valueExpr': 'V', 'axioms': [],
                    'unsafe': False, 'partial': False, 'axiom': False}
        self.before = {self.key: self.row}

    def test_baseline_pin_rejects_same_count_substitution(self):
        module = 'fixture.module'
        rows = {(module, name): {'name': name, 'typeExpr': 'T'} for name in ('first', 'second')}
        payload = json.dumps(list(rows.values()), sort_keys=True, separators=(',', ':'), ensure_ascii=True).encode()
        digest = hashlib.sha256(payload).hexdigest()
        with tempfile.TemporaryDirectory() as directory:
            pin = pathlib.Path(directory) / 'pins.json'
            pin.write_text(json.dumps({'test': {module: {'count': 2, 'records_sha256': digest}}}))
            with patch.object(check_baseline_modules, 'PINS', pin):
                check_baseline_modules.check(rows, 'test')
                altered = dict(rows)
                altered[(module, 'second')] = {'name': 'second', 'typeExpr': 'changed'}
                with self.assertRaises(ValueError):
                    check_baseline_modules.check(altered, 'test')
                substituted = {(module, name): {'name': name, 'typeExpr': 'T'} for name in ('first', 'third')}
                with self.assertRaises(ValueError):
                    check_baseline_modules.check(substituted, 'test')

    def test_type_body_and_axiom_changes_are_detected(self):
        for field, value in (('typeExpr', 'other'), ('valueExpr', 'other'), ('axioms', ['new'])):
            changed = dict(self.row)
            changed[field] = value
            with self.subTest(field=field):
                self.assertEqual(compare.differences(self.before, {self.key: changed})[2], [self.key])

    def test_removal_and_unsafe_addition_are_detected(self):
        self.assertEqual(compare.differences(self.before, {})[0], [self.key])
        new = ('module', 'new')
        addition = dict(self.row, axiom=True)
        self.assertEqual(compare.differences(self.before, {self.key: self.row, new: addition})[3], [new])

    def test_additive_safe_declaration_is_reported(self):
        new = ('module', 'new')
        removed, added, modified, unsafe = compare.differences(self.before, {self.key: self.row, new: self.row})
        self.assertEqual((removed, added, modified, unsafe), ([], [new], [], []))


if __name__ == '__main__':
    unittest.main()
