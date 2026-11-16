import importlib.util
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('compare', ROOT / 'scripts/h55/shared-fixtures/compare_source_exec.py')
compare = importlib.util.module_from_spec(spec)
spec.loader.exec_module(compare)


class ComparisonTests(unittest.TestCase):
    def setUp(self):
        self.key = ('module', 'name')
        self.row = {'typeExpr': 'T', 'valueExpr': 'V', 'axioms': [],
                    'unsafe': False, 'partial': False, 'axiom': False}
        self.before = {self.key: self.row}

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
