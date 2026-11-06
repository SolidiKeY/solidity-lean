import importlib.util
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('ledger', ROOT / 'scripts/h55/shared-fixtures/change_ledger.py')
ledger = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ledger)


class PartitionTests(unittest.TestCase):
    def test_identical_and_empty(self):
        self.assertEqual(ledger.partition('', ''), [])
        self.assertEqual([x['kind'] for x in ledger.partition('a\nb\n', 'a\nb\n')], ['equal'])

    def test_insert_delete_and_replace(self):
        for old, new, expected in [('a\n', 'x\na\n', 'insert'),
                                   ('x\na\n', 'a\n', 'delete'),
                                   ('a\n', 'b\n', 'replace')]:
            with self.subTest(expected=expected):
                self.assertIn(expected, [x['kind'] for x in ledger.partition(old, new)])

    def test_final_newline_is_not_lost(self):
        self.assertEqual(ledger.partition('a', 'a\n')[0]['kind'], 'replace')


if __name__ == '__main__':
    unittest.main()
