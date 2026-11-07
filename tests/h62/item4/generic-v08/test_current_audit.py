"""Refusal checks for current-family extension accounting."""
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[4] / 'scripts/h62/item4/generic-v08'))
from audit_current import compare


def fixture(paths):
    return {'files': [{'path': p, 'sha256': h} for p, h in paths],
            'declarations': [{'path': p, 'ordinal': 1, 'header': h} for p, h in paths]}


class CurrentAudit(unittest.TestCase):
    def test_additions_are_reported_not_lost(self):
        original = fixture([('A', 'a')])
        report = compare(original, fixture([('A', 'a'), ('Nested/B', 'b')]))
        self.assertEqual(report['original_integrity'], 'pass')
        self.assertEqual(report['added'], ['Nested/B'])
        self.assertEqual(report['added_declarations'][0]['path'], 'Nested/B')
        self.assertEqual(report['current_declaration_count'], 2)

    def test_statement_or_proof_body_change_refused(self):
        self.assertEqual(compare(fixture([('A', 'a')]), fixture([('A', 'changed')]))['original_integrity'], 'fail')

    def test_missing_original_refused_even_with_replacement(self):
        report = compare(fixture([('A', 'a')]), fixture([('B', 'a')]))
        self.assertEqual(report['original_integrity'], 'fail')
        self.assertEqual(report['removed'], ['A'])

    def test_no_changes(self):
        original = fixture([('A', 'a')])
        self.assertEqual(compare(original, original)['added'], [])


if __name__ == '__main__':
    unittest.main()
