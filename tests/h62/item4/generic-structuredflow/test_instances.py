"""Guard exact-instance extraction against missing, duplicate and forged headers."""
import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[4]/'scripts/h62/item4/generic-structuredflow'))
import instances

class InstanceExtraction(unittest.TestCase):
    def setUp(self):
        self.row = dict(path='fixture', name='Scope.observed', statement='theorem observed : True',
                        statement_sha256=instances.c.sha('theorem observed : True'))
    def test_exact(self):
        self.assertEqual(instances.select([self.row], 'fixture', 'observed'), self.row)
    def test_missing(self):
        with self.assertRaises(ValueError): instances.select([], 'fixture', 'observed')
    def test_duplicate(self):
        with self.assertRaises(ValueError): instances.select([self.row,self.row], 'fixture', 'observed')
    def test_wrong_path(self):
        with self.assertRaises(ValueError): instances.select([self.row], 'other', 'observed')
    def test_wrong_name(self):
        with self.assertRaises(ValueError): instances.select([self.row], 'fixture', 'nonzero_frame')
    def test_forged_statement(self):
        with self.assertRaises(ValueError): instances.select([dict(self.row, statement='theorem observed : False')], 'fixture', 'observed')

if __name__ == '__main__': unittest.main()
