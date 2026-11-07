"""Guard regression: duplicate destination keys hide original pin occurrences."""
import hashlib
import importlib.util
from pathlib import Path
import unittest

root = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('pin_collision_report', root / 'scripts/h55/module-times/pin_collision_report.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class PinCollisionReport(unittest.TestCase):
    def test_preserves_colliding_origins_and_rejects_corruption(self):
        def row(old):
            return {'old_checker_key':old, 'suggested_new_key':'area:key', 'observed_block':'abc',
                    'block_sha256':hashlib.sha256(b'abc').hexdigest(), 'file':old, 'source_sha256':'x',
                    'target':'a', 'axioms':[], 'start_byte':0, 'end_byte':3}
        data = {'rows':[row('a'),row('b')], 'occurrences':2, 'duplicate_checker_keys':[],
                'duplicate_suggested_keys':[['area:key',2]]}
        result = module.report(data)
        self.assertEqual(2, len(result[0]['source_rows']))
        self.assertEqual('all-occurrences-require-context-and-multiplicity-review', result[0]['status'])
        with self.assertRaises(ValueError):
            module.report({**data, 'duplicate_suggested_keys':[]})
        with self.assertRaises(ValueError):
            module.report({**data, 'rows':[row('a'),row('a')]})
        with self.assertRaises(ValueError):
            bad = row('b'); bad['observed_block'] = 'changed'
            module.report({**data, 'rows':[row('a'),bad]})

if __name__ == '__main__':
    unittest.main()
