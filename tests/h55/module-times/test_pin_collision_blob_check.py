"""Guard regression: a mismatched pin source or byte span counts as verified."""
import hashlib
import importlib.util
from pathlib import Path
import unittest
import sys

root = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(root/'scripts/h55/module-times'))
spec = importlib.util.spec_from_file_location('pin_collision_blob_check', root/'scripts/h55/module-times/pin_collision_blob_check.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class PinCollisionBlobCheck(unittest.TestCase):
    def test_checks_source_bytes_and_span(self):
        row = {'old_checker_key':'file:key', 'suggested_new_key':'dest:key', 'file':'file',
               'source_sha256':hashlib.sha256(b'xabc').hexdigest(), 'start_byte':1, 'end_byte':4,
               'observed_block':'abc', 'block_sha256':hashlib.sha256(b'abc').hexdigest()}
        proposal = {'rows':[row]}
        report = {'rows':[{'suggested_key':'dest:key','source_rows':[{'old_checker_key':'file:key'}]}],
                  'collision_groups':1, 'colliding_occurrences':1}
        self.assertEqual(1, len(module.check_rows(proposal, report, lambda path: b'xabc')))
        with self.assertRaises(ValueError):
            module.check_rows(proposal, report, lambda path: b'xabd')
        with self.assertRaises(ValueError):
            module.check_rows({'rows':[{**row, 'start_byte':0}]}, report, lambda path: b'xabc')
        with self.assertRaises(ValueError):
            module.check_rows(proposal, {**report, 'rows':report['rows']*2}, lambda path: b'xabc')

if __name__ == '__main__':
    unittest.main()
