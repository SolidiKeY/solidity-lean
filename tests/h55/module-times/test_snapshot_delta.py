"""Guard regression: changed mappings and duplicate paths disappear from census deltas."""
import importlib.util
from pathlib import Path
import sys
import unittest

root = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(root / 'scripts/h55/module-times'))
spec = importlib.util.spec_from_file_location('snapshot_delta', root / 'scripts/h55/module-times/snapshot_delta.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class SnapshotDelta(unittest.TestCase):
    def test_added_removed_mapping_bytes_and_duplicates(self):
        a = [{'path':'a', 'sha256':'1', 'context':'old'}, {'path':'gone', 'sha256':'2'}]
        b = [{'path':'a', 'sha256':'3', 'context':'new'}, {'path':'new', 'sha256':'4'}]
        result = module.delta(a, b)
        self.assertEqual(['new'], [r['path'] for r in result['added']])
        self.assertEqual(['gone'], [r['path'] for r in result['removed']])
        self.assertEqual(['a'], result['changed_bytes'])
        self.assertEqual(['a'], result['changed_mapping'])
        with self.assertRaises(ValueError):
            module.delta(a + a[:1], b)

if __name__ == '__main__':
    unittest.main()
