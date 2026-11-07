"""Guard regression: old references hide changed candidates or inflate new rows."""
import importlib.util
from pathlib import Path
import sys
import unittest

root = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(root/'scripts/h55/module-times'))
spec = importlib.util.spec_from_file_location('current_reference_drift', root/'scripts/h55/module-times/current_reference_drift.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class CurrentReferenceDrift(unittest.TestCase):
    def test_changed_new_removed_and_duplicate(self):
        old = [{'candidate':{'path':'a','sha256':'1'*64, 'context':'old'}, 'static_reference_artifacts':['/evidence/receipt']}]
        current = [{'path':'a','sha256':'2'*64,'context':'old'}, {'path':'b','sha256':'3'*64}]
        rows, removed = module.reconcile(old, current)
        self.assertEqual(['changed-candidate-review','new-candidate'], [r['state'] for r in rows])
        self.assertTrue(rows[0]['changed_bytes'])
        self.assertEqual([], removed)
        self.assertEqual(1, len(module.reconcile(old, [current[1]])[1]))
        with self.assertRaises(ValueError):
            module.reconcile([{'candidate':old[0]['candidate'], 'static_reference_artifacts':['']}], [])
        with self.assertRaises(ValueError):
            module.reconcile([{'candidate':old[0]['candidate'], 'static_reference_artifacts':['/evidence/../bad']}], [])
        with self.assertRaises(ValueError):
            module.reconcile(old, current + current[:1])
        with self.assertRaises(ValueError):
            module.reconcile(old, [{'path':'a','sha256':None}])

if __name__ == '__main__':
    unittest.main()
