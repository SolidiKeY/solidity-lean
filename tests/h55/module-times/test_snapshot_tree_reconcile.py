"""Guard regression: nonregular, mismatched or duplicate candidate paths appear verified."""
import hashlib
import importlib.util
from pathlib import Path
import unittest

root = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('snapshot_tree_reconcile', root / 'scripts/h55/module-times/snapshot_tree_reconcile.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class SnapshotTreeReconcile(unittest.TestCase):
    def test_tree_status_and_rejections(self):
        row = {'path':'a.lean', 'sha256':hashlib.sha256(b'a').hexdigest()}
        tree = {'a.lean': {'kind':'blob', 'mode':'100644', 'oid':'a'}}
        load = lambda oid: b'a'
        self.assertEqual('absent-at-old-tree', module.reconcile([row], {}, tree, load)[0]['path_status'])
        self.assertEqual('existing-path', module.reconcile([row], tree, tree, load)[0]['path_status'])
        with self.assertRaises(ValueError):
            module.reconcile([row, row], {}, tree, load)
        with self.assertRaises(ValueError):
            module.reconcile([row], {}, {'a.lean': {'kind':'blob', 'mode':'120000', 'oid':'a'}}, load)
        with self.assertRaises(ValueError):
            module.reconcile([row], {}, tree, lambda oid: b'changed')

if __name__ == '__main__':
    unittest.main()
