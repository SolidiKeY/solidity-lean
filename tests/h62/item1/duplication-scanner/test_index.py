import importlib.util
import json
import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
SCRIPT = ROOT / "scripts/h62/item1/duplication-scanner/index_audit.py"
spec = importlib.util.spec_from_file_location("h62_index", SCRIPT)
indexer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(indexer)

class IndexControls(unittest.TestCase):
    def test_wrong_input_rejected(self):
        with self.assertRaises(ValueError):
            indexer.index(b"1. modified\n")

    def test_exact_frozen_output(self):
        saved = ROOT / "tests/h62/item1/duplication-scanner/audit-index.json"
        data = json.loads(saved.read_text())
        self.assertEqual([x["id"] for x in data["items"]], list(range(1, 20)))
        self.assertEqual(data["audit_sha256"], indexer.AUDIT_SHA256)
        self.assertTrue(all(x["unowned_mechanical_opportunity"] == "not-established" for x in data["items"]))
        source = ROOT / "tests/h62/item1/duplication-scanner/audit-source.md"
        actual = subprocess.check_output([sys.executable, "-B", str(SCRIPT), str(source)])
        self.assertEqual(actual, saved.read_bytes())

if __name__ == "__main__":
    unittest.main()
