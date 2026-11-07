#!/usr/bin/env python3
import hashlib
import json
import pathlib
import subprocess
import tempfile
import unittest

SCRIPT = pathlib.Path(__file__).with_name("inventory.py")


class InventoryTest(unittest.TestCase):
    def test_occurrences_and_reconciliation_failure(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            census = root / "census.json"
            rel = "Solidity/Backend/PrimitivePackets/A/Controls.lean"
            path = root / rel
            path.parent.mkdir(parents=True)
            path.write_bytes(("theorem exact_panic_bytes : panicData .arithmetic = [] := by trivial\r\n"
                            "theorem both : panicData .arithmetic = panicData .divZero := by trivial\r\n"
                            "-- panicData is text in a comment\r\n").encode())
            entry = {"file": rel, "line": 1, "declaration": "exact_panic_bytes"}
            census.write_text(json.dumps({"declarations": [entry]}))
            cmd = ["python3", str(SCRIPT), "--root", str(root), "--named-census", str(census)]
            result = json.loads(subprocess.check_output(cmd))
            self.assertEqual(result["occurrences"][0]["sha256"], hashlib.sha256(path.read_bytes()).hexdigest())
            self.assertEqual(result["counts"], {"named_control": 1, "other_reference": 3})
            self.assertEqual([r["panic_code_hint"] for r in result["occurrences"]],
                             ["arithmetic", "arithmetic", "divZero", None])
            self.assertEqual([r["line"] for r in result["occurrences"]], [1, 2, 2, 3])
            census.write_text(json.dumps({"declarations": [{**entry, "line": 9}]}))
            failed = subprocess.run(cmd, capture_output=True, text=True)
            self.assertNotEqual(failed.returncode, 0)
            self.assertIn("reconciliation failed", failed.stderr)
            census.write_text(json.dumps({"declarations": [{**entry, "line": 3}]}))
            self.assertNotEqual(subprocess.run(cmd, capture_output=True).returncode, 0)
            census.write_text(json.dumps({"declarations": [{**entry, "declaration": "wrong"}]}))
            self.assertNotEqual(subprocess.run(cmd, capture_output=True).returncode, 0)
            census.write_text(json.dumps({"declarations": []}))
            self.assertNotEqual(subprocess.run(cmd, capture_output=True).returncode, 0)
            census.write_text(json.dumps({"declarations": [entry, entry]}))
            self.assertNotEqual(subprocess.run(cmd, capture_output=True).returncode, 0)
            path.write_text("theorem exact_panic_bytes :\n  panicData .arithmetic = [] := by trivial\n")
            census.write_text(json.dumps({"declarations": [entry]}))
            self.assertNotEqual(subprocess.run(cmd, capture_output=True).returncode, 0)


if __name__ == "__main__":
    unittest.main()
