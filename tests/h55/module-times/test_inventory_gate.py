import copy
import contextlib
import hashlib
import io
import json
import importlib.util
import pathlib
import subprocess
import tempfile
from unittest import mock
import unittest

path = pathlib.Path(__file__).resolve().parents[3] / "scripts/h55/module-times/inventory_gate.py"
spec = importlib.util.spec_from_file_location("inventory_gate", path)
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


class InventoryGate(unittest.TestCase):
    def setUp(self):
        self.current = [{"path": "Solidity/A.lean", "sha256": "a" * 64},
                        {"path": "Bridge/tests/B.lean", "sha256": "b" * 64}]
        self.rows = [{**self.current[0], "context": "root", "method": "module"},
                     {**self.current[1], "context": "bridge", "method": "file-check"}]

    def test_exact_and_missing_duplicate_extra(self):
        self.assertEqual([], gate.validate(self.current, self.rows))
        for rows in [[], self.rows[:1], self.rows + [self.rows[0]],
                     self.rows + [{**self.rows[0], "path": "Solidity/C.lean"}]]:
            with self.subTest(rows=rows):
                self.assertTrue(gate.validate(self.current, rows))

    def test_staged_edit_cancelled_in_worktree_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            source = root / "A.lean"
            source.write_text("-- original\n")
            subprocess.run(["git", "-C", str(root), "add", "A.lean"], check=True)
            subprocess.run(["git", "-C", str(root), "-c", "user.name=Fixture", "-c",
                            "user.email=fixture@example.invalid", "commit", "-qm", "base"], check=True)
            source.write_text("-- staged\n")
            subprocess.run(["git", "-C", str(root), "add", "A.lean"], check=True)
            source.write_text("-- original\n")
            manifest = root / "inventory.json"
            manifest.write_text(json.dumps([{"path": "A.lean",
                "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                "context": "root", "method": "file-check"}]))
            self.assertEqual(0, subprocess.run(["git", "diff", "--quiet", "HEAD", "--", "*.lean"], cwd=root).returncode)
            self.assertEqual(1, subprocess.run(["git", "diff", "--cached", "--quiet", "HEAD", "--", "*.lean"], cwd=root).returncode)
            stderr = io.StringIO()
            with mock.patch.object(gate, "ROOT", root), mock.patch.object(gate.sys, "argv", ["inventory_gate.py", str(manifest)]), contextlib.redirect_stderr(stderr):
                self.assertEqual(1, gate.main())
            self.assertIn("tracked Lean source differs from HEAD", stderr.getvalue())

    def test_assume_unchanged_source_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            source = root / "A.lean"
            source.write_text("-- original\n")
            subprocess.run(["git", "-C", str(root), "add", "A.lean"], check=True)
            subprocess.run(["git", "-C", str(root), "-c", "user.name=Fixture", "-c",
                            "user.email=fixture@example.invalid", "commit", "-qm", "base"], check=True)
            subprocess.run(["git", "-C", str(root), "update-index", "--assume-unchanged", "A.lean"], check=True)
            source.write_text("-- altered\n")
            manifest = root / "inventory.json"
            manifest.write_text(json.dumps([{"path": "A.lean",
                "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                "context": "root", "method": "file-check"}]))
            self.assertEqual(0, subprocess.run(["git", "diff", "--quiet", "HEAD", "--", "*.lean"], cwd=root).returncode)
            stderr = io.StringIO()
            with mock.patch.object(gate, "ROOT", root), mock.patch.object(gate.sys, "argv", ["inventory_gate.py", str(manifest)]), contextlib.redirect_stderr(stderr):
                self.assertEqual(1, gate.main())
            self.assertIn("Lean index has unverified flags or stages", stderr.getvalue())

    def test_unresolved_forged_and_malformed(self):
        for key, value in [("sha256", "c" * 64), ("sha256", None), ("context", "review"),
                           ("context", None), ("method", "exclude"), ("method", None)]:
            rows = copy.deepcopy(self.rows)
            rows[0][key] = value
            with self.subTest(key=key, value=value):
                self.assertTrue(gate.validate(self.current, rows))
        self.assertTrue(gate.validate([], self.rows))
        self.assertTrue(gate.validate(self.current + [self.current[0]], self.rows))
        self.assertTrue(gate.validate(self.current, [None]))


if __name__ == "__main__":
    unittest.main()
