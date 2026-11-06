#!/usr/bin/env python3
"""Negative controls for the textual census, using isolated temporary copies."""
import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest
from contextlib import redirect_stdout
from io import StringIO

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("census", HERE / "census.py")
census = importlib.util.module_from_spec(spec)
spec.loader.exec_module(census)
SOURCE = census.ROOT / "Solidity/Lowering/Readonly"

class CensusControls(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.dest = self.root / "Solidity/Lowering/Readonly"
        self.dest.mkdir(parents=True)
        for filename in census.FILES:
            data = subprocess.run(["git", "show", "c6f550e281a7e5affa9a99bc2cdaed556dec00e4:Solidity/Lowering/Readonly/" + filename], cwd=census.ROOT, check=True, capture_output=True).stdout
            (self.dest / filename).write_bytes(data)

    def tearDown(self):
        self.temp.cleanup()

    def scan(self):
        with redirect_stdout(StringIO()):
            return census.scan(self.root)

    def change(self, filename, old, new):
        path = self.dest / filename
        text = path.read_text(encoding="utf-8")
        self.assertIn(old, text)
        path.write_text(text.replace(old, new, 1), encoding="utf-8")

    def test_baseline(self):
        self.assertEqual(self.scan(), 0)

    def test_missing_helper(self):
        self.change("CapturePhases.lean", "private theorem run_bind", "private theorem renamed")
        self.assertEqual(self.scan(), 1)

    def test_duplicate_helper(self):
        path = self.dest / "CaptureFailures.lean"
        path.write_text(path.read_text(encoding="utf-8") + "\nprivate theorem run_bind\n", encoding="utf-8")
        self.assertEqual(self.scan(), 1)

    def test_missing_consumer(self):
        self.change("EnvironmentCredit.lean", "theorem callback_credit_failed", "theorem renamed_callback")
        self.assertEqual(self.scan(), 1)

    def test_new_consumer(self):
        path = self.dest / "CapturePhases.lean"
        path.write_text(path.read_text(encoding="utf-8") + "\ntheorem extra := by simp only [run_bind]\n", encoding="utf-8")
        self.assertEqual(self.scan(), 1)

    def test_migrated_files(self):
        with redirect_stdout(StringIO()):
            self.assertEqual(census.scan(census.ROOT, migrated=True), 0)

    def test_missing_file(self):
        (self.dest / "CaptureFailures.lean").unlink()
        self.assertEqual(self.scan(), 1)

if __name__ == "__main__":
    unittest.main()
