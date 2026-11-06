#!/usr/bin/env python3
"""Negative controls for the declaration census."""
import contextlib
import io
import pathlib
import tempfile
import unittest
import census

class CensusTest(unittest.TestCase):
    def test_missing_and_duplicate_definitions_fail(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            for path, names in census.FILES.items():
                target = root / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text("\n".join(f"def {name} (x : Nat) := x" for name in names))
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(census.census(root), 0)
                target = root / next(iter(census.FILES))
                original = target.read_text()
                target.write_text(original + "\ndef STy.isMapping (x : Nat) := x\n")
                self.assertEqual(census.census(root), 1)
                target.write_text(original.replace("def STy.isMapping", "def renamed"))
                self.assertEqual(census.census(root), 1)
                target.unlink()
                with contextlib.redirect_stderr(io.StringIO()):
                    self.assertEqual(census.census(root), 1)

if __name__ == "__main__":
    unittest.main()
