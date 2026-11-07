#!/usr/bin/env python3
"""Negative controls for constructor coverage, not Lean proofs."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest
import check_cases

ROOT = Path(__file__).resolve().parents[4]

class ConstructorCoverage(unittest.TestCase):
    def test_missing_duplicate_and_new_constructor(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for path in (check_cases.SOURCE, check_cases.SPEC):
                target = root / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text((ROOT / path).read_text())
            source = (root / check_cases.SOURCE).read_text()
            spec = (root / check_cases.SPEC).read_text()
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(check_cases.check(root), 0)
                target = root / check_cases.SPEC
                arm = "  | .bool => (false, false, .memory)\n"
                self.assertIn(arm, spec)
                target.write_text(spec.replace(arm, "", 1))
                self.assertEqual(check_cases.check(root), 1)
                target.write_text(spec.replace(arm, arm + arm, 1))
                self.assertEqual(check_cases.check(root), 1)
                target.write_text(spec)
                source_target = root / check_cases.SOURCE
                source_target.write_text(source.replace("  | bool\n", "  | bool\n  | newConstructor\n", 1))
                self.assertEqual(check_cases.check(root), 1)
                source_target.write_text(source)
                target.unlink()
                self.assertEqual(check_cases.check(root), 1)

if __name__ == "__main__":
    unittest.main()
