#!/usr/bin/env python3
"""Reject a wrong mapping, payable or location result in each case."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest
import check_case_values

ROOT = Path(__file__).resolve().parents[4]

class CaseValueTest(unittest.TestCase):
    def test_all_result_mutations(self):
        original = (ROOT / check_case_values.SPEC).read_text(encoding="utf-8")
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            target = root / check_case_values.SPEC
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(original, encoding="utf-8")
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(check_case_values.check(root), 0)
                for name, (args, mapping, payable, location) in check_case_values.ROWS.items():
                    prefix = f"  | .{name}" + (f" {args}" if args else "") + " => "
                    line = prefix + f"({mapping}, {payable}, {location})"
                    self.assertEqual(original.count(line), 1)
                    for field in range(3):
                        altered = [mapping, payable, location]
                        altered[field] = ({"true": "false", "false": "true"}.get(altered[field], ".storage"))
                        changed = prefix + "(" + ", ".join(altered) + ")"
                        with self.subTest(name=name, field=field):
                            target.write_text(original.replace(line, changed, 1), encoding="utf-8")
                            self.assertEqual(check_case_values.check(root), 1)
                target.write_text(original.replace("  | .bool =>", "  | _ => (false, false, .memory)\n  | .bool =>", 1), encoding="utf-8")
                self.assertEqual(check_case_values.check(root), 1)
                target.unlink()
                self.assertEqual(check_case_values.check(root), 1)

if __name__ == "__main__":
    unittest.main()
