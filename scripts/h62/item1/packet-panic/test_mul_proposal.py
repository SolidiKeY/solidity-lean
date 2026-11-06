#!/usr/bin/env python3
"""Textual checks only: this does not elaborate Lean or apply the patch."""
import pathlib
import re
import subprocess
import unittest

DIRECTORY = pathlib.Path(__file__).resolve().parent
ROOT = DIRECTORY.parents[3]
SOURCE = ROOT / "Solidity/Backend/PrimitivePackets/CheckedMul/Controls.lean"
HELPER = ROOT / "Solidity/Backend/PrimitivePackets/PanicBytes.lean"


def statement(text, name):
    pattern = rf"(?ms)^theorem {name} : (.*?) := by\s*$"
    matches = re.findall(pattern, text)
    if len(matches) != 1:
        raise ValueError(f"expected one declaration of {name}, got {len(matches)}")
    return matches[0]


class ProposalTest(unittest.TestCase):
    def test_statements_and_unapplied_patch(self):
        source = SOURCE.read_text()
        helper = HELPER.read_text()
        for name in ("exact_panic_bytes", "panic_not_truncated", "panic_not_empty"):
            self.assertEqual(statement(source, name), statement(helper, name))
        patch = subprocess.check_output(["python3", str(DIRECTORY / "prepare_mul_patch.py")], cwd=ROOT)
        checked = subprocess.run(["git", "apply", "--check", "-"], cwd=ROOT, input=patch, capture_output=True)
        self.assertEqual(checked.returncode, 0, checked.stderr.decode())
        text = patch.decode()
        self.assertIn("PanicBytes.exact_panic_bytes", text)
        self.assertIn("PanicBytes.panic_not_truncated", text)
        self.assertNotIn("PanicBytes.panic_not_empty", text)
        self.assertNotIn("#print axioms", text)


if __name__ == "__main__":
    unittest.main()
