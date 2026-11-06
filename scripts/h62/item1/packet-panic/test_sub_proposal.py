#!/usr/bin/env python3
"""Textual checks only: no Lean elaboration and no patch application."""
import pathlib
import subprocess
import unittest
from test_mul_proposal import statement

DIRECTORY = pathlib.Path(__file__).resolve().parent
ROOT = DIRECTORY.parents[3]
SOURCE = ROOT / "Solidity/Backend/PrimitivePackets/CheckedSub/Controls.lean"
HELPER = ROOT / "tests/h62/item1/packet-panic/PanicBytes.lean"
NAMES = ("exact_panic_bytes", "panic_not_truncated", "panic_not_empty")


class ProposalTest(unittest.TestCase):
    def test_statements_and_unapplied_patch(self):
        source, helper = SOURCE.read_text(), HELPER.read_text()
        for name in NAMES:
            self.assertEqual(statement(source, name), statement(helper, name))
        patch = subprocess.check_output(["python3", str(DIRECTORY / "prepare_sub_patch.py")], cwd=ROOT)
        checked = subprocess.run(["git", "apply", "--check", "-"], cwd=ROOT, input=patch, capture_output=True)
        self.assertEqual(checked.returncode, 0, checked.stderr.decode())
        lines = patch.decode().splitlines()
        removed = [line for line in lines if line.startswith("-") and not line.startswith("---")]
        added = [line for line in lines if line.startswith("+") and not line.startswith("+++")]
        self.assertEqual(removed, ["-  first | decide | rfl | omega"] * 3)
        self.assertEqual(added, ["+import Solidity.Backend.PrimitivePackets.PanicBytes"] +
                         ["+  exact Solidity.Backend.PrimitivePackets.PanicBytes." + name for name in NAMES])


if __name__ == "__main__":
    unittest.main()
