#!/usr/bin/env python3
"""Textual checks only: this does not elaborate Lean or apply the patch."""
import hashlib
import pathlib
import re
import subprocess
import unittest

DIRECTORY = pathlib.Path(__file__).resolve().parent
ROOT = DIRECTORY.parents[3]
SOURCE = ROOT / "Solidity/Backend/PrimitivePackets/CheckedMul/Controls.lean"
HELPER = ROOT / "Solidity/Backend/PrimitivePackets/PanicBytes.lean"
HELPER_SHA256 = "c1d3eeb8f7c23308ee1b0b33fb7be331e7792f7bf8e646812517453db7428246"


def statement(text, name):
    """Extract the reviewed restricted header form; this is not a Lean parser."""
    headers = list(re.finditer(rf"(?m)^theorem {re.escape(name)} : ", text))
    if len(headers) != 1:
        raise ValueError(f"expected one header for {name}, got {len(headers)}")
    pieces = []
    boundary = re.compile(r"^[ \t]*(?:(?:private|protected|noncomputable|unsafe|partial)[ \t]+)*(?:theorem|lemma|def|abbrev|example|opaque|instance|namespace|end|#)\b")
    for index, line in enumerate(text[headers[0].end():].splitlines(keepends=True)):
        if any(marker in line for marker in ("--", "/-", "@[")):
            break
        if index and (not line.startswith((" ", "\t")) or boundary.match(line)):
            break
        ending = re.search(r" := by[ \t]*(?:\r?\n)?$", line)
        if ending:
            pieces.append(line[:ending.start()])
            return "".join(pieces)
        pieces.append(line)
    raise ValueError(f"missing restricted proof boundary for {name}")


class ProposalTest(unittest.TestCase):
    def test_restricted_statement_boundaries(self):
        self.assertEqual(statement("theorem x : A\n    ∧ B := by\n  trivial\n", "x"), "A\n    ∧ B")
        for text in (
            "theorem x : A\ntheorem y : B := by\n  trivial\n",
            "theorem x : A\n  theorem y : B := by\n  trivial\n",
            "theorem x : A := by\n  trivial\ntheorem x : A := by\n  trivial\n",
            "theorem x : A\n#check A\n",
            "theorem x : A\n  private theorem y : B := by\n  trivial\n",
            "theorem x : A\n  @[simp] theorem y : B := by\n  trivial\n",
            "theorem x : A\n  example : B := by\n  trivial\n",
            "theorem x : A\n  -- fake := by\n",
            "theorem x : A\n  /- fake := by -/\n",
        ):
            with self.assertRaises(ValueError): statement(text, "x")

    def test_statements_and_unapplied_patch(self):
        self.assertEqual(hashlib.sha256(HELPER.read_bytes()).hexdigest(), HELPER_SHA256)
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
        self.assertIn("PanicBytes.panic_not_empty", text)
        lines = text.splitlines()
        removed = [line for line in lines if line.startswith("-") and not line.startswith("---")]
        added = [line for line in lines if line.startswith("+") and not line.startswith("+++")]
        self.assertEqual(removed, ["-  first | decide | rfl | omega"] * 3)
        self.assertEqual(added, ["+import Solidity.Backend.PrimitivePackets.PanicBytes"] +
                         ["+  exact Solidity.Backend.PrimitivePackets.PanicBytes." + name
                          for name in ("exact_panic_bytes", "panic_not_truncated", "panic_not_empty")])


if __name__ == "__main__":
    unittest.main()
