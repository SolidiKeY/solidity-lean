#!/usr/bin/env python3
"""Review-only proposal rejects upstream drift before emitting a patch."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import propose_migration as proposal

class ProposalTest(unittest.TestCase):
    def test_drift_and_existing_destination_fail_before_output(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            shared = Path("tests/h62/item1/infer-helpers/Shared.lean")
            for path in (Path(proposal.SOURCE), Path(proposal.STATIC), shared):
                target = root / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text((proposal.ROOT / path).read_text(encoding="utf-8"), encoding="utf-8")
            with patch.object(proposal, "ROOT", root):
                with contextlib.redirect_stdout(io.StringIO()) as output:
                    proposal.main()
                self.assertIn("diff --git a/" + proposal.NEW, output.getvalue())
                for path, replacements in proposal.REPLACEMENTS.items():
                    target = root / path
                    original = target.read_text(encoding="utf-8")
                    for old, _ in replacements:
                        with self.subTest(path=path, declaration=old.splitlines()[0]):
                            self.assertEqual(original.count(old), 1)
                            target.write_text(original.replace(old, "def changed : Bool := false", 1), encoding="utf-8")
                            with contextlib.redirect_stdout(io.StringIO()) as out:
                                with self.assertRaises(ValueError): proposal.main()
                            self.assertEqual(out.getvalue(), "")
                            target.write_text(original.replace(old, "/-\n" + old + "\n-/", 1), encoding="utf-8")
                            with contextlib.redirect_stdout(io.StringIO()) as out:
                                with self.assertRaises(ValueError): proposal.main()
                            self.assertEqual(out.getvalue(), "")
                            target.write_text(original, encoding="utf-8")
                target = root / proposal.SOURCE
                original = target.read_text(encoding="utf-8")
                anchor = "import Solidity.Source.Typing\n"
                self.assertEqual(original.count(anchor), 1)
                target.write_text(original.replace(anchor, "/-\n" + anchor + "-/\n", 1), encoding="utf-8")
                with contextlib.redirect_stdout(io.StringIO()) as out:
                    with self.assertRaises(ValueError): proposal.main()
                self.assertEqual(out.getvalue(), "")
                target.write_text(original, encoding="utf-8")
                target = root / proposal.NEW
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text("already owned", encoding="utf-8")
                with contextlib.redirect_stdout(io.StringIO()) as out:
                    with self.assertRaises(ValueError): proposal.main()
                self.assertEqual(out.getvalue(), "")

if __name__ == "__main__":
    unittest.main()
