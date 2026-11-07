#!/usr/bin/env python3
"""Regression and mutation acceptance for the exact frozen source inventory."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import census as c


class FrozenCensus(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = c.census(c.BASE)

    def test_full_original_inventory(self):
        self.assertEqual(c.census(), self.data)
        self.assertEqual(c.seal(self.data), json.loads(c.DEST.read_text()))
        self.assertEqual(len(self.data["files"]), 46)
        self.assertEqual(sum(f["controls"] for f in self.data["files"]), 23)
        self.assertEqual(self.data["counts"], {"theorem":241, "def":115, "abbrev":2, "#guard_msgs":2, "#eval":2})
        self.assertEqual(self.data["controls_counts"]["theorem"], 179)

    def test_every_theorem_boundary_is_real(self):
        for row in self.data["declarations"]:
            if row["kind"] == "theorem":
                text = (c.ROOT/row["path"]).read_bytes().decode()
                begin = sum(len(line) for line in text.splitlines(keepends=True)[:row["line"]-1])
                remainder = text[begin+len(row["statement"]):].lstrip()
                self.assertTrue(remainder.startswith(":="), row["name"])
                self.assertNotIn(":= by", row["statement"], row["name"])

    def test_all_eight_type_let_conclusions(self):
        names = {"ConditionalContinuationCompiler", "ConditionalReturnCompiler", "ConditionalSequenceCompiler", "ConditionalSourceCompiler", "ForContinueCompiler", "WhileContinueCompiler", "ReturnPairCompiler", "ReturnTailCompiler"}
        rows = [r for r in self.data["declarations"] if r["name"].endswith(".correct") and r["path"].split("/")[-1].removesuffix(".lean") in names]
        self.assertEqual(len(rows), 8)
        for row in rows:
            self.assertIn("let choice : Bool :=", row["statement"])
            self.assertIn("Evm.StmtOut", row["statement"])
            self.assertTrue(row["statement"].endswith("machine"), row["name"])

    def test_equation_signatures(self):
        rows = c.records("example.lean", "namespace N\ndef observe : Bool → Nat\n  | true => let x := 1; x\n  | false => 0\nend N\n")
        self.assertEqual(rows[0]["statement"], "def observe : Bool → Nat")
        self.assertEqual(rows[0]["name"], "N.observe")

    def test_nested_comments_and_strings(self):
        text = '/- outer /- theorem fake : False := by nope -/ -/\nnamespace N\n-- theorem fake2 : False := nope\ndef text : String := "theorem fake3 := \\"hello\\""\ntheorem good : let x : Nat := 1; x = 1 := rfl\nend N\n'
        rows = c.records("example.lean", text)
        self.assertEqual([r["name"] for r in rows], ["N.text", "N.good"])
        self.assertEqual(rows[1]["statement"], "theorem good : let x : Nat := 1; x = 1")

    def test_statement_and_case_mutations_refused(self):
        for mutate in (lambda d: d["declarations"].pop(),
                       lambda d: d["declarations"][0].update(statement="weakened"),
                       lambda d: d["files"].pop()):
            data = copy.deepcopy(self.data)
            mutate(data)
            self.assertNotEqual(c.seal(data), c.seal(self.data))

    def test_newlines_and_nested_new_files_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            family = root/c.FAMILY
            family.mkdir(parents=True)
            p = family/"Test.lean"
            p.write_bytes(b"theorem good : True := True.intro\n")
            with patch.object(c, "ROOT", root):
                original = c.census()
                p.write_bytes(p.read_bytes().replace(b"\n", b"\r\n"))
                self.assertNotEqual(original, c.census())
                p.write_bytes(b"theorem good : True := True.intro\n")
                (family/"Nested").mkdir()
                (family/"Nested/New.lean").write_text("theorem extra : True := True.intro\n")
                self.assertEqual(len(c.census()["files"]), 2)
                self.assertNotEqual(original, c.census())

    def test_unhandled_declarations_fail_closed(self):
        with self.assertRaises(ValueError):
            c.records("bad.lean", "axiom unsafeShortcut : False\n")
        with self.assertRaises(ValueError):
            c.records("bad.lean", "/- unclosed")


if __name__ == "__main__":
    unittest.main(verbosity=2)
