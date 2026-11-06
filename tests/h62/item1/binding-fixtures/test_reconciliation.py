#!/usr/bin/env python3
"""Deterministic census controls; lexical evidence, not Lean proofs."""
import importlib.util
import json
import pathlib
import subprocess
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[4]
SCRIPT = ROOT / "scripts/h62/item1/binding-fixtures/reconcile.py"
SPEC = importlib.util.spec_from_file_location("reconcile", SCRIPT)
reconcile = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(reconcile)


class ReconciliationControls(unittest.TestCase):
    def test_repository_inventory(self):
        data = json.loads(subprocess.check_output([sys.executable, str(SCRIPT)], cwd=ROOT))
        leased, relations = data["leased_controls"], data["relation_controls"]
        self.assertEqual(len(leased), 18)
        self.assertEqual(sum(len(row["declarations"]) for row in leased), 105)
        self.assertEqual(len(relations), 17)
        census = json.loads(subprocess.check_output([sys.executable,
            str(ROOT / "scripts/h62/item1/binding-fixtures/census.py")], cwd=ROOT))
        self.assertEqual({row["path"] for row in relations},
                         {row["path"] for row in census["definitions"]})
        self.assertTrue(all(not row["bindingrel_lines"] and not row["opposite_set_reachable"]
                            for row in leased))
        self.assertTrue(all(row["bindingrel_lines"] and not row["opposite_set_reachable"]
                            for row in relations))
        aliases = [row for row in relations if "/G19/" in row["path"]]
        self.assertEqual(len(aliases), 7)
        for row in aliases:
            self.assertIn("abbrev BindingRel := P12Controls.BindingRel",
                          (ROOT / row["path"]).read_text())

    def test_closure_cycle_missing_and_positive_path(self):
        with tempfile.TemporaryDirectory() as directory:
            fixture_root = pathlib.Path(directory)
            package = fixture_root / "Probe"
            package.mkdir()
            a, b, unrelated = (package / (name + ".lean") for name in ("A", "B", "C"))
            a.write_text("import Probe.B\nimport Probe.Missing\n")
            b.write_text("import Probe.A\n")
            unrelated.write_text("-- no imports\n")
            saved_root = reconcile.ROOT
            reconcile.ROOT = fixture_root
            try:
                self.assertEqual(reconcile.closure(a), {a, b})
                self.assertNotIn(unrelated, reconcile.closure(a))
            finally:
                reconcile.ROOT = saved_root

    def test_quoted_declaration_is_explicit_unknown(self):
        with tempfile.TemporaryDirectory() as directory:
            root=pathlib.Path(directory);source=root/'Quoted.lean'
            source.write_text('def «BindingRel» := 1\n')
            saved=reconcile.ROOT;reconcile.ROOT=root
            try:
                row=reconcile.record(source)
                self.assertEqual(row['declarations'],[])
                self.assertEqual(row['unknown_quoted_identifiers'][0]['text'],'«BindingRel»')
            finally:reconcile.ROOT=saved

    def test_lexical_nonclaims(self):
        # Commented imports must not create source dependencies.
        with tempfile.TemporaryDirectory() as directory:
            fixture_root = pathlib.Path(directory)
            package = fixture_root / "Probe"
            package.mkdir()
            a, b = package / "A.lean", package / "B.lean"
            a.write_text("/-\nimport Probe.B\n-/\n")
            b.write_text("-- comment-only reference\n")
            saved_root = reconcile.ROOT
            reconcile.ROOT = fixture_root
            try:
                self.assertNotIn(b, reconcile.closure(a))
            finally:
                reconcile.ROOT = saved_root


if __name__ == "__main__":
    unittest.main(verbosity=2)
