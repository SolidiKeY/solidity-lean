#!/usr/bin/env python3
"""Real Lean integration controls; run with python3 -I after building KeySort.

Fixtures are artificial checker probes, never claims about Solidity coverage.
No Lean server or source-tree modifications.
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("check-feature-citations.py")
spec = importlib.util.spec_from_file_location("citations", SCRIPT)
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


def fixture():
    return {"schemaVersion": 2, "features": [{"id": "synthetic", "current": "present", "theorems": [
        {"name": "Solidity.KeySort.le_refl", "module": "Solidity.KeySort", "class": "a", "premises": [], "direction": "model"}
    ]}]}


class Controls(unittest.TestCase):
    def run_check(self, data):
        with tempfile.TemporaryDirectory(prefix="citation-control-") as tmp:
            p = Path(tmp) / "fixture.json"
            p.write_text(json.dumps(data))
            return subprocess.run([sys.executable, "-I", str(SCRIPT), "--manifest", str(p)],
                                  text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def test_positive_and_deterministic(self):
        a, b = self.run_check(fixture()), self.run_check(fixture())
        self.assertEqual(a.returncode, 0, a.stderr)
        self.assertEqual(b.returncode, 0, b.stderr)
        self.assertEqual(a.stdout, b.stdout)
        self.assertEqual(json.loads(a.stdout)["rowsWithCitations"], 1)

    def test_standard_library_module_resolves(self):
        d = fixture(); d["features"][0]["theorems"][0].update(name="Nat.add_comm", module="Init.Data.Nat.Basic")
        r = self.run_check(d); self.assertEqual(r.returncode, 0, r.stderr)

    def test_optional_gap_schema_and_count(self):
        d = fixture(); d["features"][0]["modelToSolcGap"] = "Universal agreement remains open"
        _, summary = checker.validate(d)
        self.assertEqual(summary["modelToSolcGapRows"], 1)
        for bad in (None, 0, [], " "):
            d["features"][0]["modelToSolcGap"] = bad
            with self.assertRaisesRegex(ValueError, "modelToSolcGap"):
                checker.validate(d)

    def test_missing_name(self):
        d = fixture(); del d["features"][0]["theorems"][0]["name"]
        r = self.run_check(d); self.assertNotEqual(r.returncode, 0); self.assertIn("invalid citation fields", r.stderr)

    def test_misspelled_name(self):
        d = fixture(); d["features"][0]["theorems"][0]["name"] += "_bogus"
        r = self.run_check(d); self.assertNotEqual(r.returncode, 0); self.assertIn("missing declaration", r.stderr)

    def test_present_without_citation(self):
        d = fixture(); d["features"][0]["theorems"] = []
        r = self.run_check(d); self.assertNotEqual(r.returncode, 0); self.assertIn("non-d citation", r.stderr)

    def test_present_only_d(self):
        d = fixture(); d["features"][0]["theorems"][0]["class"] = "d"
        r = self.run_check(d); self.assertNotEqual(r.returncode, 0); self.assertIn("non-d citation", r.stderr)

    def test_missing_module(self):
        d = fixture(); d["features"][0]["theorems"][0]["module"] += "Bogus"
        r = self.run_check(d); self.assertNotEqual(r.returncode, 0); self.assertIn("Lean resolution failed", r.stderr)

    def test_wrong_module_origin(self):
        d = fixture(); d["features"][0]["theorems"][0].update(name="Nat.add_comm")
        r = self.run_check(d); self.assertNotEqual(r.returncode, 0); self.assertIn("wrong module origin", r.stderr)

    def test_definition_cannot_claim_a(self):
        d = fixture(); d["features"][0]["theorems"][0]["name"] = "Solidity.KeySort.le"
        r = self.run_check(d); self.assertNotEqual(r.returncode, 0); self.assertIn("requires a theorem", r.stderr)

    def test_b_requires_premises(self):
        d = fixture(); d["features"][0]["theorems"][0]["class"] = "b"
        r = self.run_check(d); self.assertNotEqual(r.returncode, 0); self.assertIn("requires named premises", r.stderr)

    def test_injection_rejected(self):
        d = fixture(); d["features"][0]["theorems"][0]["name"] += '\n#eval 0'
        r = self.run_check(d); self.assertNotEqual(r.returncode, 0); self.assertIn("fully qualified name", r.stderr)

    def test_summary_counts_rows_once_per_cell(self):
        d = fixture(); d["features"][0]["theorems"].append(dict(d["features"][0]["theorems"][0], name="Solidity.KeySort.le_any"))
        _, s = checker.validate(d)
        self.assertEqual(s["rowCells"], [{"current": "present", "class": "a", "direction": "model", "rows": 1}])

    def test_summary_mixed_directions_overlap(self):
        d = fixture()
        d["features"][0]["theorems"].append(dict(d["features"][0]["theorems"][0], direction="model-to-solc"))
        _, s = checker.validate(d)
        self.assertEqual(s["rows"], 1)
        self.assertEqual(s["modelOnlyRows"], 0)
        self.assertEqual(s["modelToSolcRows"], 1)
        self.assertEqual(sum(c["rows"] for c in s["rowCells"]), 2)


if __name__ == "__main__":
    unittest.main(verbosity=2)
