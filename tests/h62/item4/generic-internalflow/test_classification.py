"""External conservation/refusal acceptance, not semantic Lean tests."""
import copy
import importlib.util
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[4]
TOOLS = ROOT / "scripts/h62/item4/generic-internalflow"
sys.path.insert(0, str(TOOLS))
import census
import classify

class Conservation(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.inventory = census.census(classify.BASE)
        cls.mapping = classify.parse_map(classify.MAP.read_text())
        cls.result = classify.classify(cls.inventory, cls.mapping)
        cls.cases = {(Path(f["path"]).name, d["name"]): d for f in cls.result["files"] for d in f["declarations"]}

    def test_every_original_declaration_and_command_retained(self):
        expected = {f["path"]: f for f in self.inventory["files"] if f["controls_file"]}
        self.assertEqual(len(expected), 57)
        self.assertEqual(len(self.result["files"]), 57)
        self.assertEqual(self.result["summary"]["semantic_cases"], 577)
        self.assertEqual(self.result["summary"]["fixture_declarations"], 335)
        for file in self.result["files"]:
            original = expected[file["path"]]
            self.assertEqual(file["source_sha256"], original["source_sha256"])
            self.assertEqual(file["commands"], original["commands"])
            self.assertEqual(len(file["declarations"]), len(original["declarations"]))
            for before, after in zip(original["declarations"], file["declarations"]):
                for key in ("line", "kind", "name", "header", "header_sha256", "slice_sha256"):
                    self.assertEqual(before[key], after[key])
                self.assertEqual(set(after["audit9"]), {"status", "pair", "decision"})
                self.assertIn("status", after["audit11"])
                self.assertIn("status", after["audit16"])

    def test_missing_case_refused(self):
        m = copy.deepcopy(self.mapping)
        del m["RuntimeFrameCodeAuthenticationControls.lean"]["construction"]
        with self.assertRaisesRegex(ValueError, "missing/extra cases"):
            classify.classify(self.inventory, m)

    def test_extra_case_refused(self):
        m = copy.deepcopy(self.mapping)
        m["RuntimeFrameCodeAuthenticationControls.lean"]["invented_case"] = ["eq"]
        with self.assertRaisesRegex(ValueError, "missing/extra cases"):
            classify.classify(self.inventory, m)

    def test_missing_file_refused(self):
        m = copy.deepcopy(self.mapping)
        del m["RuntimeFrameCodeAuthenticationControls.lean"]
        with self.assertRaisesRegex(ValueError, "file inventory"):
            classify.classify(self.inventory, m)

    def test_duplicate_case_and_unknown_facet_refused(self):
        with self.assertRaisesRegex(ValueError, "duplicate case"):
            classify.parse_map("@X\neq: same\nobs: same\n")
        with self.assertRaisesRegex(ValueError, "unknown/duplicate facets"):
            classify.parse_map("@X\nunknown: same\n")

    def facets(self, suffix, name):
        return set(self.cases[("RuntimeFrame"+suffix+"Controls.lean", name)]["facets"])

    def test_mixed_halts_and_success_are_not_collapsed(self):
        self.assertTrue({"ss", "sx", "sn", "obs", "eq"} <= self.facets("V3AllocatingCallCoherence", "actual"))
        for suffix, name in [("V3RecursiveScope", "exhausted_boundary"), ("V3ScalarSourceCompiler", "exhausted_boundary"), ("V3EffectfulSourceSelection", "exhausted_boundary"), ("V3OrderedEffectfulStorage", "shallow_boundary")]:
            self.assertEqual(self.facets(suffix, name), {"sx", "ts"})
        self.assertEqual(self.facets("V3AllocatingSourceViews", "actual_exhaustion"), {"sx", "sn"})

    def test_refusal_is_not_revert_or_negative_entry(self):
        self.assertEqual(self.facets("V3AllocatingSourceViews", "revert_refused"), {"vref"})
        self.assertEqual(self.facets("V3CallProducer", "negative_entry"), {"entry"})
        self.assertEqual(self.facets("V3DisjointScalar", "bad_selected"), {"compile"})
        self.assertEqual(self.facets("V3ScopedScalar", "panic_preserved"), {"sp"})
        self.assertEqual(self.facets("V3ScopedScalar", "payload_preserved"), {"sd"})

    def test_counterexamples_keep_positive_conjuncts(self):
        self.assertEqual(self.facets("V3AllocatingOuterZero", "actual"), {"ss", "return", "aneg"})
        self.assertEqual(self.facets("V3TypedHeapExtensionality", "old_keeps_insufficient"), {"pres", "neq", "defaultsneg"})
        self.assertEqual(self.facets("V3DistinctParent", "wrong_active"), {"conditional", "neq"})

    def test_audit11_candidates_are_not_plain_href_mentions(self):
        candidates = [d for f in self.result["files"] for d in f["declarations"] if d["audit11"]["status"] == "candidate_typed_absence_instance"]
        self.assertEqual({d["name"] for d in candidates}, {"no_ref", "no_struct"})
        self.assertEqual(len(candidates), 2)

if __name__ == "__main__":
    unittest.main()
