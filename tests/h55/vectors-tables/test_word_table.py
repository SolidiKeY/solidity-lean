import copy
import importlib.util
import json
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("word_table", ROOT / "scripts/h55/vectors-tables/word_table.py")
w = importlib.util.module_from_spec(spec); spec.loader.exec_module(w)

class WordTableTests(unittest.TestCase):
    def test_full_inventory_and_reproduction(self):
        records = w.collect(ROOT); original = w.render(records)
        self.assertEqual(sum(len(p["rows"]) for p in records.values()), 439)
        self.assertEqual(w.manifest(records), json.loads(w.MANIFEST.read_text()))
        for name in w.NAMES: self.assertEqual(original[name], (ROOT / w.AREA / name).read_bytes())
        self.assertEqual(w.render(copy.deepcopy(records)), original)
    def test_missing_extra_order_schema_and_proof(self):
        original = w.collect(ROOT); expected = w.manifest(original)
        changes = {}
        x = copy.deepcopy(original); x[w.NAMES[0]]["rows"].pop(0); changes["missing"] = x
        x = copy.deepcopy(original); x[w.NAMES[0]]["rows"].append(copy.deepcopy(x[w.NAMES[0]]["rows"][0])); changes["extra"] = x
        x = copy.deepcopy(original); x[w.NAMES[0]]["rows"][:2] = reversed(x[w.NAMES[0]]["rows"][:2]); changes["order"] = x
        x = copy.deepcopy(original); x[w.NAMES[0]]["rows"][0]["unexpected"] = 1; changes["schema"] = x
        x = copy.deepcopy(original); x[w.NAMES[0]]["rows"][0]["text"] += "-- changed proof\n"; changes["proof"] = x
        for label, value in changes.items():
            with self.subTest(label=label):
                try: actual = w.manifest(value)
                except ValueError: continue
                self.assertNotEqual(actual, expected)

if __name__ == "__main__": unittest.main()
