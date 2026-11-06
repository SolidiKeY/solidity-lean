import copy
import importlib.util
import json
import shutil
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("raw_census", ROOT / "scripts/h55/vectors-tables/raw_census.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)

class RawCensusTests(unittest.TestCase):
    def test_full_inventory(self):
        records = r.collect(ROOT)
        self.assertEqual(r.summary(records), json.loads(r.MANIFEST.read_text()))
        self.assertEqual(len(records), 102)
        self.assertEqual(sum(len(v["families"]) for v in records.values()), 8)
        self.assertEqual(sum(len(f["constructors"]) for v in records.values() for f in v["families"]), 20)
        self.assertEqual(sum(len(v["branches"]) for v in records.values()), 1839)
    def test_inventory_and_case_mutations(self):
        records = r.collect(ROOT); expected = r.summary(records)
        name = "RawSequence.lean"; original = (ROOT / r.AREA / name).read_bytes()
        for label, changed in [("missing", original.replace(b"  | nil :", b"  -- nil :", 1)),
                               ("extra", original.replace(b"  | nil :", b"  | extra : X\n  | nil :", 1)),
                               ("order", original.replace(b"  | nil :", b"  | renamed :", 1)),
                               ("schema", original.replace(b"inductive Supported", b"structure Supported", 1))]:
            with self.subTest(label=label):
                changed_records = copy.deepcopy(records)
                try: changed_records[name] = r.scan(name, changed)
                except ValueError: continue
                self.assertNotEqual(r.summary(changed_records), expected)
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); shutil.copytree(ROOT / r.AREA, root / r.AREA, ignore=shutil.ignore_patterns("*"))
            for path in (ROOT / r.AREA).glob("Raw*.lean"): shutil.copyfile(path, root / r.AREA / path.name)
            (root / r.AREA / name).unlink()
            with self.assertRaises(ValueError): r.collect(root)
            shutil.copyfile(ROOT / r.AREA / name, root / r.AREA / name)
            (root / r.AREA / "RawExtra.lean").write_text("")
            with self.assertRaises(ValueError): r.collect(root)

if __name__ == "__main__": unittest.main()
