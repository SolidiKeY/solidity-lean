import sys
import unittest
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/h55/vectors-tables"))
import table_proposals as p

class TableProposalTests(unittest.TestCase):
    def test_full_inventory_and_proof_preservation(self):
        for kind, count in [("word", 30), ("fixture", 45)]:
            with self.subTest(kind=kind):
                sources = p.inputs(kind)
                self.assertEqual(len(sources), count)
                for _, source in sources:
                    result = p.annotated(source, kind)
                    self.assertEqual(result.count(p.MARKERS[kind]), 1)
                    self.assertEqual(result.replace(p.MARKERS[kind], b"", 1), source)
                patch = p.proposal(kind)
                self.assertEqual(patch, p.proposal(kind))
                self.assertEqual(patch.count(b"--- a/"), count)
                self.assertEqual(patch.count(b"+++ b/"), count)
    def test_invalid_schema_and_existing_marker(self):
        for kind in ("word", "fixture"):
            with self.assertRaises(ValueError): p.annotated(b"theorem x : True := by trivial\n", kind)
            with self.assertRaises(ValueError): p.annotated(b"import X\n" + p.MARKERS[kind], kind)
        with self.assertRaises(ValueError): p.inputs("unknown")

if __name__ == "__main__": unittest.main()
