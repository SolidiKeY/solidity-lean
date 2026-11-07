import importlib.util
import pathlib
import unittest

spec = importlib.util.spec_from_file_location("panic_occurrence_windows", pathlib.Path(__file__).with_name("panic_occurrence_windows.py"))
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class OccurrenceWindowsTest(unittest.TestCase):
    def test_multiple_tokens_unmapped_and_ambiguous(self):
        rows = module.occurrences("x.lean", b"-- panicData panicData2 panicData\n")
        self.assertEqual([(r["line"], r["column"]) for r in rows], [(1, 4), (1, 25)])
        # Raw word-boundary regex also matches an apostrophe identifier suffix.
        self.assertEqual(len(module.occurrences("x.lean", b"panicData'")), 1)
        w = {"file": "x.lean", "source_sha256": rows[0]["source_sha256"], "line": 1, "end_line": 1, "kind": "theorem", "name": "x", "ledger": "l", "window_sha256": "h"}
        self.assertEqual(len(module.link(rows, [w])), 2)
        self.assertIsNone(module.link(rows, [])[0]["window"])
        with self.assertRaises(ValueError): module.link(rows, [w, dict(w)])
        with self.assertRaises(ValueError): module.link(rows, [dict(w, source_sha256="wrong")])

if __name__ == "__main__": unittest.main()
