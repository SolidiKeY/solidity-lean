#!/usr/bin/env python3
import pathlib, runpy, unittest
api = runpy.run_path(str(pathlib.Path(__file__).with_name("inventory.py")))
class ImportGraphTests(unittest.TestCase):
    def test_comments_and_multiple_imports(self):
        self.assertEqual(api["imports"]("/- import False /- nested -/ -/\nimport A B -- import False\n"), {"A", "B"})
    def test_cycle(self):
        self.assertEqual(api["closure"]({"A": {"B"}, "B": {"A", "C"}}, ["A"]), {"A", "B", "C"})
    def test_missing_boundary(self):
        self.assertEqual(api["closure"]({"A": {"External"}}, ["A"]), {"A", "External"})
if __name__ == "__main__": unittest.main()
