import importlib.util
import pathlib
import sys
import unittest

DIRECTORY = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(DIRECTORY))
spec = importlib.util.spec_from_file_location("attributed_header_scan", DIRECTORY / "attributed_header_scan.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class AttributeScanTest(unittest.TestCase):
    def test_nested_multiline_and_masking(self):
        source = ("@[simp] theorem foo : True := by trivial\n"
                  "  @[inline] private def bar := 0\n"
                  "@[simp]\ntheorem separate := 0\n"
                  "@[foo [bar]] @[x \"quoted ] value\"]\nprotected lemma nested : True := by trivial\n"
                  "/- outer /- @[simp] theorem fake : True := by trivial -/ -/\n"
                  "\"@[simp] theorem fake2 : True := by trivial\"\n")
        masked = module.mask_comments_and_strings(source, mask_attributes=False)
        self.assertEqual(len(masked), len(source))
        self.assertEqual([i for i, c in enumerate(masked) if c == "\n"],
                         [i for i, c in enumerate(source) if c == "\n"])
        self.assertEqual(module.candidates(source), [(1, 9, None, "theorem", "foo"),
            (2, 21, "private", "def", "bar"), (4, 1, None, "theorem", "separate"),
            (6, 11, "protected", "lemma", "nested")])
        self.assertEqual(module.candidates("@[simp]\nprivate\ntheorem shifted : True := by trivial\n"),
                         [(3, 1, "private", "theorem", "shifted")])
        census = [{"file": "x.lean", "line": 3, "kind": "theorem", "name": "shifted"}]
        self.assertTrue(module.census_covers(census, "x.lean", 3, "theorem", "shifted"))
        self.assertFalse(module.census_covers(census, "x.lean", 2, "theorem", "shifted"))
        with self.assertRaisesRegex(ValueError, "unterminated attribute"):
            module.candidates("@[broken [nested] theorem bad : True := by trivial")

if __name__ == "__main__": unittest.main()
