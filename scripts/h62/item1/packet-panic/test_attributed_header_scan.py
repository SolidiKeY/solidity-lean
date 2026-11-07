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
    def test_narrow_candidates(self):
        source = "@[simp] theorem foo : True := by trivial\n  @[inline] private def bar := 0\n@[simp]\ntheorem separate := 0\n"
        self.assertEqual(module.candidates(source), [(1, None, "theorem", "foo"), (2, "private", "def", "bar")])
        # This deliberately narrow raw scan is not a parser or a comment masker.
        self.assertEqual(module.candidates("/-\n@[simp] theorem fake : True := by trivial\n-/\n")[0][3], "fake")

if __name__ == "__main__": unittest.main()
