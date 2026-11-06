import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
spec = importlib.util.spec_from_file_location("census", ROOT/"scripts/h62/item6/migrate-backend/census.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class LexicalControls(unittest.TestCase):
    def test_comments_strings_and_nested_comments(self):
        text = 'import Solidity.Backend.Control\n/- import Fake.A /- nested -/ -/\n-- import Fake.B\n#eval "import Fake.C"\nimport Lean Std\n'
        self.assertEqual(module.imports(text), ["Solidity.Backend.Control", "Lean", "Std"])
        clean = module.mask(text)
        self.assertEqual(len(clean), len(text))
        self.assertEqual(clean.count("\n"), text.count("\n"))

    def test_comment_markers_inside_strings(self):
        text = '#eval "-- /- \\" fake"\nimport Solidity.KeySort -- trailing\n'
        self.assertEqual(module.imports(text), ["Solidity.KeySort"])

    def test_toolchain_prefix_does_not_hide_vendor_dependencies(self):
        for name in ("Init","Init.Data.Nat","Lean","Lean.Elab","Std","Std.Data.HashMap"):
            self.assertTrue(module.is_toolchain_module(name),name)
        for name in ("LeanTeX","StandardFake","Initializer"):
            self.assertFalse(module.is_toolchain_module(name),name)

    def test_multiple_and_qualified_imports(self):
        self.assertEqual(module.imports("public import Lean Std\nmeta import Init\n"), ["Lean", "Std", "Init"])

if __name__ == "__main__": unittest.main()
