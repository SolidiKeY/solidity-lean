import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from census import module_to_path
import verify_census as verification

class ImportPathTests(unittest.TestCase):
    def test_quoted_hyphen_component(self):
        self.assertEqual(module_to_path("tests.h62.item2.«audit-theories».CoreTotality"),
          Path("tests/h62/item2/audit-theories/CoreTotality.lean"))
    def test_quoted_dot_is_one_component(self):
        self.assertEqual(module_to_path("One.«Two.Three».Four"),Path("One/Two.Three/Four.lean"))
    def test_normal_name_is_unchanged(self):
        self.assertEqual(module_to_path("Solidity.Evm.Compiler"),Path("Solidity/Evm/Compiler.lean"))
    def test_malformed_name_fails_closed(self):
        for name in ("One..Two","One.«Two","One.«../Two»"):
            with self.assertRaises(ValueError): module_to_path(name)
    def test_quoted_dependency_changes_parent_fingerprint(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);child=root/"tests/my-lane/B.lean";child.parent.mkdir(parents=True)
            parent=root/"A.lean";parent.write_text("import tests.«my-lane».B\n")
            child.write_text("def marker := 0\n")
            with patch.object(verification,"ROOT",root),patch.object(verification,"VERSION","fixture"):
                verification.FINGERPRINTS.clear();before=verification.fingerprint("A.lean")
                child.write_text("def marker := 1\n")
                verification.FINGERPRINTS.clear();after=verification.fingerprint("A.lean")
                self.assertNotEqual(before,after)
                verification.FINGERPRINTS.clear()

if __name__=="__main__":unittest.main()
