"""Scanner acceptance and non-vacuity controls; no Lean claims."""
import importlib.util,json,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
spec=importlib.util.spec_from_file_location("census",ROOT/"scripts/h62/item6/migrate-evm/census.py")
c=importlib.util.module_from_spec(spec); spec.loader.exec_module(c)

class CensusTests(unittest.TestCase):
    def test_comments_strings_and_characters(self):
        text = "import A\n/- import Fake /- nested -/ -/\n-- import Nope\ndef text := \"import Other\"\ndef quote : Char := '\"'\n"
        self.assertEqual(c.imports(text),["A"])
        self.assertEqual(c.mask(text).count("\n"),text.count("\n"))
    def test_import_whitespace(self):
        self.assertEqual(c.imports("import\n Solidity.KeySort\npublic meta import Lean A.B\n"),["Solidity.KeySort","Lean","A.B"])
    def test_malformed_lexical_input(self):
        for text in ('/- unclosed','def x := "unclosed'):
            with self.assertRaises(ValueError): c.mask(text)
    def test_freeze_changes_and_dependency_negative_controls(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); (root/"Solidity/Evm").mkdir(parents=True)
            source=root/"Solidity/Evm/A.lean"; dep=root/"Solidity/B.lean"
            source.write_text("import Solidity.B\ntheorem witness : True := True.intro\n")
            dep.write_text("def value : Nat := 1\n")
            old=c.census(root); self.assertEqual(old["order"],["Solidity.B","Solidity.Evm.A"])
            self.assertEqual(old["external_edges"],[["Solidity.Evm.A","Solidity.B"]])
            self.assertEqual(old,c.census(root))
            source.write_text(source.read_text().replace("True := True.intro","False := by contradiction"))
            self.assertNotEqual(old["modules"]["Solidity.Evm.A"]["sha256"],c.census(root)["modules"]["Solidity.Evm.A"]["sha256"])
            dep.unlink()
            with self.assertRaisesRegex(ValueError,"missing local import"): c.census(root)
            dep.write_text("import Solidity.Evm.A\n")
            with self.assertRaisesRegex(ValueError,"import cycle"): c.census(root)
    def test_all_frozen_sources(self):
        data=c.census(ROOT)
        self.assertEqual(data["assigned_count"],277)
        self.assertEqual(data["closure_count"],386)
        self.assertEqual(data["order"][0],"Solidity.KeySort")
        self.assertEqual(len(data["external_edges"]),39)
        self.assertEqual(sum(v["sorry_tokens"]+v["axiom_tokens"] for v in data["modules"].values() if v["assigned"]),0)

if __name__=="__main__": unittest.main()
