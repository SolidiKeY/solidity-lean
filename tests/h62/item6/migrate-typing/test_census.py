"""Negative controls for frozen source census (no Lean invocation)."""
import importlib.util, pathlib, tempfile, unittest
ROOT=pathlib.Path(__file__).resolve().parents[4]
SPEC=importlib.util.spec_from_file_location("census",ROOT/"scripts/h62/item6/migrate-typing/census.py")
c=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(c)
class Controls(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup); self.root=pathlib.Path(self.tmp.name)
        self.area=self.root/"Solidity/Typing";self.area.mkdir(parents=True)
        for name in c.NAMES:(self.area/(name+".lean")).write_text("theorem witness : True := True.intro\n")
    def test_reproducible(self): self.assertEqual(c.census(self.root),c.census(self.root))
    def test_missing_assigned(self):
        (self.area/"Fits.lean").unlink()
        with self.assertRaisesRegex(ValueError,"census mismatch"): c.census(self.root)
    def test_missing_dependency(self):
        (self.area/"Fits.lean").write_text("import Solidity.Missing\n")
        with self.assertRaisesRegex(ValueError,"missing local import"): c.census(self.root)
    def test_cycle(self):
        (self.area/"Fits.lean").write_text("import Solidity.Typing.Tight\n")
        (self.area/"Tight.lean").write_text("import Solidity.Typing.Fits\n")
        with self.assertRaisesRegex(ValueError,"import cycle"): c.census(self.root)
    def test_changed_premise(self):
        frozen=c.census(self.root)
        (self.area/"Fits.lean").write_text("theorem witness (h : False) : True := False.elim h\n")
        with self.assertRaisesRegex(ValueError,"frozen census mismatch"): c.verify(self.root,frozen)
    def test_comment_import_not_a_dependency(self):
        p=self.area/"Fits.lean";p.write_text('/- outer /- nested -/\nimport Solidity.Missing\n-/\n-- import Solidity.Missing\ndef s := "import Solidity.Missing"\n@[simp] theorem witness : True := True.intro\n')
        snapshot=c.census(self.root);file=next(f for f in snapshot["files"] if f["module"].endswith("Fits"))
        self.assertEqual(file["imports"],[]);self.assertIn("witness",[d["name"] for d in file["declaration_sites"]])
if __name__=="__main__": unittest.main()
