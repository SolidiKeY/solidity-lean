"""Negative controls on an isolated miniature Git repository, never production."""
import importlib.util, pathlib, subprocess, tempfile, unittest, sys
sys.dont_write_bytecode=True
SOURCE=pathlib.Path(__file__).resolve().parents[4]/"scripts/h62/item6/migrate-language/census.py"
spec=importlib.util.spec_from_file_location("census",SOURCE)
census=importlib.util.module_from_spec(spec); spec.loader.exec_module(census)
class Controls(unittest.TestCase):
    def test_source_mutation_deletion_and_generated_root(self):
        with tempfile.TemporaryDirectory() as temp:
            root=pathlib.Path(temp)
            def git(*args): return subprocess.check_output(["git",*args],cwd=root,stderr=subprocess.DEVNULL).decode().strip()
            git("init"); p=root/"Solidity/Language/Fixture.lean"; p.parent.mkdir(parents=True)
            p.write_text("theorem frozen : True := True.intro\n")
            (root/"Solidity.lean").write_text("import Solidity.Language.Fixture\n")
            git("add","."); git("-c","user.name=Control","-c","user.email=control@example.invalid","commit","-m","fixture")
            old_root,old_base=census.root,census.base
            try:
                census.root=root; census.base=git("rev-parse","HEAD")
                d=census.census(); self.assertTrue(d["inventory_unchanged"])
                self.assertEqual(len(d["consumers"]),1); self.assertTrue(d["files"][0]["unchanged"])
                p.write_text("theorem frozen : False := by contradiction\n")
                self.assertFalse(census.census()["files"][0]["unchanged"])
                p.unlink(); self.assertFalse(census.census()["inventory_unchanged"])
                p.write_text("theorem frozen : True := True.intro\n")
                (p.parent/"Added.lean").write_text("def extra := 1\n")
                # Unpublished additions cannot be mistaken for the pinned inventory.
                with self.assertRaises(subprocess.CalledProcessError): census.census()
            finally: census.root,census.base=old_root,old_base
if __name__=="__main__": unittest.main()
