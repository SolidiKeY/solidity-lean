"""Negative controls for coverage bookkeeping, not proofs of Lean statements."""
import importlib.util, pathlib, subprocess, sys, tempfile, unittest
p=pathlib.Path(__file__).resolve().parents[4]/"scripts/h62/item6/migrate-bridge/census.py"
spec=importlib.util.spec_from_file_location("census",p); census=importlib.util.module_from_spec(spec); spec.loader.exec_module(census)
class CensusTests(unittest.TestCase):
    def setUp(self): self.a=[{"path":"Bridge/A.lean","bytes":1,"sha256":"a"}]
    def test_identity(self): self.assertEqual(census.compare(self.a,self.a),{"removed":[],"added":[],"changed":[]})
    def test_missing_file(self): self.assertEqual(census.compare(self.a,[])["removed"],["Bridge/A.lean"])
    def test_changed_proof_or_statement(self):
        b=[dict(self.a[0],sha256="b")]; self.assertEqual(census.compare(self.a,b)["changed"],["Bridge/A.lean"])
    def test_added_file(self): self.assertEqual(census.compare([],self.a)["added"],["Bridge/A.lean"])
class SnapshotTests(unittest.TestCase):
    def test_staged_addition_and_worktree_deletion(self):
        with tempfile.TemporaryDirectory() as d:
            root=pathlib.Path(d); census.git(root,"init","-q"); (root/"Bridge").mkdir()
            a=root/"Bridge/A.lean"; a.write_text("theorem a : True := True.intro\n")
            census.git(root,"add","Bridge/A.lean")
            census.git(root,"-c","user.name=Test","-c","user.email=test@invalid","commit","-qm","fixture")
            before=census.snapshot(root,"HEAD")
            cli=[sys.executable,str(p),"--root",str(root),"--baseline","HEAD","--require-unchanged"]
            self.assertEqual(subprocess.run(cli,stdout=subprocess.DEVNULL).returncode,0)
            (root/"Bridge/B.lean").write_text("theorem b : True := True.intro\n")
            census.git(root,"add","Bridge/B.lean")
            self.assertEqual(census.compare(before,census.snapshot(root))["added"],["Bridge/B.lean"])
            self.assertEqual(subprocess.run(cli,stdout=subprocess.DEVNULL).returncode,1)
            a.unlink()
            self.assertEqual(census.compare(before,census.snapshot(root))["removed"],["Bridge/A.lean"])
            self.assertEqual(subprocess.run(cli,stdout=subprocess.DEVNULL).returncode,1)
if __name__=="__main__": unittest.main()
