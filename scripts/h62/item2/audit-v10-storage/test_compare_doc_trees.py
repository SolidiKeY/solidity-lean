#!/usr/bin/env python3
import io, subprocess, tarfile, tempfile, unittest
from pathlib import Path
import compare_doc_trees as m
ROOT=Path(__file__).resolve().parents[4]
class ComparisonTest(unittest.TestCase):
    def test_only_root_selection_changes(self):
        original=(ROOT/m.CHECKER).read_bytes()
        changed=m.runtime_checker(original)
        self.assertEqual(changed.replace(b'cd "$DOC_COMPARE_ROOT"',b'cd "$(dirname "$0")/.."'),original)
        for bad in [b"echo no root",original+original]:
            with self.assertRaises(ValueError):m.runtime_checker(bad)
    def test_unsafe_archives_rejected(self):
        for name,kind in [("../escape",tarfile.REGTYPE),("link",tarfile.SYMTYPE)]:
            with tempfile.TemporaryDirectory() as temp:
                raw=io.BytesIO()
                with tarfile.open(fileobj=raw,mode="w") as tree:
                    item=tarfile.TarInfo(name);item.type=kind;item.linkname="/outside";tree.addfile(item)
                with self.assertRaises(ValueError):m.extract_exact(raw.getvalue(),Path(temp))
    def test_formatted_findings_retained(self):
        a="ambiguous: sample cites target (2 files share that name)\n"
        b=a.replace("(2 files","(3 files")
        self.assertEqual(m.compare(a,a)["status"],"pass")
        self.assertEqual(m.compare(b,a)["status"],"fail")
        self.assertEqual(m.compare(b,a)["new_findings"],[b.strip()])
    def test_incomplete_checker_cannot_pass(self):
        for status,text in [(2,""),(1,""),(0,""),(0,"missing: broken\n"),
                            (1,"missing: broken\nFAIL: 2 reference(s) name a file that does not exist.\n")]:
            with self.subTest(status=status,text=text),self.assertRaises(ValueError):m.validate_completion(status,text)
        m.validate_completion(0,"OK: every backticked *.lean reference resolves.\n")
        m.validate_completion(1,"missing: broken\nFAIL: 1 reference(s) name a file that does not exist.\n")
    def test_committed_tree_ignores_untracked_rescue(self):
        with tempfile.TemporaryDirectory() as temp:
            outer=Path(temp);repo=outer/"repo";repo.mkdir();out=outer/"evidence";out.mkdir()
            subprocess.run(["git","init","-q",str(repo)],check=True)
            (repo/"Solidity").mkdir();(repo/"Solidity/A.lean").write_text("example : True := True.intro\n")
            tick=chr(96);(repo/"notes.md").write_text(tick+"Missing.lean"+tick+"\n")
            subprocess.run(["git","add","--force","--all"],cwd=repo,check=True)
            subprocess.run(["git","-c","user.name=fixture","-c","user.email=fixture@example.invalid","commit","-qm","baseline"],cwd=repo,check=True)
            base=subprocess.check_output(["git","rev-parse","HEAD"],cwd=repo,text=True).strip()
            (repo/"Missing.lean").write_text("example : True := True.intro\n")
            (repo/"notes.md").write_text(tick+"Solidity/A.lean"+tick+"\n")
            subprocess.run(["git","add","notes.md"],cwd=repo,check=True)
            subprocess.run(["git","-c","user.name=fixture","-c","user.email=fixture@example.invalid","commit","-qm","current"],cwd=repo,check=True)
            current=subprocess.check_output(["git","rev-parse","HEAD"],cwd=repo,text=True).strip()
            checker=out/"checker.sh";checker.write_bytes(m.runtime_checker((ROOT/m.CHECKER).read_bytes()))
            old,oldlog=m.check_tree(repo,base,checker,out,"baseline")
            new,newlog=m.check_tree(repo,current,checker,out,"current")
            self.assertEqual((old["exit"],old["missing"]),(1,1))
            self.assertEqual((new["exit"],new["missing"]),(0,0))
            self.assertEqual(m.compare(newlog,oldlog)["status"],"pass")
            self.assertEqual(len(m.compare(newlog,oldlog)["removed_findings"]),1)
            failed=out/"failed-checker.sh";failed.write_bytes(b"exit 2\n")
            with self.assertRaises(ValueError):m.check_tree(repo,current,failed,out,"failed")
            self.assertTrue((out/"failed.log").is_file())
            self.assertTrue((out/"failed-infrastructure-failure.json").is_file())
if __name__=="__main__":unittest.main()
