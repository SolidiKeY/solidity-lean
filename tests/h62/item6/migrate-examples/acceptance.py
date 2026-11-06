#!/usr/bin/env python3
"""Negative controls for lexical boundaries and owned-process cleanup."""
import importlib.util,json,os,pathlib,subprocess,sys,tempfile,time,unittest
ROOT=pathlib.Path(__file__).resolve().parents[4]
TOOLS=ROOT/"scripts/h62/item6/migrate-examples"
def module(name):
    spec=importlib.util.spec_from_file_location(name,TOOLS/(name+".py"));m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
census=module("census");bounded=module("bounded-run")
class Acceptance(unittest.TestCase):
    def test_nested_comments_and_strings(self):
        source='/- comment /- nested -/ end -/\n-- def fake\ndef text := "\nimport Fake.Module\n"\nlocal instance : Unit := ()\n@[noinline] def actual : Nat := 3\nexample {C : Type} : True := True.intro\n'
        clean=census.strip_comments(source)
        self.assertEqual(clean.count("\n"),source.count("\n"))
        self.assertNotIn("Fake.Module",clean)
        rows=census.declarations_in(clean)
        self.assertEqual([(r["kind"],r["name"],r["line"]) for r in rows],[("def","text",3),("instance",None,6),("def","actual",7),("example",None,8)])
    def test_success(self):
        with tempfile.TemporaryDirectory() as tmp:
            output=pathlib.Path(tmp)/"result.json"
            subprocess.run([sys.executable,str(TOOLS/"bounded-run.py"),"--output",str(output),"--",sys.executable,"-c","print('completed')"],check=True,stdout=subprocess.DEVNULL)
            self.assertIsNone(json.loads(output.read_text())["stop"])
    def test_cleanup_after_leader_exit(self):
        with tempfile.TemporaryDirectory() as tmp:
            output=pathlib.Path(tmp)/"result.json"
            child='import subprocess,sys; p=subprocess.Popen([sys.executable,"-c","import time; time.sleep(60)"]); print(p.pid,flush=True)'
            run=subprocess.run([sys.executable,str(TOOLS/"bounded-run.py"),"--output",str(output),"--",sys.executable,"-c",child],stdout=subprocess.DEVNULL)
            self.assertNotEqual(run.returncode,0)
            data=json.loads(output.read_text());self.assertEqual(data["stop"],"ORPHAN_GROUP_STOP");self.assertEqual(data["exit"],0)
            pid=int(output.with_suffix(".log").read_text().strip())
            stat=pathlib.Path(f"/proc/{pid}/stat")
            for _ in range(100):
                if not stat.exists() or stat.read_text().split()[2]=="Z":break
                time.sleep(0.01)
            if stat.exists():self.assertEqual(stat.read_text().split()[2],"Z")
if __name__=="__main__":unittest.main()
