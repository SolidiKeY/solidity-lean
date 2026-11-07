#!/usr/bin/env python3
"""Negative controls for lexical boundaries and owned-process cleanup."""
import importlib.util,json,os,pathlib,subprocess,sys,tempfile,time,unittest
ROOT=pathlib.Path(__file__).resolve().parents[4]
TOOLS=ROOT/"scripts/h62/item6/migrate-examples"
def module(name):
    spec=importlib.util.spec_from_file_location(name,TOOLS/(name+".py"));m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
census=module("census");bounded=module("bounded-run");interfaces=module("interfaces")
class Acceptance(unittest.TestCase):
    def test_nested_comments_and_strings(self):
        source='/- comment /- nested -/ end -/\n-- def fake\ndef text := "\nimport Fake.Module\n"\nlocal instance : Unit := ()\n@[noinline] def actual : Nat := 3\nexample {C : Type} : True := True.intro\n'
        clean=census.strip_comments(source)
        self.assertEqual(clean.count("\n"),source.count("\n"))
        self.assertNotIn("Fake.Module",clean)
        rows=census.declarations_in(clean)
        self.assertEqual([(r["kind"],r["name"],r["line"]) for r in rows],[("def","text",3),("instance",None,6),("def","actual",7),("example",None,8)])
    def test_available_cache_accounting(self):
        gib=1024**3
        # A 14 GiB charge containing 4 GiB clean inactive cache still has 6 GiB
        # estimated available; cache is reclaimable, unlike anonymous working set.
        self.assertEqual(bounded.cgroup_headroom(14*gib,16*gib,{"inactive_file":4*gib}), (6*gib,4*gib))
        # Dirty/writeback pages must not create fictitious headroom.
        self.assertEqual(bounded.cgroup_headroom(14*gib,16*gib,{"inactive_file":4*gib,"file_dirty":2*gib,"file_writeback":gib}), (3*gib,gib))
        self.assertEqual(bounded.cgroup_headroom(14*gib,16*gib,{"inactive_file":gib,"file_dirty":2*gib}), (2*gib,0))
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
class InterfaceAcceptance(unittest.TestCase):
    def fixture(self):
        modules=["Solidity.Examples.X","Solidity.Examples.Y"]
        scope={"base":interfaces.BASE,"modules":[{"module":m,"path":m.replace(".","/")+".lean","source_sha256":"0"*64} for m in modules]}
        header={"schema":"h62-examples-interface-v1","modules":list(reversed(modules))}
        keys=[["str",["anonymous"],"a.b"],["str",["str",["anonymous"],"a"],"b"]]
        rows=[{"module":modules[0],"name":"a.b","name_key":k,"kind":"definition","unsafe":False,"private_name":False,"protected_name":False,"level_parameters":[],"type":["sort",["zero"]]} for k in keys]
        return scope,header,rows
    def raw(self,header,rows):return "\n".join(json.dumps(x) for x in [header]+rows+[{"complete":True,"declarations":len(rows)}])
    def test_scope_and_structural_names(self):
        scope,header,rows=self.fixture();data=interfaces.inventory(self.raw(header,rows),scope)
        self.assertEqual(len(data["declarations"]),2)
        truncated="\n".join(self.raw(header,rows).splitlines()[:-1])
        with self.assertRaisesRegex(ValueError,"missing completion footer"):interfaces.inventory(truncated,scope)
        self.assertEqual(data["module_counts"]["Solidity.Examples.Y"],0)
        bad=dict(header);bad["modules"]=bad["modules"][:1]
        with self.assertRaises(ValueError):interfaces.inventory(self.raw(bad,rows),scope)
        with self.assertRaises(ValueError):interfaces.inventory(self.raw(header,[]),scope)
        with self.assertRaises(ValueError):interfaces.inventory(self.raw(header,[rows[0],rows[0]]),scope)
    def test_missing_and_changed_interfaces(self):
        scope,header,rows=self.fixture();old=interfaces.inventory(self.raw(header,rows),scope)
        removed=interfaces.inventory(self.raw(header,rows[:1]),scope)
        self.assertEqual(len(interfaces.compare(old,removed)["removed"]),1)
        changed=json.loads(json.dumps(rows));changed[0]["type"]=["sort",["succ",["zero"]]]
        new=interfaces.inventory(self.raw(header,changed),scope)
        self.assertEqual(len(interfaces.compare(old,new)["changed"]),1)
        header["modules"].reverse()
        self.assertEqual(old["interface_sha256"],interfaces.inventory(self.raw(header,rows),scope)["interface_sha256"])

    def test_streamed_inventory_keeps_validation(self):
        scope,header,rows=self.fixture();raw=self.raw(header,rows)
        expected=interfaces.inventory(raw,scope)
        self.assertEqual(expected,interfaces.inventory(iter(raw.splitlines()),scope))
        def truncated():
            yield from raw.splitlines()[:-1]
        with self.assertRaisesRegex(ValueError,"missing completion footer"):
            interfaces.inventory(truncated(),scope)

    def test_visibility_only_changes_and_missing_flags(self):
        scope,header,rows=self.fixture();old=interfaces.inventory(self.raw(header,rows),scope)
        for field in ("private_name","protected_name"):
            changed=json.loads(json.dumps(rows));changed[0][field]=True
            new=interfaces.inventory(self.raw(header,changed),scope)
            self.assertEqual(len(interfaces.compare(old,new)["changed"]),1)
            self.assertNotEqual(old["interface_sha256"],new["interface_sha256"])
            del changed[0][field]
            with self.assertRaisesRegex(ValueError,"visibility-name flags"):
                interfaces.inventory(self.raw(header,changed),scope)

if __name__=="__main__":unittest.main()
