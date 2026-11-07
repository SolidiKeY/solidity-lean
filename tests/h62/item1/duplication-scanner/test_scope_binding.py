"""Guard AST observations promoted to Scope and stale intrinsic-context dependencies."""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[4];SCRIPTS=ROOT/"scripts/h62/item1/duplication-scanner"
sys.path.insert(0,str(SCRIPTS))
try:
    import bind_project_closure as closure
finally:sys.path.pop(0)


class ScopeBindingControls(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup);self.directory=Path(self.tmp.name)
        self.pins=json.loads(closure.profile("scope")["pins"].read_text())

    def invoke(self,pattern,*options):
        return subprocess.run([sys.executable,"-B",str(SCRIPTS/"scan.py"),str(ROOT),pattern,*map(str,options)],capture_output=True,timeout=15)

    def test_explicit_admission_and_existing_ast_default(self):
        closure.admitted_sources(self.pins,"scope")
        closure.admitted_sources(json.loads(closure.PINS.read_text()))
        self.assertEqual(closure.profile("ast")["pins"],closure.PINS)
        with self.assertRaisesRegex(ValueError,"unadmitted project target"):closure.profile("arbitrary")

    def test_ast_and_scope_manifests_cannot_be_interchanged(self):
        for pins,target in [(self.pins,"ast"),(json.loads(closure.PINS.read_text()),"scope")]:
            with self.assertRaisesRegex(ValueError,"unadmitted project closure"):closure.admitted_sources(pins,target)

    def test_missing_reordered_or_fabricated_dependency_refused(self):
        for rows in (self.pins["modules"][:-1],list(reversed(self.pins["modules"])),self.pins["modules"]*2):
            pins=copy.deepcopy(self.pins);pins["modules"]=rows
            with self.assertRaises(ValueError):closure.admitted_sources(pins,"scope")
        pins=copy.deepcopy(self.pins);pins["modules"][-1]["project_dependencies"]=["Solidity/KeySort.lean"]
        with self.assertRaises(ValueError):closure.admitted_sources(pins,"scope")
        pins=copy.deepcopy(self.pins);pins["modules"][-1]["sha256"]="0"*64
        with self.assertRaisesRegex(ValueError,"source pin drift"):closure.admitted_sources(pins,"scope")

    def test_all_three_objects_must_be_fresh(self):
        old={"module":closure.encoded(["Lean"]),"base":{"sha256":"sdk","realpath":"/sdk/Lean.olean"}}
        added=[{"module":closure.encoded(row["module"]),"base":{"sha256":"fresh","realpath":"/fresh/"+row["module"][-1]+".olean"}} for row in self.pins["modules"]]
        fresh=[{"module":row["module"],"artifact":obj["base"]} for row,obj in zip(self.pins["modules"],added)]
        closure.verify_closure([old],[old]+added,fresh)
        for index in range(3):
            changed=copy.deepcopy(added);changed[index]["base"]["realpath"]="/cached/object.olean"
            with self.assertRaisesRegex(ValueError,"not the fresh compiled"):closure.verify_closure([old],[old]+changed,fresh)

    def test_scope_target_needs_its_selected_source_and_fresh_output(self):
        output=self.directory/"new"
        result=self.invoke("Solidity/AST.lean","--project-binding-target","scope","--project-binding-output",output)
        self.assertNotEqual(result.returncode,0);self.assertIn(b"pinned project source",result.stderr);self.assertFalse(output.exists())
        output.mkdir();(output/"receipt.json").write_text('{"status":"pass"}')
        result=self.invoke("Solidity/Scope.lean","--project-binding-target","scope","--project-binding-output",output)
        self.assertNotEqual(result.returncode,0);self.assertIn(b"saved receipts",result.stderr)

    def test_scope_rejects_ast_baseline_contract_before_execution(self):
        raw=self.invoke("Solidity/Scope.lean");self.assertEqual(raw.returncode,0)
        previous=json.loads(raw.stdout)
        previous["selection"]["project_binding_contract"]=hashlib.sha256(closure.PINS.read_bytes()).hexdigest()
        previous["selection"]["project_binding_target"]="Solidity.AST"
        path=self.directory/"previous.json";path.write_text(json.dumps(previous))
        output=self.directory/"new"
        result=self.invoke("Solidity/Scope.lean","--project-binding-target","scope","--project-binding-output",output,
                           "--previous",path,"--previous-sha256",hashlib.sha256(path.read_bytes()).hexdigest())
        self.assertNotEqual(result.returncode,0);self.assertIn(b"incompatible version or selection",result.stderr);self.assertFalse(output.exists())


if __name__=="__main__":unittest.main()
