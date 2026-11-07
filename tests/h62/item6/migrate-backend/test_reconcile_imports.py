import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[4]
SCRIPTS = ROOT/"scripts/h62/item6/migrate-backend"
sys.path.insert(0,str(SCRIPTS))
spec = importlib.util.spec_from_file_location("reconcile_imports",SCRIPTS/"reconcile_imports.py")
reconcile = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reconcile)

def fixture(folder, dependencies):
    module = "Solidity.Backend.Sample"
    source = folder/"Solidity/Backend/Sample.lean"
    source.parent.mkdir(parents=True,exist_ok=True)
    text = "".join("import "+dep+"\n" for dep in dependencies)
    source.write_text(text)
    row = {"module":module,"path":"Solidity/Backend/Sample.lean","imports":dependencies,
           "sha256":hashlib.sha256(source.read_bytes()).hexdigest()}
    return module,{"files":[row],"topological_closure":[module]},source.with_suffix(".ilean")

class CompilerImportControls(unittest.TestCase):
    def test_incomplete_cannot_pass_and_order_is_checked(self):
        with tempfile.TemporaryDirectory() as folder:
            artifacts = Path(folder)
            module,census,path = fixture(artifacts,["Lean","Std"])
            self.assertEqual(reconcile.reconcile(census,artifacts,artifacts)["status"],"pending")
            data = {"module":module,"version":1,"directImports":[["Lean",False,False,False],["Std",False,False,False]]}
            path.write_text(json.dumps(data))
            report = reconcile.reconcile(census,artifacts,artifacts)
            self.assertEqual(report["status"],"pass")
            self.assertEqual(report["source_inventory_checked"],1)
            self.assertEqual(report["checked_modules"],1)
            data["directImports"].reverse();path.write_text(json.dumps(data))
            self.assertEqual(reconcile.reconcile(census,artifacts,artifacts)["status"],"fail")
            path.write_text("{")
            self.assertEqual(reconcile.reconcile(census,artifacts,artifacts)["status"],"pending")

    def test_wrong_module_identity_cannot_pass(self):
        with tempfile.TemporaryDirectory() as folder:
            artifacts = Path(folder)
            module,census,path = fixture(artifacts,[])
            path.write_text(json.dumps({"module":"Solidity.Backend.Other","directImports":[]}))
            self.assertEqual(reconcile.reconcile(census,artifacts,artifacts)["status"],"fail")

    def test_unresolved_non_toolchain_dependency_cannot_pass(self):
        for dependency in ("Solidity.Missing","LeanTeX","StandardFake"):
            with self.subTest(dependency=dependency), tempfile.TemporaryDirectory() as folder:
                artifacts = Path(folder)
                module,census,path = fixture(artifacts,[dependency])
                path.write_text(json.dumps({"module":module,"directImports":[[dependency,False,False,False]]}))
                with self.assertRaises(ValueError): reconcile.reconcile(census,artifacts,artifacts)

    def test_missing_source_and_stale_hash_cannot_pass(self):
        with tempfile.TemporaryDirectory() as folder:
            artifacts = Path(folder)
            module,census,path = fixture(artifacts,[])
            path.with_suffix(".lean").write_text("-- changed\n")
            with self.assertRaises(ValueError): reconcile.reconcile(census,artifacts,artifacts)
            module,census,path = fixture(artifacts,[])
            (path.parent/"Omitted.lean").write_text("-- assigned source omitted by census\n")
            with self.assertRaises(ValueError): reconcile.reconcile(census,artifacts,artifacts)

if __name__ == "__main__": unittest.main()
