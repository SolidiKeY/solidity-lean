"""Adversarial receipt freshness controls. These external tests are not Lean proofs."""
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
sys.dont_write_bytecode=True
SCRIPT=Path(__file__).resolve().parents[4]/"scripts/h62/item2/audit-calculus/receipts.py"
spec=importlib.util.spec_from_file_location("receipts",SCRIPT)
receipts=importlib.util.module_from_spec(spec);spec.loader.exec_module(receipts)


class FreshnessControls(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup);self.root=Path(self.tmp.name)
        source=self.root/"M.lean";source.write_text("theorem t : True := True.intro")
        helper=self.root/receipts.HELPER;helper.parent.mkdir(parents=True);helper.write_text("audit helper")
        self.data={"module":"M","theorems":[]}
        self.record={"schema":2,"kind":"kernel-census","exit":0,"file":"M.lean","module":"M",
                     "source_sha256":receipts.sha(source),"helper_source_sha256":receipts.sha(helper),"lean_sha256":"same-toolchain"}
        for key,text in {"log":"H62_KERNEL_CENSUS "+json.dumps(self.data)+"\n","json":json.dumps(self.data),
                         "scratch":"import M","artifact":"checked module artifact","helper_artifact":"checked helper artifact"}.items():
            path=self.root/key;path.write_text(text);self.record[key]=str(path);self.record[key+"_sha256"]=receipts.sha(path)
        self.compiled={"exit":0,"source_sha256":self.record["source_sha256"],"artifact_sha256":self.record["artifact_sha256"],"lean_sha256":"same-toolchain"}
        self.helper={"exit":0,"source_sha256":self.record["helper_source_sha256"],"artifact_sha256":self.record["helper_artifact_sha256"],"lean_sha256":"same-toolchain"}

    def validate(self):return receipts.validate_export(self.record,self.root,self.compiled,self.helper)

    def test_consistent_receipt(self):self.assertEqual(self.validate(),self.data)

    def test_failed_new_export_cannot_reuse_old_json(self):
        self.record["exit"]=1
        with self.assertRaises(RuntimeError):self.validate()

    def test_changed_frozen_source(self):
        (self.root/"M.lean").write_text("different theorem")
        with self.assertRaises(RuntimeError):self.validate()

    def test_changed_helper_source(self):
        (self.root/receipts.HELPER).write_text("different helper")
        with self.assertRaises(RuntimeError):self.validate()

    def test_tampered_json(self):
        Path(self.record["json"]).write_text("{}")
        with self.assertRaises(RuntimeError):self.validate()

    def test_rehashed_json_still_must_match_log(self):
        Path(self.record["json"]).write_text(json.dumps({"module":"M","theorems":["fake"]}))
        self.record["json_sha256"]=receipts.sha(self.record["json"])
        with self.assertRaises(RuntimeError):self.validate()

    def test_latest_module_compile_failed(self):
        self.compiled["exit"]=1
        with self.assertRaises(RuntimeError):self.validate()

    def test_latest_helper_artifact_differs(self):
        self.helper["artifact_sha256"]="different"
        with self.assertRaises(RuntimeError):self.validate()

    def test_toolchain_mismatch(self):
        self.helper["lean_sha256"]="different"
        with self.assertRaises(RuntimeError):self.validate()

    def test_promoted_legacy_cache_is_not_a_compile(self):
        self.compiled.update(kind="compile-cache",legacy_adoption=True)
        with self.assertRaises(RuntimeError):self.validate()

    def test_replaced_legacy_artifact_cannot_be_promoted(self):
        legacy={"schema":1,"file":"M.lean","exit":0,"source_sha256":self.record["source_sha256"],"version":"old"}
        Path(self.record["artifact"]).write_text("replaced legacy artifact")
        found=receipts.find_direct_compile([legacy],"M.lean",self.record["source_sha256"],
            receipts.sha(self.record["artifact"]),{},"same-toolchain")
        self.assertIsNone(found)

    def test_mixed_toolchain_dependency_edge(self):
        parent={"lean_sha256":"sdkA"};child={"lean_sha256":"sdkB","artifact_sha256":"same-object"}
        with self.assertRaises(RuntimeError):receipts.validate_dependency_edge(parent,child,"same-object")


if __name__=="__main__":unittest.main()
