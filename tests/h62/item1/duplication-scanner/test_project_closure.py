"""Guard cached dependency objects, omitted closure members and source drift."""
import copy
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

ROOT=Path(__file__).resolve().parents[4];SCRIPTS=ROOT/"scripts/h62/item1/duplication-scanner"
sys.path.insert(0,str(SCRIPTS))
try:
    spec=importlib.util.spec_from_file_location("project_closure",SCRIPTS/"bind_project_closure.py")
    closure=importlib.util.module_from_spec(spec);spec.loader.exec_module(closure)
finally:sys.path.pop(0)


def artifact(parts,digest="fresh",path="/fresh/module.olean"):
    return {"module":closure.encoded(parts),"base":{"sha256":digest,"realpath":path}}


class ProjectClosureControls(unittest.TestCase):
    def setUp(self):
        self.pins=json.loads(closure.PINS.read_text())
        self.old=artifact(["Lean"],"sdk","/sdk/Lean.olean")
        self.new=[artifact(["Solidity",name],path="/fresh/"+name+".olean") for name in ("KeySort","AST")]
        self.fresh=[{"module":["Solidity",name],"artifact":row["base"]} for name,row in zip(("KeySort","AST"),self.new)]

    def test_exact_original_closure_is_admitted(self):closure.admitted_sources(self.pins)

    def test_missing_duplicate_foreign_cached_or_reordered_source_rejected(self):
        for rows in (self.pins["modules"][:-1],self.pins["modules"]*2,list(reversed(self.pins["modules"]))):
            pins=copy.deepcopy(self.pins);pins["modules"]=rows
            with self.assertRaisesRegex(ValueError,"unadmitted project closure"):closure.admitted_sources(pins)
        pins=copy.deepcopy(self.pins);pins["modules"][1]["sha256"]="cached"
        with self.assertRaisesRegex(ValueError,"source pin drift"):closure.admitted_sources(pins)

    def test_exact_fresh_dependency_extension(self):closure.verify_closure([self.old],[self.old]+self.new,self.fresh)

    def test_missing_extra_duplicate_or_preloaded_project_rejected(self):
        for after in ([self.old]+self.new[:1],[self.old]+self.new+[artifact(["Foreign"])],[self.old]+self.new*2):
            with self.assertRaises(ValueError):closure.verify_closure([self.old],after,self.fresh)
        with self.assertRaises(ValueError):closure.verify_closure([self.old,self.new[0]],[self.old]+self.new,self.fresh)

    def test_each_dependency_hash_and_path_bound(self):
        for index in range(2):
            for field,value in (("sha256","stale"),("realpath","/cached/object.olean")):
                changed=copy.deepcopy(self.new);changed[index]["base"][field]=value
                with self.assertRaisesRegex(ValueError,"not the fresh compiled"):
                    closure.verify_closure([self.old],[self.old]+changed,self.fresh)

    def test_sdk_artifact_change_and_duplicate_fresh_identity_rejected(self):
        changed=copy.deepcopy(self.old);changed["base"]["sha256"]="changed"
        with self.assertRaisesRegex(ValueError,"existing dependency changed"):
            closure.verify_closure([self.old],[changed]+self.new,self.fresh)
        with self.assertRaises(ValueError):closure.verify_closure([self.old],[self.old]+self.new,self.fresh*2)

    def test_lexical_join_uses_exact_staged_bytes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);(root/"AST.lean").write_bytes(b"compiled bytes")
            row={"path":"AST.lean","sha256":closure.hashlib.sha256(b"compiled bytes").hexdigest()}
            self.assertEqual(closure.staged_bytes(root,row),b"compiled bytes")
            (root/"AST.lean").write_bytes(b"different bytes")
            with self.assertRaisesRegex(ValueError,"staged lexical bytes"):
                closure.staged_bytes(root,row)

    def test_probe_metadata_bytes_are_bound_to_checked_process_log(self):
        with tempfile.TemporaryDirectory() as tmp:
            log=Path(tmp)/"probe.log"
            raw=(closure.binder.observer.PREFIX+'{}\n'+closure.leaf.PREFIX+'{"census":{},"locations":{}}\n').encode()
            log.write_bytes(raw);digest=closure.hashlib.sha256(raw).hexdigest()
            self.assertEqual(closure.checked_probe(log,digest),({}, {"census":{},"locations":{}}))
            log.write_bytes(raw.replace(b'"census":{}',b'"census":{"fabricated":true}'))
            with self.assertRaisesRegex(ValueError,"checked process output"):
                closure.checked_probe(log,digest)

    def test_saved_success_does_not_trigger_build(self):
        with tempfile.TemporaryDirectory() as tmp:
            output=Path(tmp);(output/"receipt.json").write_text('{"status":"pass"}')
            with mock.patch.object(closure.binder,"rebuild") as rebuild:
                with self.assertRaises(FileExistsError):closure.run(output)
            rebuild.assert_not_called()


if __name__=="__main__":unittest.main()
