"""Guard cached project substitution, changed source/imports and metadata scope."""
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
    spec=importlib.util.spec_from_file_location("project_leaf",SCRIPTS/"bind_project_leaf.py")
    leaf=importlib.util.module_from_spec(spec);spec.loader.exec_module(leaf)
finally:sys.path.pop(0)


def name(part):return ["str",["anonymous"],part]


def artifact(module,digest="original",path="/fresh/module.olean"):
    return {"module":module,"base":{"sha256":digest,"realpath":path}}


class ProjectLeafControls(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup);self.directory=Path(self.temp.name)
        self.pins=json.loads(leaf.PINS.read_text())

    def test_original_readonly_source_and_probe_pins(self):leaf.admitted_sources(self.pins)

    def test_source_drift_or_symlink_stops_before_compile(self):
        pins=copy.deepcopy(self.pins);pins["source_sha256"]="0"*64
        with self.assertRaisesRegex(ValueError,"source pin drift"):leaf.admitted_sources(pins)
        source=self.directory/"KeySort.lean";source.symlink_to(leaf.SOURCE)
        with mock.patch.object(leaf,"SOURCE",source),self.assertRaisesRegex(ValueError,"symlink"):leaf.admitted_sources(self.pins)

    def test_new_import_rejected_even_with_updated_source_hash(self):
        source=self.directory/"KeySort.lean";source.write_text('import Solidity.Backend.WorldCalls.Premises\n')
        pins=copy.deepcopy(self.pins);pins["source_sha256"]=leaf.binder.sha(source)
        with mock.patch.object(leaf,"SOURCE",source),self.assertRaisesRegex(ValueError,"no longer import-free"):leaf.admitted_sources(pins)

    def test_fresh_artifact_and_exact_one_module_extension(self):
        old=artifact(name("Lean"));new=artifact(leaf.MODULE,"fresh","/fresh/KeySort.olean")
        leaf.verify_closure([old],[old,new],new["base"])
        for rows in ([old,new,artifact(name("Foreign"))],[new],[old,new,new]):
            with self.assertRaises(ValueError):leaf.verify_closure([old],rows,new["base"])

    def test_cached_artifact_or_mutated_dependency_rejected(self):
        old=artifact(name("Lean"));new=artifact(leaf.MODULE,"fresh","/fresh/KeySort.olean")
        changed=copy.deepcopy(old);changed["base"]["sha256"]="changed"
        with self.assertRaisesRegex(ValueError,"dependency changed"):leaf.verify_closure([old],[changed,new],new["base"])
        for field,value in (("sha256","cached"),("realpath","/cache/KeySort.olean")):
            wrong=copy.deepcopy(new);wrong["base"][field]=value
            with self.assertRaisesRegex(ValueError,"not the fresh"):leaf.verify_closure([old],[old,wrong],new["base"])

    def test_project_validator_requires_explicit_target_fixture_default_unchanged(self):
        value={"format":1,"module":leaf.MODULE,"total":1,"rows":[{"declaration":name("T"),"kind":"inductive","status":"serialized","signature":[]}]}
        with self.assertRaises(ValueError):leaf.kernel.validate(value)
        self.assertEqual(leaf.kernel.validate(value,leaf.MODULE),value)

    def test_sidecar_presence_and_hash_changes_are_observed(self):
        artifact=self.directory/"KeySort.olean";artifact.write_bytes(b"fresh")
        initial=leaf.project_sidecars(artifact);side=Path(str(artifact)+".server");side.write_bytes(b"server")
        self.assertNotEqual(initial,leaf.project_sidecars(artifact))
        side.unlink();side.symlink_to(artifact)
        with self.assertRaisesRegex(ValueError,"symlink"):leaf.project_sidecars(artifact)

    def test_saved_project_receipt_never_triggers_rebuild(self):
        output=self.directory/"existing";output.mkdir();(output/"receipt.json").write_text('{"status":"pass"}')
        with mock.patch.object(leaf.binder,"rebuild") as rebuild:
            with self.assertRaises(FileExistsError):leaf.run(output)
        rebuild.assert_not_called()


if __name__=="__main__":unittest.main()
