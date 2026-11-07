"""Guard H127 input binding against ambient environment and undeclared dependencies.

Synthetic source plans/toolchain bytes test admission only. No Git, compiler,
Lean, worker, container or input executable is run, including in positive tests.
"""
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import stat
import tempfile
import unittest
from unittest import mock

spec=importlib.util.spec_from_file_location("input_set",Path(__file__).with_name("input-set.py"))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)


class SetControls(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name).resolve();self.inputs={};self.roots={}
        for role in m.ROLES:
            path=self.root/role;path.mkdir();self.roots[role]=path
        source=self.roots["source"]
        for module in m.plan_module.SLOW:
            path=source/(module.replace(".","/")+".lean");path.parent.mkdir(parents=True,exist_ok=True);path.write_text("-- synthetic; never elaborated\n")
        (source/"lake-manifest.json").write_text(json.dumps({"version":"1.1.0","packagesDir":".lake/packages","lakeDir":".lake","packages":[],"name":"«solidity-lean»"}))
        (source/"lakefile.toml").write_text('name = "fixture"\ndefaultTargets = ["Solidity"]\n[[lean_lib]]\nname = "SoliditySlowExamples"\n')
        (source/"lean-toolchain").write_text("leanprover/lean4:v4.24.0\n")
        (source/"SoliditySlowExamples.lean").write_text("\n".join("import "+x for x in m.plan_module.SLOW)+"\n")
        (source/".git").mkdir();(source/".git/HEAD").write_text("synthetic unverified Git metadata\n")
        tools=self.roots["toolchain"]/"bin";tools.mkdir()
        for name in ("lean","lake"):
            path=tools/name;path.write_bytes(b"synthetic bytes, never executed");path.chmod(0o755)
        (self.roots["cache"]/"fixture").write_bytes(b"initial fixture state")
        for path in source.rglob("*"):
            if path.is_file() and ".git" not in path.parts:path.chmod(0o644)
        self.plan_path=self.root/"plan.json"
        self.pin_plan()
        for role in m.ROLES:self.pin_role(role)

    def write_pin(self,path,value):
        path.write_text(json.dumps(value,sort_keys=True)+"\n")
        return hashlib.sha256(path.read_bytes()).hexdigest()

    def pin_plan(self):
        entries=[]
        for path in sorted(self.roots["source"].rglob("*")):
            if not path.is_file() or ".git" in path.parts:continue
            raw=path.read_bytes();mode=stat.S_IMODE(path.stat().st_mode)
            entries.append({"path":path.relative_to(self.roots["source"]).as_posix(),"mode":"100755" if mode==0o755 else "100644","bytes":len(raw),"sha256":hashlib.sha256(raw).hexdigest()})
        self.plan={"schemaVersion":1,"status":"prepared-not-executed","head":"a"*40,"tree":"b"*40,"rootGate":"SoliditySlowExamples","slowModules":list(m.plan_module.SLOW),"sourceInventory":entries}
        self.plan_pin=self.write_pin(self.plan_path,self.plan)

    def pin_role(self,role):
        receipt=self.root/(role+"-inventory.json")
        pin=self.write_pin(receipt,m.copy.inventory.inventory(self.roots[role]))
        self.inputs[role]={"root":str(self.roots[role]),"receipt":str(receipt),"sha256":pin}

    def admit(self):return m.admit(self.plan_path,self.plan_pin,self.inputs)

    def test_positive_binding_drops_ambient_paths_and_cannot_authorize_worker(self):
        with mock.patch.dict(os.environ,{"LEAN_PATH":"/host/injected","LD_PRELOAD":"/host/injected.so","GITHUB_ACTIONS":"true","HOME":"/host/home","LAKE_HOME":"/host/lake"}):
            result=self.admit()
        self.assertEqual(result["environment"],m.ENVIRONMENT)
        for key in ("LEAN_PATH","LD_PRELOAD","GITHUB_ACTIONS"):
            self.assertNotIn(key,result["environment"])
        for key in ("ciBudgetAuthorized","sourceGitSemanticsAuthenticated","imageAuthenticated","toolchainVersionAuthenticated","writableCacheInitialized","networkIsolationAuthenticated","readOnlyMountAuthenticated","lifetimeSealed","workerExecutionAuthorized"):
            self.assertIs(result[key],False)
        result["environment"]["HOME"]="changed"
        self.assertEqual(m.ENVIRONMENT["HOME"],"/output/home")

    def test_missing_extra_role_and_bad_receipt_pin_refused(self):
        original=copy.deepcopy(self.inputs)
        for variant in ("missing","extra","pin"):
            self.inputs=copy.deepcopy(original)
            if variant=="missing":del self.inputs["packages"]
            elif variant=="extra":self.inputs["hidden"]={}
            else:self.inputs["cache"]["sha256"]="0"*64
            with self.subTest(variant=variant),self.assertRaises(ValueError):self.admit()

    def test_unlisted_source_and_hidden_package_even_with_updated_role_pin(self):
        for role in ("source","packages"):
            path=self.roots[role]/"hidden";path.write_bytes(b"unexpected")
            self.pin_role(role)
            with self.subTest(role=role),self.assertRaisesRegex(ValueError,"unlisted"):self.admit()
            path.unlink();self.pin_role(role)

    def test_manifest_and_lake_dependency_cannot_resolve_new_package(self):
        path=self.roots["source"]/"lake-manifest.json";original=path.read_bytes()
        value=json.loads(original);value["packages"]=[{"name":"unexpected"}]
        path.write_text(json.dumps(value));self.pin_plan();self.pin_role("source")
        with self.assertRaisesRegex(ValueError,"empty package manifest"):self.admit()
        path.write_bytes(original)
        (self.roots["source"]/"lakefile.toml").write_text('name = "fixture"\n[[require]]\nname = "unexpected"\n')
        self.pin_plan();self.pin_role("source")
        with self.assertRaisesRegex(ValueError,"unlisted Lake dependency"):self.admit()

    def test_source_plan_bytes_names_and_denominator_are_independent(self):
        for field in ("sha256","path","slowModules"):
            value=copy.deepcopy(self.plan)
            if field=="slowModules":value[field].pop()
            elif field=="path":value["sourceInventory"].append(copy.deepcopy(value["sourceInventory"][0]))
            else:value["sourceInventory"][0][field]="0"*64
            self.plan_pin=self.write_pin(self.plan_path,value)
            with self.subTest(field=field),self.assertRaises(ValueError):self.admit()

    def test_selected_sources_root_denominator_and_nondefault_mapping_required(self):
        source=self.roots["source"]
        path=source/(m.plan_module.SLOW[0].replace(".","/")+".lean")
        original=path.read_bytes();path.unlink();self.pin_plan();self.pin_role("source")
        with self.assertRaisesRegex(ValueError,"selected slow source absent"):self.admit()
        path.write_bytes(original);path.chmod(0o644)
        root=source/"SoliditySlowExamples.lean";original=root.read_bytes()
        root.write_text("-- empty, not a proof root\n");self.pin_plan();self.pin_role("source")
        with self.assertRaisesRegex(ValueError,"denominator changed"):self.admit()
        root.write_bytes(original)
        config=source/"lakefile.toml";config.write_text(config.read_text().replace('["Solidity"]','["SoliditySlowExamples"]'))
        self.pin_plan();self.pin_role("source")
        with self.assertRaisesRegex(ValueError,"non-default source mapping"):self.admit()

    def test_role_overlap_and_identity_alias_refused(self):
        original=copy.deepcopy(self.inputs)
        self.inputs["cache"]=copy.deepcopy(self.inputs["source"])
        with self.assertRaisesRegex(ValueError,"overlap or alias"):self.admit()
        self.inputs=original
        real=m.copy.inventory.inventory
        source_id=real(self.roots["source"])["records"][0]["observedIdentity"]
        def alias(root):
            value=real(root)
            if Path(root)==self.roots["cache"]:
                value["records"][0]["observedIdentity"]["device"]=source_id["device"]
                value["records"][0]["observedIdentity"]["inode"]=source_id["inode"]
            return value
        path=Path(self.inputs["cache"]["receipt"])
        self.inputs["cache"]["sha256"]=self.write_pin(path,alias(self.roots["cache"]))
        with mock.patch.object(m.copy.inventory,"inventory",side_effect=alias),self.assertRaisesRegex(ValueError,"overlap or alias"):self.admit()

    def test_toolchain_selection_and_executable_shape_refused(self):
        (self.roots["toolchain"]/"bin/lean").chmod(0o644);self.pin_role("toolchain")
        with self.assertRaisesRegex(ValueError,"executable missing"):self.admit()
        (self.roots["toolchain"]/"bin/lean").chmod(0o755);self.pin_role("toolchain")
        (self.roots["source"]/"lean-toolchain").write_text("unreviewed toolchain\n")
        self.pin_plan();self.pin_role("source")
        with self.assertRaisesRegex(ValueError,"toolchain selection"):self.admit()

    def test_source_drift_during_input_set_observation_refused(self):
        real=m.copy.inventory.inventory;changed=False
        def drift(root):
            nonlocal changed
            value=real(root)
            if Path(root)==self.roots["cache"] and not changed:
                changed=True
                target=self.roots["source"]/(m.plan_module.SLOW[0].replace(".","/")+".lean")
                target.write_text("-- changed\n")
            return value
        with mock.patch.object(m.copy.inventory,"inventory",side_effect=drift),self.assertRaisesRegex(ValueError,"changed during admission"):
            self.admit()


if __name__=="__main__":unittest.main()
