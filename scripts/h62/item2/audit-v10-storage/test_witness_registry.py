"""Reference-accounting regressions; no Lean or semantic proof claim."""
import copy
import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import unittest

spec=importlib.util.spec_from_file_location("registry",Path(__file__).with_name("witness_registry.py"))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class RegistryTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.inventory=m.frozen_inventory()
    def fixture(self,root):
        directory=root/"tests/h62/item2/audit-v10-storage"
        directory.mkdir(parents=True)
        for source in m.MAP_DIR.glob("*.lean"):
            shutil.copyfile(source,directory/source.name)
        for source in m.MAP_DIR.glob("*-witness-map.json"):
            shutil.copyfile(source,directory/source.name)
        shutil.copyfile(m.MAP_DIR/"kernel-source-pins.json",directory/"kernel-source-pins.json")
        interfaces={row["frozen_id"].split(":",1)[0]
                    for _,packet in m.maps() for row in packet["rows"]}
        for relative in interfaces:
            path=Path(relative)
            if path.is_absolute() or ".." in path.parts:
                raise ValueError("unsafe test interface path")
            target=root/path;target.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(m.ROOT/path,target)
        return directory
    def test_complete_reference_ledger(self):
        result=m.build(self.inventory,m.maps())
        self.assertEqual(result["counts"],dict(conservative_rows=3281,mapped_joint_bundles=23,unmapped=3258))
        self.assertEqual(len({r["id"] for r in result["rows"]}),3281)
        self.assertEqual(len(result["witness_source_sha256"]),6)
    def test_corruption_refused(self):
        for kind in ["duplicate","unknown","signature","witness","source","interface","pin"]:
            with self.subTest(kind=kind),tempfile.TemporaryDirectory() as temp:
                root=Path(temp);directory=self.fixture(root)
                path=next(directory.glob("*-witness-map.json"));packet=json.loads(path.read_text())
                if kind=="duplicate":packet["rows"].append(copy.deepcopy(packet["rows"][0]))
                elif kind=="unknown":packet["rows"][0]["frozen_id"]="absent"
                elif kind=="signature":packet["rows"][0]["signature"]+=" "
                elif kind=="witness":packet["rows"][0]["witness"]="Missing.Namespace.theorem"
                elif kind=="source":
                    source=directory/"LoopWitnesses.lean";source.write_text(source.read_text()+"\n")
                elif kind=="interface":
                    source=root/"Solidity/Backend/StorageOps/TargetOperations.lean";source.write_text(source.read_text()+"\n")
                elif kind=="pin":
                    pins=directory/"kernel-source-pins.json";data=json.loads(pins.read_text())
                    next(iter(data["sources"].values()))["sha256"]="0"*64
                    pins.write_text(json.dumps(data))
                path.write_text(json.dumps(packet))
                with self.assertRaises(ValueError):m.build(self.inventory,m.maps(root),root)

if __name__=="__main__":unittest.main()
