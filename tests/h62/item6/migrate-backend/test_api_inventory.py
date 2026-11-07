import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[4]
spec = importlib.util.spec_from_file_location("api_inventory", ROOT/"scripts/h62/item6/migrate-backend/api_inventory.py")
api = importlib.util.module_from_spec(spec)
spec.loader.exec_module(api)
NAT = ["str",["anonymous"],"Nat"]
BINDER = ["str",["anonymous"],"x"]
LEAF = ["const",NAT,[]]
SHARED = {"root":1,"nodes":[LEAF,["forallE",BINDER,0,0,"default"]]}
DUPLICATED = {"root":2,"nodes":[LEAF,LEAF,["forallE",BINDER,0,1,"default"]]}

class TypeInventoryControls(unittest.TestCase):
    def test_sharing_is_representation_only(self):
        self.assertEqual(api.type_hash(SHARED),api.type_hash(DUPLICATED))
        metadata = {"root":2,"nodes":[LEAF,["forallE",BINDER,0,0,"default"],["mdata",1]]}
        self.assertEqual(api.type_hash(SHARED),api.type_hash(metadata))

    def test_binder_and_structure_changes_are_visible(self):
        changed = copy.deepcopy(SHARED)
        changed["nodes"][-1][-1] = "implicit"
        self.assertNotEqual(api.type_hash(SHARED),api.type_hash(changed))
        a = ["str",["anonymous"],"x.y"]
        b = ["str",["str",["anonymous"],"x"],"y"]
        self.assertNotEqual(api.canonical(a),api.canonical(b))

    def test_open_cyclic_and_unreachable_nodes_are_refused(self):
        invalid = [
            {"root":0,"nodes":[["fvar","x"]]},
            {"root":0,"nodes":[["bvar","0"]]},
            {"root":0,"nodes":[["app",0,0]]},
            {"root":1,"nodes":[LEAF,["sort",["zero"]]]},
            {"root":0,"nodes":[["sort",["mvar","u"]]]}
        ]
        for dag in invalid:
            with self.subTest(dag=dag), self.assertRaises(ValueError): api.type_hash(dag)

    def test_module_and_declaration_loss_is_refused(self):
        census = {"files":[{"module":"Solidity.Backend.Sample"}]}
        row = {"name":BINDER,"display_name":"x","module":"Solidity.Backend.Sample", "kind":"definition","level_params":[],"unsafe":False,"visibility":"public","protected":False,"type":SHARED}
        header = {"schema":2,"module_inventory":["Solidity.Backend.Sample"],"declaration_count":1}
        with tempfile.TemporaryDirectory() as folder:
            raw = Path(folder)/"raw.jsonl"
            def write(h, rows): raw.write_text("\n".join(json.dumps(x) for x in [h,*rows])+"\n")
            write(header,[row]);self.assertEqual(api.index_export(raw,census)["declaration_count"],1)
            for h,rows in [({**header,"module_inventory":[]},[row]),(header,[]),({**header,"declaration_count":2},[row,row])]:
                write(h,rows)
                with self.assertRaises(ValueError): api.index_export(raw,census)

    def test_undeclared_and_duplicate_universe_parameters_are_refused(self):
        census = {"files":[{"module":"Solidity.Backend.Sample"}]}
        universe = ["str",["anonymous"],"u"]
        header = {"schema":2,"module_inventory":["Solidity.Backend.Sample"],"declaration_count":1}
        with tempfile.TemporaryDirectory() as folder:
            raw = Path(folder)/"raw.jsonl"
            for node in (["sort",["param",universe]],["const",NAT,[["param",universe]]]):
                row = {"name":BINDER,"display_name":"x","module":"Solidity.Backend.Sample","kind":"definition","level_params":[],"unsafe":False,"visibility":"public","protected":False,"type":{"root":0,"nodes":[node]}}
                raw.write_text("\n".join(json.dumps(x) for x in (header,row))+"\n")
                with self.assertRaises(ValueError): api.index_export(raw,census)
                row["level_params"] = [universe]
                raw.write_text("\n".join(json.dumps(x) for x in (header,row))+"\n")
                self.assertEqual(api.index_export(raw,census)["declaration_count"],1)
                row["level_params"] = [universe,universe]
                raw.write_text("\n".join(json.dumps(x) for x in (header,row))+"\n")
                with self.assertRaises(ValueError): api.index_export(raw,census)

    def test_noncanonical_naturals_are_refused(self):
        for value in ("01","١","²","-1",""):
            self.assertFalse(api.name_ok(["num",["anonymous"],value]))
            with self.assertRaises(ValueError): api.type_hash({"root":0,"nodes":[["natVal",value]]})
        for value in ("0","1","123"): self.assertTrue(api.natural_ok(value))

    def test_comparison_refuses_duplicate_or_malformed_indexes(self):
        row = {"name":BINDER,"display_name":"x","module":"Solidity.Backend.Sample","kind":"definition","level_params":[],"unsafe":False,"visibility":"public","protected":False,"type_sha256":"a"*64}
        valid = {"schema":2,"modules":["Solidity.Backend.Sample"],"declaration_count":1,"raw_sha256":"b"*64,"declarations":[row]}
        self.assertFalse(api.compare(valid,valid)["changed"])
        bads = [{**valid,"schema":True},{**valid,"declaration_count":2},{**valid,"raw_sha256":"invalid"},{**valid,"modules":[]},{**valid,"declarations":[row,row],"declaration_count":2},{**valid,"declarations":[{**row,"type_sha256":"bad"}]}]
        for bad in bads:
            with self.subTest(bad=bad),self.assertRaises(ValueError): api.compare(bad,valid)
            with self.assertRaises(ValueError): api.compare(valid,bad)

    def test_output_scope_alias_and_overwrite_guards_without_writes(self):
        with self.assertRaises(ValueError): api.validate_output(ROOT/"Solidity/Backend/Creation/Linking.lean")
        with self.assertRaises(ValueError): api.validate_output(ROOT/"tests/h62/item6/migrate-backend/ApiInventory.lean.in")
        target = ROOT/"tests/h62/item6/migrate-backend/NoWriteApi.json"
        with self.assertRaises(ValueError): api.validate_output(target,[target])
        self.assertEqual(api.validate_output(target),target.resolve())

    def test_generated_public_names_are_kept_and_protected_changes_visible(self):
        generated = ["str",["str",["anonymous"],"Solidity"],"_proof_2"]
        self.assertFalse(api.name_is_private(generated))
        private = ["str",["num",["str",["anonymous"],"_private"],"0"],"x"]
        self.assertTrue(api.name_is_private(private))
        row = {"name":generated,"display_name":"Solidity._proof_2","module":"Solidity.Backend.Sample","kind":"theorem","level_params":[],"unsafe":False,"visibility":"public","protected":False,"type_sha256":"a"*64}
        old = {"schema":2,"modules":["Solidity.Backend.Sample"],"declaration_count":1,"raw_sha256":"b"*64,"declarations":[row]}
        new = {**old,"declarations":[{**row,"protected":True}]}
        self.assertEqual(len(api.compare(old,new)["changed"]),1)
        for bad_row in ({**row,"visibility":"private"},{**row,"protected":"false"}):
            with self.assertRaises(ValueError): api.compare({**old,"declarations":[bad_row]},old)
        with self.assertRaises(ValueError): api.compare({**old,"schema":1},old)

if __name__ == "__main__": unittest.main()
