"""Guard regression: malformed/private/inherited candidates must not become coverage."""
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "scripts/h62/item2/audit-bytecode-selection"))
from kernel_metadata import *

import copy
import unittest

class MetadataSchemaTests(unittest.TestCase):
    def row(self):
        return {
            "manifest_sha256": "fingerprint", "name": "_private.M.0.N.t",
            "user_name": "N.t", "private": True, "original_kind": "Lean.ConstantKind.thm",
            "declaration_range": {"start_line": 1, "end_line": 2, "selection_line": 1},
            "module": "M", "kind": "theorem", "interface_or_premises_module": False,
            "predicate_valued": False, "body_expr": None, "body_status": "proof body intentionally omitted",
            "is_theorem": True, "is_projection": False, "proof_type": True,
            "type_expr": "closed type expression", "type": "True", "level_params": [],
            "binders": [], "parents": [],
        }
    def test_complete_row(self):
        self.assertEqual(validate_record(self.row())["user_name"], "N.t")
    def test_schema_and_flag_corruption(self):
        for change in ("missing", "bool", "range", "kind", "proof"):
            value=self.row()
            if change=="missing": value.pop("binders")
            if change=="bool": value["private"]=1
            if change=="range": value["declaration_range"]["selection_line"]=3
            if change=="kind": value["kind"]="constant"
            if change=="proof": value["proof_type"]=False
            with self.subTest(change=change), self.assertRaises(ValueError):
                validate_record(value)
    def test_private_link_needs_exact_name_range_and_flag(self):
        source={"id":"p:0","module":"M","candidate_user_name":"N.t","name_token_line":1,
                "signature_sha256":"a"*64}
        row=self.row()
        self.assertEqual(source_links([row],[source],{"p:0"})[0]["status"],"name_range_match_candidate")
        row["private"]=False
        self.assertEqual(source_links([row],[source],{"p:0"})[0]["status"],"unmatched")
        row=self.row();row["declaration_range"]=None
        self.assertEqual(source_links([row],[source],{"p:0"})[0]["status"],"unmatched")
    def test_duplicate_source_identity_and_anchor(self):
        row=self.row()
        source={"id":"p:0","module":"M","candidate_user_name":"N.t","name_token_line":1,
                "signature_sha256":"a"*64}
        with self.assertRaises(ValueError): source_links([row],[source,source],{"p:0"})
        other=dict(source,id="p:1")
        result=source_links([row],[source,other],{"p:0","p:1"})
        self.assertEqual([r["status"] for r in result],["ambiguous","ambiguous"])
    def test_mixed_manifests_refused(self):
        a=self.row();b=self.row();b.update(name="other",manifest_sha256="other")
        with self.assertRaises(ValueError):source_links([a,b],[],set())
        with self.assertRaises(ValueError):parent_metadata([a,b])
    def test_prop_projection_can_be_original_theorem(self):
        row=self.row();row.update(is_projection=True,kind="field")
        self.assertEqual(validate_record(row)["kind"],"field")
    def test_unsupported_enums_and_empty_completion(self):
        row=self.row();row["original_kind"]="made up"
        with self.assertRaises(ValueError):validate_record(row)
        row=self.row();row["is_projection"]=True
        with self.assertRaises(ValueError):validate_record(row)
        pins={"manifest_sha256":"fingerprint","modules":["M"]}
        with self.assertRaises(ValueError):
            read_records('H62_CENSUS_DONE {"manifest_sha256":"fingerprint","counts":{"M":0}}',pins)
    def test_completion_and_duplicate_keys(self):
        row=self.row();pins={"manifest_sha256":"fingerprint","modules":["M"]}
        log="H62_CENSUS_JSON "+json.dumps(row)+"\nH62_CENSUS_DONE "+json.dumps({
             "manifest_sha256":"fingerprint","counts":{"M":1}})+"\n"
        self.assertEqual(len(read_records(log,pins)),1)
        with self.assertRaises(ValueError): read_records(log+log.splitlines()[0],pins)
        with self.assertRaises(ValueError): parse_json('{"name":"a","name":"b"}')


class ParentMetadataTests(unittest.TestCase):
    row = MetadataSchemaTests.row
    def constant(self, name, parents=None):
        row=self.row()
        row.update(name=name, user_name=name, private=False, is_theorem=False,
                   proof_type=False, original_kind="Lean.ConstantKind.defn", kind="constant", body_status="no available value",
                   parents=parents or [])
        return row
    def test_exact_parent_edges_and_external_gap(self):
        edge={"structure":"Parent","projection":"Child.toParent","subobject":True}
        child=self.constant("Child",[edge])
        gap=parent_metadata([child])[0]
        self.assertEqual(len(gap["missing_records"]),1)
        self.assertIn("uncovered",gap["inherited_obligation_status"])
        parent=self.constant("Parent")
        projection=self.constant("Child.toParent")
        projection.update(kind="field",is_projection=True)
        linked=parent_metadata([child,parent,projection])[0]
        self.assertEqual(linked["missing_records"],[])
        self.assertEqual(linked["edges"][0]["route"],["Child","Parent"])
        self.assertEqual(linked["witness_status"],"uncovered")
    def test_projection_type_evidence_is_preserved_without_acceptance(self):
        child=self.constant("Child",[{"structure":"Parent","projection":"Child.toParent","subobject":True}])
        parent=self.constant("Parent")
        projection=self.constant("Child.toParent")
        projection.update(kind="field",is_projection=True, type_expr="forall Child, Parent", type="Child → Parent",
            level_params=["u"], binders=[{"name":"self","binder_info":"Lean.BinderInfo.default",
                "type":"Child","proof_binder":False,"head_constant":"Child"}])
        edge=parent_metadata([child,parent,projection])[0]["edges"][0]
        evidence=edge["projection_type"]
        self.assertEqual(evidence["type_expr"],projection["type_expr"])
        self.assertEqual(evidence["level_params"],["u"])
        self.assertEqual(evidence["binders"],projection["binders"])
        self.assertEqual(evidence["type_expr_sha256"],hashlib.sha256(projection["type_expr"].encode()).hexdigest())
        self.assertIn("no provenance",evidence["status"])
        self.assertEqual(edge["child_type"]["name"],"Child")
        self.assertEqual(edge["parent_type"]["name"],"Parent")

    def test_corrupted_type_changes_binding_without_becoming_verified(self):
        before=self.constant("Child.toParent");after=copy.deepcopy(before)
        after["type_expr"]="forall Unrelated, Other"
        left,right=observed_type(before),observed_type(after)
        self.assertNotEqual(left["record_sha256"],right["record_sha256"])
        self.assertNotEqual(left["type_expr_sha256"],right["type_expr_sha256"])
        self.assertEqual(left["status"],right["status"])
        after=copy.deepcopy(before);after["module"]="Different"
        self.assertNotEqual(left["record_sha256"],observed_type(after)["record_sha256"])
        self.assertEqual(left["type_expr_sha256"],observed_type(after)["type_expr_sha256"])

    def test_type_snapshot_does_not_alias_mutable_input(self):
        original=self.constant("Child")
        original["level_params"]=["u"]
        original["binders"]=[{"name":"self","binder_info":"Lean.BinderInfo.default",
            "type":"Child","proof_binder":False,"head_constant":"Child"}]
        snapshot=observed_type(original)
        original["level_params"].append("v")
        original["binders"][0]["type"]="Other"
        original["declaration_range"]["end_line"]=9
        self.assertEqual(snapshot["level_params"],["u"])
        self.assertEqual(snapshot["binders"][0]["type"],"Child")
        self.assertEqual(snapshot["declaration_range"]["end_line"],2)
        snapshot["level_params"].append("w")
        self.assertEqual(original["level_params"],["u","v"])

    def test_missing_type_records_stay_missing(self):
        child=self.constant("Child",[{"structure":"External","projection":"Child.toExternal","subobject":True}])
        result=parent_metadata([child])[0]
        edge=result["edges"][0]
        self.assertIsNone(edge["parent_type"])
        self.assertIsNone(edge["projection_type"])
        self.assertEqual(result["missing_records"],[edge])
        self.assertIn("uncovered",result["inherited_obligation_status"])

    def test_diamond_retains_both_inherited_type_routes(self):
        def link(c,p): return {"structure":p,"projection":c+".to"+p,"subobject":True}
        records=[self.constant("Root",[link("Root","Left"),link("Root","Right")]),
                 self.constant("Left",[link("Left","Base")]),
                 self.constant("Right",[link("Right","Base")]),self.constant("Base")]
        for child,parent in [("Root","Left"),("Root","Right"),("Left","Base"),("Right","Base")]:
            projection=self.constant(child+".to"+parent)
            projection.update(kind="field",is_projection=True,type_expr=child+"→"+parent)
            records.append(projection)
        root=parent_metadata(records)[0]
        self.assertEqual([e["route"] for e in root["edges"] if e["structure"]=="Base"],
                         [["Root","Left","Base"],["Root","Right","Base"]])
        self.assertEqual(root["missing_records"],[])
        self.assertEqual(root["witness_status"],"uncovered")
        self.assertIn("not reconstructed",root["inherited_obligation_status"])

    def test_wrong_projection_is_refused(self):
        edge={"structure":"Parent","projection":"Child.toParent","subobject":True}
        with self.assertRaises(ValueError):
            parent_metadata([self.constant("Child",[edge]),self.constant("Parent"),
                             self.constant("Child.toParent")])
    def test_cycle_is_retained_without_loop(self):
        row=self.constant("A",[{"structure":"A","projection":"A.self","subobject":True}])
        projection=self.constant("A.self");projection.update(kind="field",is_projection=True)
        self.assertEqual(parent_metadata([row,projection])[0]["cycles"],[["A","A"]])

if __name__ == "__main__":
    unittest.main()
