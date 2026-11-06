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


class ChunkControls(unittest.TestCase):
    def parts(self):
        return [{"module":"M","offset":0,"limit":2,"total":3,"theorems":[{"name":"a"},{"name":"b"}]},
                {"module":"M","offset":2,"limit":2,"total":3,"theorems":[{"name":"c"}]}]

    def parse(self,parts):
        log="\n".join("H62_KERNEL_CENSUS_CHUNK "+json.dumps(part) for part in parts)
        return receipts.parse_export_log(log,"M","chunks-v1")

    def test_all_chunks_reassemble(self):
        self.assertEqual([r["name"] for r in self.parse(self.parts())["theorems"]],["a","b","c"])

    def test_missing_chunk_rejected(self):
        with self.assertRaises(RuntimeError):self.parse(self.parts()[:1])

    def test_duplicate_chunk_rejected(self):
        parts=self.parts()
        with self.assertRaises(RuntimeError):self.parse(parts+parts[1:])

    def test_inconsistent_total_rejected(self):
        parts=self.parts();parts[1]["total"]=4
        with self.assertRaises(RuntimeError):self.parse(parts)

    def test_repeated_theorem_rejected(self):
        parts=self.parts();parts[1]["theorems"]=[{"name":"b"}]
        with self.assertRaises(RuntimeError):self.parse(parts)

    def test_truncated_chunk_rejected(self):
        parts=self.parts();parts[0]["theorems"].pop()
        with self.assertRaises(RuntimeError):self.parse(parts)

    def test_empty_module_has_one_checked_empty_chunk(self):
        parts=[{"module":"M","offset":0,"limit":16,"total":0,"theorems":[]}]
        self.assertEqual(self.parse(parts),{"module":"M","theorems":[]})


class ProbeFreshnessControls(unittest.TestCase):
    def test_malformed_zero_exit_probe_supersedes_prior_success(self):
        with tempfile.TemporaryDirectory() as temporary:
            log=Path(temporary)/"probe.log"
            for text in [
                "H62_KERNEL_CENSUS_CHUNK {bad json",
                "H62_KERNEL_CENSUS_CHUNK "+json.dumps({"module":"M"}),
                "H62_KERNEL_CENSUS_CHUNK "+json.dumps({"module":"M","offset":0,"limit":16,"total":-1,"theorems":[]}),
            ]:
                with self.subTest(text=text):
                    log.write_text(text)
                    history=[{"kind":"kernel-census","file":"M.lean","exit":0}]
                    record={"kind":"kernel-census-probe","file":"M.lean","module":"M","log":str(log),"exit":0}
                    with self.assertRaises(RuntimeError):
                        receipts.probe_total_or_tombstone(record,16,history.append)
                    latest=[r for r in history if r["kind"]=="kernel-census"][-1]
                    self.assertEqual(latest["exit"],89)
                    with self.assertRaises(RuntimeError):
                        receipts.validate_export(latest,Path(temporary),{},{})

    def test_well_formed_probe_total(self):
        with tempfile.TemporaryDirectory() as temporary:
            log=Path(temporary)/"probe.log"
            log.write_text("H62_KERNEL_CENSUS_CHUNK "+json.dumps({"module":"M","offset":0,"limit":16,"total":1,"theorems":[{"name":"t"}]}))
            history=[]
            self.assertEqual(receipts.probe_total_or_tombstone({"module":"M","log":str(log)},16,history.append),1)
            self.assertEqual(history,[])

class DagStructureControls(unittest.TestCase):
    def row(self):
        return {"type_expression_format":"expr-dag-v1",
                "type_expression":{"root":1,"nodes":[["leaf","P"],["forall","x",0,0,"default"]]},
                "binders":[{"domain_node":0}]}

    def test_valid_dependent_domain_graph(self):
        self.assertIsNone(receipts.validate_statement_encoding(self.row()))

    def test_forward_edge_rejected(self):
        row=self.row();row["type_expression"]["nodes"][1][2]=1
        with self.assertRaises(RuntimeError):receipts.validate_statement_encoding(row)

    def test_missing_binder_rejected(self):
        row=self.row();row["binders"]=[]
        with self.assertRaises(RuntimeError):receipts.validate_statement_encoding(row)

    def test_wrong_domain_rejected(self):
        row=self.row();row["binders"][0]["domain_node"]=1
        with self.assertRaises(RuntimeError):receipts.validate_statement_encoding(row)

    def test_boolean_domain_rejected(self):
        row=self.row();row["binders"][0]["domain_node"]=False
        with self.assertRaises(RuntimeError):receipts.validate_statement_encoding(row)

    def test_incomplete_constructor_rejected(self):
        row=self.row();row["type_expression"]["nodes"][1].pop()
        with self.assertRaises(RuntimeError):receipts.validate_statement_encoding(row)

    def test_unbound_root_rejected(self):
        row=self.row();row["type_expression"]["root"]=0
        with self.assertRaises(RuntimeError):receipts.validate_statement_encoding(row)

    def test_unknown_encoding_rejected(self):
        row=self.row();row["type_expression_format"]="unknown"
        with self.assertRaises(RuntimeError):receipts.validate_statement_encoding(row)

    def test_repr_dag_confusion_rejected(self):
        row=self.row();row["type_expression_format"]="repr-v1"
        with self.assertRaises(RuntimeError):receipts.validate_statement_encoding(row)


if __name__=="__main__":unittest.main()
