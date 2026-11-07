"""Guard lost obligations, legacy target ambiguity and false proof promotion."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec=importlib.util.spec_from_file_location("ledger",Path(__file__).with_name("obligation_dependencies.py"))
ledger=importlib.util.module_from_spec(spec);spec.loader.exec_module(ledger)


class ObligationControls(unittest.TestCase):
    def setUp(self):
        files=[f"A{i}.lean" for i in range(129)]
        statuses=["pending","joint-witness","joint-witness-target-failure","no-top-level-input-hypotheses","checked-joint-impossibility","pending-ro-v2"]
        self.rows=[dict(file=files[i%129],source_name=f"N.t{i}",signature_sha256=f"sig{i}",variable_context=[],visibility="private" if i==0 else "public",witness_status=statuses[i%6],owner="historical-owner",signature="exact signature") for i in range(792)]
        self.frozen=dict(base=ledger.census.BASE,theorem_count=792,modules=[dict(file=f) for f in files],declarations=self.rows,map_sha256="map")
        self.graph=dict(original_base=ledger.census.BASE,original_obligations=792,frozen_target_files=129,frozen_map_sha256="map",schema=1,kind=ledger.KIND,held_module=ledger.HELD,source_head="historical",targets=[dict(target=f,status="no-declared-path-to-held-module",path=None,unknown=[]) for f in files])

    def test_all_obligations_and_historical_fields_retained(self):
        result=ledger.join(self.frozen,self.graph,self.rows)
        self.assertEqual(result["original_obligations"],792)
        self.assertEqual({r["frozen"]["source_name"] for r in result["rows"]},{r["source_name"] for r in self.rows})
        for row in result["rows"]:
            self.assertIn(row["frozen"],self.rows)
            self.assertEqual(row["current_kernel_fidelity"],"pending")
            self.assertEqual(row["live_ownership"],"unverified")
            self.assertEqual(row["timing_hold"],"retained")
        self.assertEqual(sum(r["count"] for r in result["cross_counts"]),792)

    def test_removed_private_remains_pending_and_context_drift_visible(self):
        now=copy.deepcopy(self.rows[1:]);now[0]["variable_context"]=["changed"]
        result=ledger.join(self.frozen,self.graph,now)
        missing=[r for r in result["rows"] if r["current_lexical_status"]=="absent-upstream"]
        self.assertEqual(len(missing),1)
        self.assertEqual(missing[0]["frozen"]["witness_status"],"pending")
        self.assertEqual(result["lexical_statuses"]["header-or-context-drift"],1)

    def test_legacy_target_reports_rejected(self):
        del self.graph["targets"][0]["target"]
        with self.assertRaisesRegex(ValueError,"explicit target"):
            ledger.join(self.frozen,self.graph,self.rows)

    def test_dropped_duplicate_and_foreign_targets_rejected(self):
        for targets in (self.graph["targets"][:-1],self.graph["targets"]+[self.graph["targets"][0]],self.graph["targets"][:-1]+[dict(target="Foreign.lean")]):
            graph=copy.deepcopy(self.graph);graph["targets"]=targets
            with self.assertRaises(ValueError):ledger.join(self.frozen,graph,self.rows)

    def test_missing_or_duplicate_original_rejected(self):
        for rows in (self.rows[:-1],self.rows[:-1]+[self.rows[0]]):
            frozen=copy.deepcopy(self.frozen);frozen["declarations"]=rows
            with self.assertRaises(ValueError):ledger.join(frozen,self.graph,self.rows)

    def test_dependency_path_cannot_replace_identity(self):
        target=self.graph["targets"][0];target.update(status="declared-path-to-held-module",path=["Other.lean",ledger.HELD])
        with self.assertRaisesRegex(ValueError,"endpoints"):
            ledger.join(self.frozen,self.graph,self.rows)
        target["path"]=[target["target"],ledger.HELD]
        result=ledger.join(self.frozen,self.graph,self.rows)
        self.assertTrue(any(r["historical_header_dependency"]["status"]=="declared-path-to-held-module" for r in result["rows"]))

    def test_wrong_held_module_or_inconsistent_unknown_rejected(self):
        for field,value in (("held_module","Other.lean"),("kind","other"),("schema",2)):
            graph=copy.deepcopy(self.graph);graph[field]=value
            with self.assertRaisesRegex(ValueError,"wrong dependency"):
                ledger.join(self.frozen,graph,self.rows)
        self.graph["targets"][0]["unknown"]=["Missing.lean"]
        with self.assertRaisesRegex(ValueError,"no-path with unresolved"):
            ledger.join(self.frozen,self.graph,self.rows)

    def test_modules_without_named_theorems_are_not_dropped(self):
        rows=copy.deepcopy(self.rows)
        for row in rows:row["file"]="A0.lean"
        frozen=copy.deepcopy(self.frozen);frozen["declarations"]=rows
        result=ledger.join(frozen,self.graph,rows)
        self.assertEqual(len(result["modules"]),129)
        self.assertEqual(sum(m["original_declarations"]==0 for m in result["modules"]),128)
        self.assertEqual(sum(m["original_declarations"] for m in result["modules"]),792)
        self.graph["targets"][1]["unknown"]=["Unresolved.lean"]
        with self.assertRaisesRegex(ValueError,"no-path with unresolved"):
            ledger.join(frozen,self.graph,rows)

    def test_hash_pin_and_duplicate_json_keys_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/"input.json";path.write_text('{"x":1,"x":2}')
            with self.assertRaisesRegex(ValueError,"SHA256"):
                ledger.load_pinned(path,"wrong")
            with self.assertRaisesRegex(ValueError,"duplicate JSON"):
                ledger.load_pinned(path,ledger.sha(path.read_bytes()))


if __name__=="__main__":unittest.main()
