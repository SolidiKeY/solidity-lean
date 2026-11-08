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
    def report_fixture(self, row, identity="one", status="proved"):
        return {"id":identity,"receipt":{key:"a"*64 for key in
            ("artifact_manifest_sha256","source_sha256","output_sha256","native_result_sha256","seal_sha256")},
            "entries":[{"target":observed_type(row),"helper":"Audit.h","status":status,
                        "reason":"" if status=="proved" else "no supported default"}]}
    def projection_report_fixture(self):
        row=self.row();row.update(name="N.Cert.ok",user_name="N.Cert.ok",private=False,
            original_kind="Lean.ConstantKind.thm",is_theorem=True,is_projection=True,kind="field",
            body_status="proof body intentionally omitted; declaration retained")
        return row,self.report_fixture(row)
    def test_hypothesis_reports_keep_checked_field_reports_without_theorem_source_credit(self):
        row,artifact=self.projection_report_fixture();other=self.row();other['name']='unreported'
        result=hypothesis_report_index([row,other],{"M":[]},[artifact]);entry=next(v for v in result['declarations'] if v['name']==row['name'])
        self.assertTrue(entry['is_projection']);self.assertEqual(entry['record_kind'],'field')
        self.assertTrue(entry['original_theorem']);self.assertEqual(entry['report_status'],'reported_proof')
        self.assertEqual(entry['source_ids'],[]);self.assertEqual(entry['accounting_status'],'unmatched')
        self.assertEqual(result['summary']['distinct_reported_proof_targets'],1)
        self.assertEqual(result['summary']['unreported_records'],1)
        for flag in ['proof_acceptance_established','joint_witness_established','statement_correspondence_established','inherited_obligations_established','global_witness_ledger_linked']:
            self.assertFalse(entry[flag])
    def test_hypothesis_reports_still_reject_data_projections_and_unrelated_proof_constants(self):
        row,artifact=self.projection_report_fixture()
        for changes in [{'original_kind':'Lean.ConstantKind.defn','is_theorem':False,'proof_type':False,'body_status':'no available value'},
                        {'original_kind':'Lean.ConstantKind.defn','is_theorem':False,'is_projection':False,'kind':'constant'}]:
            bad=copy.deepcopy(row);bad.update(changes);a=self.report_fixture(bad)
            with self.subTest(changes=changes),self.assertRaises(ValueError):hypothesis_report_index([bad],{'M':[]},[a])
    def test_hypothesis_field_reports_deduplicate_and_refuse_stale_snapshots(self):
        row,a=self.projection_report_fixture();b=copy.deepcopy(a);b['id']='repeat'
        result=hypothesis_report_index([row],{'M':[]},[a,b])
        self.assertEqual(result['summary']['artifact_reports'],2);self.assertEqual(result['summary']['distinct_reported_proof_targets'],1)
        self.assertEqual(result,hypothesis_report_index([row],{'M':[]},[b,a]))
        for change in [{'type_expr':'stale'},{'private':True},{'level_params':['u']}]:
            bad=copy.deepcopy(a);bad['entries'][0]['target'].update(change)
            with self.subTest(change=change),self.assertRaises(ValueError):hypothesis_report_index([row],{'M':[]},[bad])
        saved=copy.deepcopy(result);a['entries'][0]['target']['type_expr']='mutation';self.assertEqual(result,saved)

    def federation_fixture(self):
        base=self.ranged_row();field,_=self.projection_report_fixture()
        field.update(module='Supplement',name='Supplement.Cert.ok',manifest_sha256='supplement-fingerprint')
        return [dict(id='base',rows=[base],mapping={'M':[self.source_candidate(base)]},artifacts=[]),
                dict(id='supplement',rows=[field],mapping={'Supplement':[]},artifacts=[self.report_fixture(field,'supplement')])]
    def test_federation_preserves_fingerprints_reports_and_base_gaps(self):
        parts=self.federation_fixture();result=federated_hypothesis_reports(parts)
        self.assertEqual(result['summary'],{'slices':2,'disjoint_records':2,'disjoint_module_scopes':2,'reported_proof_targets':1,'unreported_records':1})
        self.assertEqual([p['inspection_fingerprint'] for p in result['inspection_slices']],['fingerprint','supplement-fingerprint'])
        first,second=[p['index']['declarations'][0] for p in result['inspection_slices']]
        self.assertEqual(first['report_status'],'no_report');self.assertEqual(second['report_status'],'reported_proof')
        self.assertEqual(second['source_ids'],[])
        for key in ['coherent_environment_established','proof_acceptance_established','source_correspondence_established','full_census_accepted','global_witness_ledger_linked']:
            self.assertFalse(result[key])
        self.assertEqual(result,federated_hypothesis_reports(list(reversed(parts))))
        for part,packet in zip(parts,result['inspection_slices']):
            self.assertEqual(packet['index']['declarations'][0]['record_sha256'],observed_type(part['rows'][0])['record_sha256'])
        with_empty=copy.deepcopy(parts);with_empty[0]['mapping']['Empty']=[]
        empty_result=federated_hypothesis_reports(with_empty)
        self.assertEqual(empty_result['inspection_slices'][0]['module_scope'],['Empty','M'])
        self.assertEqual(empty_result['summary']['disjoint_module_scopes'],3)
        saved=copy.deepcopy(result);parts[1]['rows'][0]['type_expr']='changed';self.assertEqual(result,saved)
    def test_federation_refuses_overlap_ids_empty_and_mixed_contexts(self):
        parts=self.federation_fixture()
        for change in ['id','name','module','mapping']:
            bad=copy.deepcopy(parts)
            if change=='id':bad[1]['id']=bad[0]['id']
            elif change=='name':bad[1]['rows'][0]['name']=bad[0]['rows'][0]['name']
            elif change=='module':bad[1]['rows'][0]['module']='M'
            else:bad[1]['mapping']['M']=[]
            with self.subTest(change=change),self.assertRaises(ValueError):federated_hypothesis_reports(bad)
        with self.assertRaises(ValueError):federated_hypothesis_reports([])
        with self.assertRaises(ValueError):federated_hypothesis_reports([dict(id='empty',rows=[],mapping={},artifacts=[])])
        mixed=dict(id='mixed',rows=parts[0]['rows']+parts[1]['rows'],mapping=dict(parts[0]['mapping'],**parts[1]['mapping']),artifacts=[])
        with self.assertRaises(ValueError):federated_hypothesis_reports([mixed])

    def test_hypothesis_reports_deduplicate_successes_and_retain_failures_and_gaps(self):
        row=self.ranged_row();other=self.row();other.update(name="unreported",user_name="unreported",declaration_range=None)
        mapping={"M":[self.source_candidate(row)]}
        artifacts=[self.report_fixture(row,"old","unsupported-default"),self.report_fixture(row,"new"),self.report_fixture(row,"repeat")]
        result=hypothesis_report_index([row,other],mapping,artifacts)
        self.assertEqual(result['summary'],{'kernel_records':2,'source_candidates':1,'artifact_reports':3,'distinct_reported_proof_targets':1,'unsupported_only_targets':0,'unreported_records':1,'unreported_by_record_kind':{'theorem':1}})
        entry=next(r for r in result['declarations'] if r['name']==row['name'])
        self.assertTrue(entry['private']);self.assertEqual(entry['report_status'],'reported_proof')
        self.assertEqual([r['reported_status'] for r in entry['hypothesis_reports']],['proved','unsupported-default','proved'])
        self.assertTrue(all(not r['joint_witness_established'] and not r['proof_acceptance_established'] and not r['inherited_obligations_established'] and not r['global_witness_ledger_linked'] for r in result['declarations']))
        self.assertFalse(result['source_correspondence_established']);self.assertFalse(result['full_census_accepted'])
        self.assertEqual(result,hypothesis_report_index([other,row],mapping,list(reversed(artifacts))))
        before=copy.deepcopy(result);artifacts[0]['entries'][0]['target']['type_expr']='changed';mapping['M'][0]['kernel_names'].append('changed')
        self.assertEqual(result,before)
    def test_hypothesis_reports_reject_stale_type_private_and_unknown_targets(self):
        row=self.ranged_row();mapping={"M":[self.source_candidate(row)]}
        for changes in ({'type_expr':'forged'},{'private':False},{'private':1},{'proof_type':1},{'name':'absent'},{'name':[]}):
            artifact=self.report_fixture(row);artifact['entries'][0]['target'].update(changes)
            with self.subTest(changes=changes),self.assertRaises(ValueError):hypothesis_report_index([row],mapping,[artifact])
        with self.assertRaises(ValueError):hypothesis_report_index([row],[],[])
    def test_hypothesis_reports_refuse_duplicate_id_target_helper_and_bad_outcome(self):
        row=self.ranged_row();mapping={"M":[self.source_candidate(row)]};artifact=self.report_fixture(row)
        with self.assertRaises(ValueError):hypothesis_report_index([row],mapping,[artifact,copy.deepcopy(artifact)])
        bad=copy.deepcopy(artifact);bad['entries']*=2
        with self.assertRaises(ValueError):hypothesis_report_index([row],mapping,[bad])
        for changes in ({'status':'uninhabited'},{'status':[]},{'reason':'proof was assumed'},{'status':'unsupported-default','reason':''}):
            bad=copy.deepcopy(artifact);bad['entries'][0].update(changes)
            with self.subTest(changes=changes),self.assertRaises(ValueError):hypothesis_report_index([row],mapping,[bad])
        for change in (None,'x'*64,'a'*63):
            bad=copy.deepcopy(artifact);bad['receipt']['output_sha256']=change
            with self.subTest(change=change),self.assertRaises(ValueError):hypothesis_report_index([row],mapping,[bad])
    def test_hypothesis_reports_keep_unsupported_unreported_and_inherited_uninstantiated(self):
        row=self.ranged_row();row['parents']=[{'structure':'Parent','projection':'toParent','subobject':True}]
        mapping={"M":[self.source_candidate(row)]};artifact=self.report_fixture(row,status='unsupported-default')
        result=hypothesis_report_index([row],mapping,[artifact]);entry=result['declarations'][0]
        self.assertEqual(entry['report_status'],'reported_unsupported_attempts');self.assertEqual(entry['parent_metadata'],row['parents'])
        self.assertFalse(entry['inherited_obligations_established'])
        self.assertEqual(hypothesis_report_index([row],mapping,[])['declarations'][0]['report_status'],'no_report')
        entry['parent_metadata'][0]['structure']='changed';self.assertEqual(row['parents'][0]['structure'],'Parent')

    def test_binder_join_keeps_order_private_heads_and_unresolved_categories(self):
        row=self.row(); row["binders"]=[
            {"name":"x","binder_info":"Lean.BinderInfo.implicit","type":"N.P", "proof_binder":False,"head_constant":"N.P"},
            {"name":"h","binder_info":"Lean.BinderInfo.default","type":"x = x", "proof_binder":True,"head_constant":"Eq"},
            {"name":"p","binder_info":"Lean.BinderInfo.default","type":"x", "proof_binder":True,"head_constant":None}]
        parent=self.row();parent.update(name="N.P",user_name="N.P",private=False)
        result=binder_metadata([row,parent]);entry=next(d for d in result["declarations"] if d["name"]==row["name"])
        self.assertEqual([b["index"] for b in entry["binders"]],[0,1,2])
        self.assertEqual([b["preceding_binder_count"] for b in entry["binders"]],[0,1,2])
        self.assertEqual([b["head_status"] for b in entry["binders"]],["supplied_record_present","not_in_supplied_records","no_constant_head_observed"])
        self.assertEqual([b["binder"] for b in entry["binders"]],row["binders"])
        self.assertTrue(entry["private"])
        self.assertEqual(result["head_records"][0]["name"],"N.P")
        self.assertFalse(any(b["instantiated_type_accepted"] or b["joint_witness_established"] for b in entry["binders"]))
        self.assertTrue(all(b["premise_role"].startswith("unclassified;") for b in entry["binders"]))
        original=copy.deepcopy(result);row["binders"][0]["type"]="changed"
        self.assertEqual(result,original)
        result["head_records"][0]["binders"].append({"external":"mutation"})
        self.assertEqual(parent["binders"],[])
    def test_binder_join_accounts_zero_binders_and_rejects_duplicate_heads(self):
        row=self.row();result=binder_metadata([row])
        self.assertEqual(len(result["declarations"]),1)
        self.assertEqual(result["declarations"][0]["binder_count"],0)
        self.assertEqual(result["head_records"],[])
        with self.assertRaises(ValueError):binder_metadata([row,row])
        other=self.row();other.update(name="different",manifest_sha256="different")
        with self.assertRaises(ValueError):binder_metadata([row,other])
    def test_binder_join_is_order_independent_and_does_not_collapse_repeated_binders(self):
        row=self.row();row["binders"]=[{"name":"h","binder_info":"Lean.BinderInfo.default","type":"True","proof_binder":True,"head_constant":"True"}]*2
        other=self.row();other.update(name="True",user_name="True")
        a=binder_metadata([row,other]);b=binder_metadata([other,row])
        self.assertEqual(a,b)
        entry=next(d for d in a["declarations"] if d["name"]==row["name"])
        self.assertEqual(entry["binder_count"],2)
        self.assertEqual([x["index"] for x in entry["binders"]],[0,1])

    def source_candidate(self, row, start=0):
        signature="theorem t : True "
        return {"name_candidate":row["user_name"],"kind":"theorem","name_line":1,"name_column":0,"byte_start":start,"byte_end":start+20,"signature":signature,"signature_sha256":hashlib.sha256(signature.encode()).hexdigest(),"kernel_names":[row["name"]],"match_count":1,"mapping_status":"unique"}
    def ranged_row(self):
        row=self.row();row["declaration_range"].update(selection_column=0,selection_end_line=1,selection_end_column=1,position_units="one-based lines; zero-based Unicode codepoint columns")
        return row
    def test_source_graph_preserves_both_sides_and_private_candidates(self):
        row=self.ranged_row();other=self.row();other.update(name="unmatched",user_name="unmatched")
        source=self.source_candidate(row);missing=self.source_candidate(row,50);missing.update(name_candidate="absent",kernel_names=[],match_count=0,mapping_status="unmatched")
        result=source_candidate_graph([row,other],{"M":[source,missing]})
        self.assertEqual(len(result["records"]),2);self.assertEqual(len(result["sources"]),2)
        self.assertEqual([r["accounting_status"] for r in result["sources"]],["one_to_one_candidate","unmatched"])
        self.assertTrue(result["records"][0]["private"])
        self.assertFalse(any(r["statement_correspondence_established"] or r["joint_witness_established"] for r in result["records"]))
        before=copy.deepcopy(result);source["kernel_names"].append("changed");self.assertEqual(result,before)
        result["sources"][0]["source"]["signature"]="mutated";self.assertNotEqual(source["signature"],"mutated")
    def test_source_graph_detects_shared_target_and_is_deterministic(self):
        row=self.ranged_row();a=self.source_candidate(row);b=self.source_candidate(row,30)
        result=source_candidate_graph([row],{"M":[b,a]})
        self.assertEqual(result,source_candidate_graph([row],{"M":[a,b]}))
        self.assertTrue(all(r["accounting_status"]=="ambiguous_candidate" for r in result["sources"]))
        self.assertEqual(result["records"][0]["accounting_status"],"ambiguous_candidate")
    def test_source_graph_refuses_stale_or_forged_edges_and_duplicate_identity(self):
        row=self.ranged_row();source=self.source_candidate(row)
        for changes in ({"signature_sha256":"0"*64},{"kernel_names":["missing"]},{"match_count":True},{"name_column":1},{"mapping_status":"unmatched"}):
            bad=dict(source,**changes)
            with self.subTest(changes=changes),self.assertRaises(ValueError):source_candidate_graph([row],{"M":[bad]})
        with self.assertRaises(ValueError):source_candidate_graph([row],{"M":[source,source]})
        with self.assertRaises(ValueError):source_candidate_graph([row,row],{"M":[source]})

    def test_source_graph_one_source_multiple_records_and_non_theorem_refusal(self):
        row=self.ranged_row();other=copy.deepcopy(row);other["name"]="different_kernel_identity"
        source=self.source_candidate(row);source.update(kernel_names=sorted([row["name"],other["name"]]),match_count=2,mapping_status="ambiguous")
        result=source_candidate_graph([row,other],{"M":[source]})
        self.assertEqual(result["sources"][0]["accounting_status"],"ambiguous_candidate")
        self.assertTrue(all(r["accounting_status"]=="ambiguous_candidate" for r in result["records"]))
        row.update(original_kind="Lean.ConstantKind.defn",is_theorem=False,kind="constant",body_status="no available value")
        self.assertEqual(validate_record(row)["kind"],"constant")
        with self.assertRaises(ValueError):source_candidate_graph([row],{"M":[self.source_candidate(row)]})

    def test_snapshot_bindings_keep_utf8_offsets_and_legacy_positions(self):
        from census import declarations
        raw="-- α prefix\nnamespace N\nprivate theorem π (h : True) : True := h\nend N\n".encode()
        candidate=declarations(raw.decode())[0]
        self.assertGreater(candidate['byte_start'],len(raw[:candidate['byte_start']].decode()))
        self.assertEqual(candidate['name_column'],raw.decode().splitlines()[2].index('π'))
        result=source_snapshot_bindings({'M':[candidate]},{'M':raw})
        bound=result['modules'][0]['candidates'][0]
        self.assertEqual(bound['name_position_status'],'supplied_and_reproduced')
        self.assertFalse(bound['statement_correspondence_established'])
        legacy=copy.deepcopy(candidate);legacy.pop('name_line');legacy.pop('name_column')
        old=source_snapshot_bindings({'M':[legacy]},{'M':raw})['modules'][0]['candidates'][0]
        self.assertEqual(old['name_position_status'],'reproduced_from_snapshot')
        self.assertEqual((old['name_line'],old['name_column']),(candidate['name_line'],candidate['name_column']))
        saved=copy.deepcopy(result);candidate['signature']='changed';self.assertEqual(result,saved)
    def test_snapshot_bindings_refuse_forged_hashes_and_context(self):
        from census import declarations
        raw=b'theorem t : True := True.intro\n';candidate=declarations(raw.decode())[0]
        for changes in ({'signature':'theorem t : False ','signature_sha256':hashlib.sha256(b'theorem t : False ').hexdigest()},{'preceding_context_sha256':'0'*64},{'name_column':True},{'byte_start':False},{'name_line':2}):
            with self.subTest(changes=changes),self.assertRaises(ValueError):source_snapshot_bindings({'M':[dict(candidate,**changes)]},{'M':raw})
        with self.assertRaises(ValueError):source_snapshot_bindings({'M':[candidate]},{'M':b'-- different context\n'+raw})
    def test_snapshot_bindings_require_complete_unique_membership(self):
        from census import declarations
        raw=b'theorem a : True := True.intro\ntheorem b : True := True.intro\n';rows=declarations(raw.decode())
        with self.assertRaises(ValueError):source_snapshot_bindings({'M':rows[:1]},{'M':raw})
        with self.assertRaises(ValueError):source_snapshot_bindings({'M':rows+[rows[0]]},{'M':raw})
        with self.assertRaises(ValueError):source_snapshot_bindings({'M':rows},{'N':raw})
        self.assertEqual(source_snapshot_bindings({'M':rows[::-1]},{'M':raw}),source_snapshot_bindings({'M':rows},{'M':raw}))
        empty=source_snapshot_bindings({'Empty':[]},{'Empty':b'namespace Empty\nend Empty\n'})
        self.assertEqual(empty['modules'][0]['candidates'],[])

    def obligation_fixture(self):
        from census import declarations
        raw=b'private theorem t (h : True) : True := h\n';source=declarations(raw.decode())[0]
        row=self.ranged_row();row.update(user_name=source['name_candidate'])
        row['declaration_range'].update(selection_column=source['name_column'],selection_end_column=source['name_column']+1)
        row['binders']=[{'name':'h','binder_info':'Lean.BinderInfo.default','type':'True','proof_binder':True,'head_constant':'True'}]
        inspected=dict(source,kernel_names=[row['name']],match_count=1,mapping_status='unique')
        unseen=b'theorem u : True := True.intro\n'
        return {'M':[source],'Unseen':declarations(unseen.decode())},{'M':raw,'Unseen':unseen},row,{'M':[inspected]}
    def test_obligation_inventory_distinguishes_missing_types_from_observed_binders(self):
        mapping,sources,row,inspected=self.obligation_fixture()
        result=source_obligation_inventory(mapping,sources,[row],inspected)
        seen,unseen=result['obligations']
        self.assertEqual(seen['inspection_status'],'one_to_one_candidate')
        self.assertEqual(seen['candidate_types'][0]['raw_binder_count'],1)
        self.assertEqual(seen['candidate_types'][0]['observed_proof_binder_count'],1)
        self.assertTrue(seen['candidate_types'][0]['observed_type']['private'])
        self.assertEqual(unseen['inspection_status'],'module_uninspected')
        self.assertEqual(unseen['candidate_types'],[])
        self.assertTrue(all(not o['statement_correspondence_established'] and not o['joint_witness_established'] for o in result['obligations']))
        zero=copy.deepcopy(row);zero['binders']=[]
        measured=source_obligation_inventory(mapping,sources,[zero],inspected)['obligations']
        self.assertEqual(measured[0]['candidate_types'][0]['raw_binder_count'],0)
        self.assertEqual(measured[1]['candidate_types'],[])
        before=copy.deepcopy(result);row['binders'][0]['type']='changed';mapping['M'][0]['signature']='changed'
        self.assertEqual(result,before)
    def test_obligation_inventory_retains_ambiguous_types_and_unmatched_records(self):
        mapping,sources,row,inspected=self.obligation_fixture();other=copy.deepcopy(row);other['name']='second'
        inspected['M'][0].update(kernel_names=sorted([row['name'],other['name']]),match_count=2,mapping_status='ambiguous')
        extra=self.row();extra.update(name='extra',user_name='extra')
        result=source_obligation_inventory(mapping,sources,[row,other,extra],inspected)
        self.assertEqual(result['obligations'][0]['inspection_status'],'ambiguous_candidate')
        self.assertEqual(len(result['obligations'][0]['candidate_types']),2)
        self.assertEqual(next(r for r in result['kernel_records'] if r['name']=='extra')['accounting_status'],'unmatched')
        self.assertEqual(len(result['kernel_records']),3)
    def test_obligation_inventory_refuses_mixed_scope_or_stale_type_edges(self):
        mapping,sources,row,inspected=self.obligation_fixture()
        with self.assertRaises(ValueError):source_obligation_inventory(mapping,sources,[row],{'Outside':[]})
        bad=copy.deepcopy(row);bad['module']='Outside'
        with self.assertRaises(ValueError):source_obligation_inventory(mapping,sources,[bad],inspected)
        inspected['M'][0]['name_column']+=1
        with self.assertRaises(ValueError):source_obligation_inventory(mapping,sources,[row],inspected)
    def test_obligation_inventory_is_deterministic(self):
        mapping,sources,row,inspected=self.obligation_fixture()
        self.assertEqual(source_obligation_inventory(mapping,sources,[row],inspected),source_obligation_inventory(dict(reversed(list(mapping.items()))),dict(reversed(list(sources.items()))),[row],inspected))

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



class ExpandedMetadataTests(unittest.TestCase):
    row = MetadataSchemaTests.row

    def expanded(self):
        row = self.row()
        row["body_status"] = "proof body intentionally omitted; declaration retained"
        row["declaration_range"].update(selection_column=2, selection_end_line=1,
            selection_end_column=3, position_units="one-based lines; zero-based Unicode codepoint columns")
        return row

    def test_expanded_positions_and_omitted_proof_constants(self):
        row = self.expanded()
        self.assertEqual(validate_record(row), row)
        row.update(is_theorem=False, kind="constant", original_kind="Lean.ConstantKind.defn")
        self.assertEqual(validate_record(row), row)
        row["body_expr"] = "unexpected proof"
        with self.assertRaises(ValueError): validate_record(row)

    def test_expanded_position_corruption_refused(self):
        changes = [{"selection_column": -1}, {"selection_end_line": 0},
                   {"selection_end_column": 1}, {"position_units": "bytes"},
                   {"selection_end_column": True}]
        for change in changes:
            row = self.expanded(); row["declaration_range"].update(change)
            with self.subTest(change=change), self.assertRaises(ValueError): validate_record(row)
        row = self.expanded(); row["declaration_range"].pop("selection_end_column")
        with self.assertRaises(ValueError): validate_record(row)

    def test_target_roster_is_partial_observation_not_linkage(self):
        row = self.expanded()
        report = selected_domains([row], {"helper": row["name"]})
        self.assertFalse(report[0]["witness_ledger_linked"])
        self.assertFalse(report[0]["establishes_original_conclusion"])
        self.assertEqual(report[0]["kernel_type"]["type_expr"], row["type_expr"])
        row["binders"].append({"ignored": "mutation"})
        self.assertEqual(report[0]["kernel_type"]["binders"], [])

    def test_missing_duplicate_and_non_theorem_roster_refused(self):
        row = self.expanded()
        for roster in ({}, {"a": "absent"}, {"a": row["name"], "b": row["name"]}, {"a": 1}):
            with self.subTest(roster=roster), self.assertRaises(ValueError): selected_domains([row], roster)
        row.update(is_theorem=False, kind="constant", original_kind="Lean.ConstantKind.defn")
        with self.assertRaises(ValueError): selected_domains([row], {"a": row["name"]})


class RecordPartitionTests(unittest.TestCase):
    row = MetadataSchemaTests.row

    def records(self):
        candidate=self.row()
        field=self.row();field.update(name="field",user_name="field",kind="field",is_projection=True)
        auxiliary=self.row();auxiliary.update(name="odd_auxiliary_name",user_name="odd_auxiliary_name",declaration_range=None)
        ranged=self.row();ranged.update(name="other",user_name="other")
        return [candidate,field,auxiliary,ranged]

    def test_exact_once_lossless_and_order_independent(self):
        rows=self.records();groups=partition_records(rows,[rows[0]["name"]])
        self.assertEqual({key:len(value) for key,value in groups.items()},
            {"supplied_source_candidate":1,"direct_field":1,"unattributed_no_range":1,"unmatched_range":1})
        flattened=[entry for group in groups.values() for entry in group]
        self.assertEqual({entry["record"]["name"] for entry in flattened},{row["name"] for row in rows})
        self.assertEqual(groups,partition_records(list(reversed(rows)),[rows[0]["name"]]))
        for entry in flattened:
            for flag in ("source_identity_established","statement_correspondence_established","inherited_obligations_established","witness_ledger_linked"):
                self.assertFalse(entry[flag])
        rows[0]["type_expr"]="mutated"
        self.assertEqual(groups["supplied_source_candidate"][0]["record"]["type_expr"],"closed type expression")

    def test_invalid_candidates_and_duplicate_records_refused(self):
        rows=self.records()
        for candidates in (["absent"],[rows[0]["name"]]*2,[rows[2]["name"]],"not a list"):
            with self.subTest(candidates=candidates),self.assertRaises(ValueError):partition_records(rows,candidates)
        with self.assertRaises(ValueError):partition_records(rows+[rows[0]],[])

    def test_projection_precedes_range_and_unknown_names_remain_unattributed(self):
        rows=self.records();rows[1]["declaration_range"]=None
        groups=partition_records(rows,[])
        self.assertEqual([e["record"]["name"] for e in groups["direct_field"]],["field"])
        self.assertEqual([e["record"]["name"] for e in groups["unattributed_no_range"]],["odd_auxiliary_name"])



class SourceRangeBindingTests(unittest.TestCase):
    def fixture(self, raw="α theorem 名 : True := by\n  trivial\n"):
        row=MetadataSchemaTests().ranged_row()
        row["declaration_range"].update(selection_column=10,selection_end_column=11)
        sources={"M":raw.encode()}
        return row,sources,{"M":hashlib.sha256(raw.encode()).hexdigest()}
    def test_unicode_selection_is_utf8_bytes_and_keeps_raw_type(self):
        row,sources,pins=self.fixture();packet=source_range_bindings([row],sources,pins)
        entry=packet["records"][0];selection=entry["range_bytes"]["selection"]
        self.assertEqual(selection["text"],"名")
        self.assertEqual(sources["M"][selection["byte_start"]:selection["byte_end"]],"名".encode())
        self.assertEqual(selection["byte_start"],11);self.assertEqual(selection["byte_end"],14)
        self.assertEqual(entry["observed_type"],observed_type(row))
        self.assertFalse(any(entry[k] for k in ["source_identity_established","statement_correspondence_established","inherited_obligations_established","joint_witness_established"]))
    def test_missing_and_legacy_ranges_are_not_selection_bindings(self):
        row,sources,pins=self.fixture();missing=copy.deepcopy(row);missing.update(name="missing",declaration_range=None)
        legacy=copy.deepcopy(row);legacy.update(name="legacy",declaration_range={"start_line":1,"end_line":2,"selection_line":1})
        packet=source_range_bindings([row,missing,legacy],sources,pins);by={r["observed_type"]["name"]:r for r in packet["records"]}
        self.assertEqual(by["missing"]["binding_status"],"no_declaration_range");self.assertIsNone(by["missing"]["range_bytes"])
        self.assertEqual(by["legacy"]["binding_status"],"line_range_only");self.assertIsNone(by["legacy"]["range_bytes"]["selection"])
        self.assertEqual(len(packet["records"]),3)
    def test_invalid_positions_pins_and_scope_fail_closed(self):
        row,sources,pins=self.fixture()
        for change in [{"end_line":99},{"selection_column":999,"selection_end_column":999}]:
            bad=copy.deepcopy(row);bad["declaration_range"].update(change)
            with self.subTest(change=change),self.assertRaises(ValueError):source_range_bindings([bad],sources,pins)
        with self.assertRaises(ValueError):source_range_bindings([row],{"M":sources["M"]+b"drift"},pins)
        with self.assertRaises(ValueError):source_range_bindings([row],sources,{"M":"g"*64})
        with self.assertRaises(ValueError):source_range_bindings([row],{"N":sources["M"]},{"N":pins["M"]})
    def test_multiline_crlf_unicode_separator_and_eof_positions(self):
        row,sources,pins=self.fixture("α\r\n名\u2028x\n")
        row["declaration_range"].update(start_line=1,end_line=3,selection_line=1,selection_column=1,selection_end_line=2,selection_end_column=2)
        entry=source_range_bindings([row],sources,pins)["records"][0]
        self.assertEqual(entry["range_bytes"]["selection"]["text"],"\r\n名\u2028")
        self.assertEqual(entry["range_bytes"]["line_byte_end"],len(sources["M"]))
        row["declaration_range"].update(selection_line=3,selection_column=0,selection_end_line=3,selection_end_column=0)
        self.assertEqual(source_range_bindings([row],sources,pins)["records"][0]["range_bytes"]["selection"]["text"],"")
    def test_ordering_uninspected_modules_and_mutation_isolation(self):
        row,sources,pins=self.fixture();other=copy.deepcopy(row);other["name"]="other";sources["Unseen"]=b"";pins["Unseen"]=hashlib.sha256(b"").hexdigest()
        packet=source_range_bindings([row,other],sources,pins)
        self.assertEqual(packet,source_range_bindings([other,row],dict(reversed(list(sources.items()))),dict(reversed(list(pins.items())))))
        self.assertEqual(packet["sources"][1]["supplied_records"],0)
        saved=copy.deepcopy(packet);row["binders"].append({"external":"mutation"});self.assertEqual(packet,saved)
        packet["records"][0]["observed_type"]["declaration_range"]["start_line"]=99
        self.assertEqual(other["declaration_range"]["start_line"],1)

if __name__ == "__main__":
    unittest.main()
