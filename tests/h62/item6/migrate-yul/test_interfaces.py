import copy,importlib.util,json,pathlib,tempfile,unittest
p=pathlib.Path(__file__).resolve().parents[4]/'scripts/h62/item6/migrate-yul/interfaces.py'
spec=importlib.util.spec_from_file_location('interfaces',p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class Snapshots(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.root=pathlib.Path(self.tmp.name)
        self.mod='Test.Module';self.name=m.module_name(self.mod)
        self.header=dict(record='header',schema=2,module=self.name,import_level='private',import_all=True,expected_constants=1,extra_codegen_count=0,extra_codegen_names=[])
        self.row=dict(record='declaration',module=self.name,name=m.module_name('Test.theorem'),display_name='Test.theorem',kind='theorem',private=False,shared=False,authoritative_origin=self.name,universes=[],unsafe=False,partial=False,type='["sort",["zero"]]',payload={'proof':'["nat",0]'})
        self.footer=dict(record='complete',module=self.name,count=1,axiom_union=[])
        self.raw=self.root/'snapshot.jsonl.partial';self.write([self.header,self.row,self.footer])
    def tearDown(self):self.tmp.cleanup()
    def write(self,rows):self.raw.write_text(''.join(json.dumps(r)+'\n' for r in rows))
    def probe(self,command=None,output_hash=None):
        helper=self.root/'tests/h62/item6/migrate-yul/ExportInterfaces.lean';helper.parent.mkdir(parents=True,exist_ok=True);helper.write_text('unit-test source binding')
        bound={str(helper):m.digest(helper)}
        cmd=command or ['lean','--run',str(helper),self.mod,str(self.raw)]
        report=dict(status='pass',kind='probe',repository=str(self.root),modules=[dict(exit=0,stop=None,command=cmd)],probe_sources_before=bound,probe_sources_after=bound,source_check_before={'status':'pass'},source_check_after={'status':'pass'},probe_output_freshness_required=True,probe_outputs_after={str(self.raw):{'sha256':output_hash or m.digest(self.raw),'bytes':self.raw.stat().st_size}},lean='unit-test',lake='unit-test')
        path=self.root/'probe.json';path.write_text(json.dumps(report));return path
    def test_incomplete_rejected(self):
        self.write([self.header,self.row])
        with self.assertRaises(ValueError):m.inspect_snapshot(self.raw,self.mod)
    def test_wrong_count_rejected(self):
        footer=dict(self.footer,count=2);self.write([self.header,self.row,footer])
        with self.assertRaises(ValueError):m.inspect_snapshot(self.raw,self.mod)
    def test_duplicate_declaration_rejected(self):
        self.write([self.header,self.row,self.row,self.footer])
        with self.assertRaises(ValueError):m.inspect_snapshot(self.raw,self.mod)
    def test_wrong_module_rejected(self):
        with self.assertRaises(ValueError):m.inspect_snapshot(self.raw,'Wrong.Module')
    def test_proof_change_separated_from_signature(self):
        old=m.inspect_snapshot(self.raw,self.mod)['declarations'][0]
        row=copy.deepcopy(self.row);row['payload']['proof']='["nat",1]';self.write([self.header,row,self.footer])
        new=m.inspect_snapshot(self.raw,self.mod)['declarations'][0]
        self.assertEqual(old['signature_sha256'],new['signature_sha256']);self.assertNotEqual(old['proof_sha256'],new['proof_sha256'])
    def test_shared_declaration_retained(self):
        row=dict(self.row,shared=True,authoritative_origin=m.module_name('Earlier.Module'));self.write([self.header,row,self.footer])
        self.assertTrue(m.inspect_snapshot(self.raw,self.mod)['declarations'][0]['shared'])
    def test_header_ir_drift_reported(self):
        old=m.inspect_snapshot(self.raw,self.mod);new=copy.deepcopy(old)
        new['header']['extra_codegen_count']=1;new['header']['extra_codegen_names']=[m.module_name('IR.extra')]
        result=m.compare_snapshots(old,new)
        self.assertEqual(result['status'],'differences_require_review');self.assertIn('extra_codegen_names',result['header_changes'])
    def test_authoritative_origin_drift_reported(self):
        old=m.inspect_snapshot(self.raw,self.mod);new=copy.deepcopy(old)
        new['declarations'][0]['shared']=True;new['declarations'][0]['authoritative_origin']=m.module_name('Earlier.Module')
        result=m.compare_snapshots(old,new)
        self.assertEqual(result['status'],'differences_require_review');self.assertEqual(len(result['changes']['provenance']),1)
    def test_unrelated_probe_rejected(self):
        probe=self.probe(['lean','--run','other.lean','--self-test'])
        with self.assertRaises(ValueError):m.seal(self.raw,probe,self.mod,self.root/'sealed.json')
    def test_modified_output_rejected(self):
        probe=self.probe(output_hash='0'*64)
        with self.assertRaises(ValueError):m.seal(self.raw,probe,self.mod,self.root/'sealed.json')
    def test_passing_bound_output_compression_verified(self):
        probe=self.probe();result=m.seal(self.raw,probe,self.mod,self.root/'sealed.json')
        self.assertFalse(self.raw.exists());self.assertTrue(pathlib.Path(result['compressed']).is_file())
        self.assertEqual(len(result['declarations']),1)
    def test_failed_probe_rejected(self):
        probe=self.probe();report=json.loads(probe.read_text());report['status']='fail';probe.write_text(json.dumps(report))
        with self.assertRaises(ValueError):m.seal(self.raw,probe,self.mod,self.root/'sealed.json')
    def use_dag(self):
        self.header.update(schema=3,expression_encoding='canonical expr-dag-v1 JSON text, metadata erased only')
        self.row['type']=m.canonical(m.expr_dag.from_tree(self.row['type']))
        self.row['payload']['proof']=m.canonical(m.expr_dag.from_tree(self.row['payload']['proof']))
        self.write([self.header,self.row,self.footer])
    def dag_probe(self):
        probe=self.probe();report=json.loads(probe.read_text())
        helper=self.root/'tests/h62/item6/migrate-yul/ExportInterfacesDag.lean';helper.write_text('unit-test DAG source binding')
        report['modules'][0]['command']=['lean','--run',str(helper),self.mod,str(self.raw)]
        report['probe_sources_before']={str(helper):m.digest(helper)};report['probe_sources_after']=dict(report['probe_sources_before'])
        probe.write_text(json.dumps(report));return probe
    def test_dag_helper_schema_binding(self):
        self.use_dag();probe=self.probe()
        with self.assertRaises(ValueError):m.seal(self.raw,probe,self.mod,self.root/'sealed.json')
    def test_tree_schema_rejects_dag_helper(self):
        probe=self.dag_probe()
        with self.assertRaises(ValueError):m.seal(self.raw,probe,self.mod,self.root/'sealed.json')
    def test_passing_bound_dag_snapshot(self):
        self.use_dag();probe=self.dag_probe();result=m.seal(self.raw,probe,self.mod,self.root/'sealed.json')
        self.assertEqual(result['schema'],3);self.assertEqual(len(result['declarations']),1)
    def test_dag_type_cycle_rejected(self):
        self.use_dag();self.row['type']='["expr-dag-v1",0,[["app",0,0]]]';self.write([self.header,self.row,self.footer])
        with self.assertRaises(ValueError):m.inspect_snapshot(self.raw,self.mod)
    def test_dag_recursor_rule_validated(self):
        self.use_dag();self.row['kind']='recursor';self.row['payload']={'rules':[{'rhs':'["expr-dag-v1",0,[["fvar","bad"]]]'}]};self.write([self.header,self.row,self.footer])
        with self.assertRaises(ValueError):m.inspect_snapshot(self.raw,self.mod)
    def test_cross_encoding_comparison_rejected(self):
        old=m.inspect_snapshot(self.raw,self.mod);self.use_dag();new=m.inspect_snapshot(self.raw,self.mod)
        with self.assertRaises(ValueError):m.compare_snapshots(old,new)
if __name__=='__main__':unittest.main()
