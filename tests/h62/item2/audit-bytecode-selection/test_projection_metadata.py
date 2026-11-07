"""Guard stale/missing projection records and registry guesses from acceptance."""
from pathlib import Path
import sys,json,copy,types,subprocess,unittest
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'scripts/h62/item2/audit-bytecode-selection'))
import projection_metadata as reader
import elaborated_census as generator
import kernel_metadata as metadata
import test_kernel_metadata as schema_fixtures

class ProjectionMetadataTests(unittest.TestCase):
    def fixture(self):
        target=schema_fixtures.MetadataSchemaTests().row();target.update(module='Solidity.Backend.AbiEntry.BoolBindingBodyInterface',kind='field',is_projection=True,interface_or_premises_module=True)
        pins={'fingerprint':'a'*64,'targets':{target['name']:metadata.observed_type(target)}}
        row={'fingerprint':pins['fingerprint'],'name':target['name'],'module':target['module'],'private':True,
             'type_expr':target['type_expr'],'level_params':[], 'metadata_status':'registered_projection_observed',
             'registry':{'ctor_name':'M.C.mk','num_params':1,'field_index':0,'from_class':False},
             'constructor':{'name':'M.C.mk','type_expr':'constructor expression','level_params':[],
                            'inductive':'M.C','num_params':1,'num_fields':1,'constructor_index':0},
             'inductive':{'name':'M.C','type_expr':'inductive expression','level_params':[]},
             'structure':{'name':'M.C','projections':[target['name']],
                          'parents':[{'structure':'M.P','projection':'M.C.toP','subobject':True}]}}
        return target,pins,row
    def log(self,pins,rows,count=None):
        return '\n'.join(['H62_PROJECTION_JSON '+json.dumps(r) for r in rows]+['H62_PROJECTION_DONE '+json.dumps({'fingerprint':pins['fingerprint'],'count':len(rows) if count is None else count})])
    def test_complete_metadata_retains_types_and_does_not_instantiate(self):
        target,pins,row=self.fixture();out=reader.read_projection_records(self.log(pins,[row]),pins)
        self.assertEqual(out['records'],[row]);self.assertTrue(out['observed_relations'][0]['registered_parameter_counts_match'])
        self.assertFalse(out['inherited_instantiation_accepted']);self.assertFalse(out['source_correspondence_established'])
        self.assertFalse(out['observed_relations'][0]['source_ownership_established'])
        out['records'][0]['structure']['parents'][0]['structure']='changed'
        self.assertEqual(row['structure']['parents'][0]['structure'],'M.P')
        row['registry']['field_index']=2
        self.assertFalse(reader.read_projection_records(self.log(pins,[row]),pins)['observed_relations'][0]['registered_index_within_constructor'])
    def test_refuse_stale_scalar_types_missing_duplicate_and_post_terminal(self):
        target,pins,row=self.fixture()
        for key,value in [('type_expr','stale'),('module','wrong'),('private',1),('level_params',['u']),('fingerprint','b'*64)]:
            bad=copy.deepcopy(row);bad[key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):reader.read_projection_records(self.log(pins,[bad]),pins)
        for log in ['',self.log(pins,[]),self.log(pins,[row,row]),self.log(pins,[row],True),self.log(pins,[row])+'\nH62_PROJECTION_JSON '+json.dumps(row)]:
            with self.subTest(log=log[:40]),self.assertRaises(ValueError):reader.read_projection_records(log,pins)
        bad=copy.deepcopy(row);bad['registry']['num_params']=True
        with self.assertRaises(ValueError):reader.read_projection_records(self.log(pins,[bad]),pins)
        bad=copy.deepcopy(row);bad['constructor']['name']='another'
        with self.assertRaises(ValueError):reader.read_projection_records(self.log(pins,[bad]),pins)
    def test_missing_registry_remains_observed_gap_not_field_exclusion(self):
        target,pins,row=self.fixture();row.update(metadata_status='no_registered_projection',registry=None,constructor=None,inductive=None,structure=None)
        out=reader.read_projection_records(self.log(pins,[row]),pins)
        self.assertEqual(len(out['records']),1);self.assertIsNone(out['observed_relations'][0]['registered_parameter_counts_match'])
        bad=copy.deepcopy(row);bad['metadata_status']='registered_projection_observed'
        with self.assertRaises(ValueError):reader.read_projection_records(self.log(pins,[bad]),pins)
    def test_renderer_uses_registry_not_prefix_and_preserves_old_template(self):
        target,pins,row=self.fixture();program,manifest=generator.projection_inspection_source(ROOT,[target])
        self.assertIn('env.getProjectionFnInfo? name',program);self.assertIn('env.find? projection.ctorName',program)
        self.assertIn('List Lean.Name',program);self.assertNotIn('List Name',program)
        self.assertIn('registryValue).isNone',program);self.assertIn('classField.fromClass',program)
        self.assertFalse(manifest['inherited_instantiation_accepted']);self.assertFalse(manifest['kernel_accepted'])
        old=types.ModuleType('previous_inspector');old.__file__=str(ROOT/'scripts/h62/item2/audit-bytecode-selection/elaborated_census.py')
        raw=subprocess.check_output(['git','show','50fd0831998f25d1b270d82018b6d8179e3459a8:scripts/h62/item2/audit-bytecode-selection/elaborated_census.py'],cwd=ROOT)
        exec(compile(raw,old.__file__,'exec'),old.__dict__)
        self.assertEqual(generator.TEMPLATE,old.TEMPLATE)
        self.assertEqual(generator.inspection_source(['M'],'f'),old.inspection_source(['M'],'f'))
        target['is_projection']=False;target['kind']='theorem'
        with self.assertRaises(ValueError):generator.projection_inspection_source(ROOT,[target])

if __name__=='__main__':unittest.main()
