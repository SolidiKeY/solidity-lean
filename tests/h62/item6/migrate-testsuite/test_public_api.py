import copy,hashlib,importlib.util,json,sys,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'scripts/h62/item6/migrate-testsuite'))
spec=importlib.util.spec_from_file_location('public_api_report',ROOT/'scripts/h62/item6/migrate-testsuite/public-api-report.py');api=importlib.util.module_from_spec(spec);spec.loader.exec_module(api)
class InventoryControls(unittest.TestCase):
    def setUp(self):
        self.census={'owned':{'M':{}}}
        self.row={'module':'M','name':'N.match_1','internal':False,'kind':'definition','name_parts':['str',['anonymous'],'N.match_1'],'level_params':[],'type_sha256':'a'*64,'value_sha256':None}
        self.text=json.dumps(self.row)+'\n';self.manifest={'status':'pass','sha256':hashlib.sha256(self.text.encode()).hexdigest(),'declarations':1,'module_counts':{'M':1}}
        self.kernel={'module':'M','name':'N.match_1','name_parts':self.row['name_parts'],'category':'kernel','private':False,'internal':False}
        self.extra={'module':'M','name':'N.match_1._lambda_1','name_parts':['str',self.row['name_parts'],'_lambda_1'],'category':'compiler_extra','private':False,'internal':True}
        self.count={'module':'M','kernel':1,'compiler_extra':1}
    def run_report(self,rows=None,count=None,manifest=None,exit=0):
        lines=['H62-API '+json.dumps(r) for r in (rows if rows is not None else [self.kernel,self.extra])]
        if count is not False:lines+=['H62-API-MODULE '+json.dumps(count or self.count)]
        return api.report(self.census,self.text,manifest or self.manifest,lines,exit)
    def test_generated_and_compiler_names_are_retained(self):
        text,s=self.run_report();rows=[json.loads(v) for v in text.splitlines()]
        self.assertEqual(len(rows),2);self.assertEqual(s['exclusions'],0)
        extra=next(r for r in rows if r['category']=='compiler_extra')
        self.assertIsNone(extra['old_signature']);self.assertIsNone(extra['new_signature']);self.assertEqual(extra['signature_status'],'compiler_extra_signature_unresolved')
        self.assertEqual(s['implemented_shims'],[])
    def test_failed_compiler_cannot_accept_output(self):
        with self.assertRaisesRegex(ValueError,'INVENTORY_COMPILER_FAILED'):self.run_report(exit=1)
    def test_snapshot_tampering_refused(self):
        m=copy.deepcopy(self.manifest);m['sha256']='b'*64
        with self.assertRaisesRegex(ValueError,'UNVERIFIED_SIGNATURE_SNAPSHOT'):self.run_report(manifest=m)
    def test_missing_generated_kernel_refused(self):
        with self.assertRaisesRegex(ValueError,'INCOMPLETE_KERNEL_INVENTORY'):self.run_report(rows=[self.extra])
    def test_unknown_kernel_signature_refused(self):
        r=copy.deepcopy(self.kernel);r['name']='N.noConfusion'
        with self.assertRaisesRegex(ValueError,'MISSING_KERNEL_SIGNATURE'):self.run_report(rows=[r,self.extra])
    def test_missing_compiler_extra_refused(self):
        with self.assertRaisesRegex(ValueError,'INVENTORY_COUNT_MISMATCH'):self.run_report(rows=[self.kernel])
    def test_duplicate_name_refused(self):
        with self.assertRaisesRegex(ValueError,'DUPLICATE_API_ROW'):self.run_report(rows=[self.kernel,self.extra,self.extra])
    def test_missing_module_manifest_refused(self):
        with self.assertRaisesRegex(ValueError,'INCOMPLETE_API_MODULES'):self.run_report(count=False)
    def test_visibility_mismatch_refused(self):
        r=copy.deepcopy(self.kernel);r['internal']=True
        with self.assertRaisesRegex(ValueError,'NAME_FLAG_MISMATCH'):self.run_report(rows=[r,self.extra])
    def test_false_private_flag_refused(self):
        r=copy.deepcopy(self.kernel);r['private']=True
        with self.assertRaisesRegex(ValueError,'NAME_FLAG_MISMATCH'):self.run_report(rows=[r,self.extra])
    def test_compiler_kernel_overlap_refused(self):
        r=copy.deepcopy(self.kernel);r['category']='compiler_extra'
        with self.assertRaisesRegex(ValueError,'CROSS_CATEGORY_NAME_OVERLAP'):self.run_report(rows=[self.kernel,r])
    def test_malformed_frozen_type_hash_refused(self):
        row=copy.deepcopy(self.row);row['type_sha256']='not a type hash'
        self.text=json.dumps(row)+'\n';self.manifest['sha256']=hashlib.sha256(self.text.encode()).hexdigest()
        with self.assertRaisesRegex(ValueError,'INVALID_SIGNATURE_ROW'):self.run_report()
    def test_changed_name_structure_refused(self):
        r=copy.deepcopy(self.kernel);r['name_parts']=['str',['anonymous'],'other']
        with self.assertRaisesRegex(ValueError,'SIGNATURE_NAME_MISMATCH'):self.run_report(rows=[r,self.extra])
if __name__=='__main__':unittest.main()
