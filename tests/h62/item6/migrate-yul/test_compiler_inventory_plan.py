"""A contradictory zero count must never skip a verified nonempty module."""
import hashlib,importlib.util,json,pathlib,sys,tempfile,unittest
sys.dont_write_bytecode=True
scripts=pathlib.Path(__file__).resolve().parents[4]/'scripts/h62/item6/migrate-yul'
sys.path.insert(0,str(scripts))
spec=importlib.util.spec_from_file_location('old_compiler_export',scripts/'export-old-compiler-signatures.py')
export=importlib.util.module_from_spec(spec);spec.loader.exec_module(export)
class CompilerInventoryPlan(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.path=pathlib.Path(self.tmp.name)/'summary.json'
        name=['str',['anonymous'],'extra']
        self.path.write_text(json.dumps(dict(module='Example',header=dict(extra_codegen_count=1,extra_codegen_names=[name]))))
        sha=hashlib.sha256(self.path.read_bytes()).hexdigest()
        self.census=dict(yul_modules=['Example'])
        self.names=dict(module_count=1,compiler_name_records=1,modules=[dict(module='Example',summary=str(self.path),summary_sha256=sha,compiler_name_records=1,extra_codegen_names=[name])])
        self.kernel=dict(module_count=1,selected_for_verification=1,modules=[dict(module='Example',summary=str(self.path),summary_sha256=sha)])
    def test_verified_nonempty_plan_retained(self):
        self.assertEqual(export.validate_plan(self.census,self.names,self.kernel),self.names['modules'])
    def test_contradictory_zero_cannot_skip_query(self):
        self.names['modules'][0]['compiler_name_records']=0
        self.names['compiler_name_records']=0
        with self.assertRaisesRegex(ValueError,'count contradicts'):
            export.validate_plan(self.census,self.names,self.kernel)
    def test_summary_identity_bound_to_kernel_inventory(self):
        other=self.path.with_name('same-bytes.json');other.write_bytes(self.path.read_bytes())
        self.names['modules'][0]['summary']=str(other)
        with self.assertRaisesRegex(ValueError,'not bound'):
            export.validate_plan(self.census,self.names,self.kernel)
    def test_top_level_total_cannot_hide_missing_name(self):
        self.names['compiler_name_records']=0
        with self.assertRaisesRegex(ValueError,'total mismatch'):
            export.validate_plan(self.census,self.names,self.kernel)
if __name__=='__main__':unittest.main()
