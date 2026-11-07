"""Transport integrity controls for compiler snapshots, not compiler correctness."""
import importlib.util, json, pathlib, sys, tempfile, unittest
sys.dont_write_bytecode = True
scripts = pathlib.Path(__file__).resolve().parents[4]/'scripts/h62/item6/migrate-yul'
sys.path.insert(0,str(scripts))
spec = importlib.util.spec_from_file_location('compiler_signatures',scripts/'compiler-signatures.py')
collector = importlib.util.module_from_spec(spec)
spec.loader.exec_module(collector)

class CompilerSignatures(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.path = pathlib.Path(self.tmp.name)/'snapshot.jsonl'
        module = collector.interfaces.module_name('Example')
        self.rows = [dict(record='header',schema=1,module=module,expected_names=1,
            module_uses_module_system=False,inspector_header_is_module=False),
            dict(record='compiler_name',module=module,name=['str',['anonymous'],'name'],
                 private_name_marker=False,kernel_constant_available=False,
                 compiler_is_decl_public=True,ir_lookup='not_found',signature=None),
            dict(record='complete',module=module,count=1,ir_found=0,ir_missing=1,migration_acceptance=False)]
    def inspect(self):
        self.path.write_text(''.join(json.dumps(r)+'\n' for r in self.rows))
        return collector.inspect(self.path,'Example')
    def found(self):
        name = self.rows[1]['name']
        self.rows[1].update(ir_lookup='found', signature=dict(name=name,extern=False,
            parameters=[dict(variable_index=2,borrow=True,type=['struct',None,
                [['union',name,[['repr','Lean.IR.IRType.uint8']]]]])],
            result=['repr','Lean.IR.IRType.object']))
        self.rows[-1].update(ir_found=1,ir_missing=0)
    def test_found_nested_signature_retained(self):
        self.found()
        result = self.inspect()
        self.assertEqual(result['declarations'][0]['signature'],self.rows[1]['signature'])
        self.assertFalse(result['migration_acceptance'])
    def test_mismatched_signature_name_rejected(self):
        self.found()
        self.rows[1]['signature']['name']=['str',['anonymous'],'other']
        with self.assertRaisesRegex(ValueError,'signature identity'):
            self.inspect()
    def test_malformed_nested_ir_rejected(self):
        self.found()
        self.rows[1]['signature']['parameters'][0]['type'][2][0][2]=False
        with self.assertRaisesRegex(ValueError,'IR type'):
            self.inspect()
    def test_missing_ir_retained_and_unaccepted(self):
        result = self.inspect()
        self.assertIsNone(result['declarations'][0]['signature'])
        self.assertFalse(result['migration_acceptance'])
    def test_truncation_rejected(self):
        self.rows.pop()
        with self.assertRaisesRegex(ValueError,'incomplete'):
            self.inspect()
    def test_forged_found_count_rejected(self):
        self.rows[-1]['ir_found']=1
        with self.assertRaisesRegex(ValueError,'count mismatch'):
            self.inspect()
    def test_acceptance_claim_rejected(self):
        self.rows[-1]['migration_acceptance']=True
        with self.assertRaisesRegex(ValueError,'acceptance claim'):
            self.inspect()

if __name__ == '__main__':
    unittest.main()
