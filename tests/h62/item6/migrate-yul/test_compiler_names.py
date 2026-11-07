"""Negative accounting controls; no claim about IR type or visibility correctness."""
import hashlib, importlib.util, json, pathlib, sys, tempfile, unittest
sys.dont_write_bytecode = True
scripts = pathlib.Path(__file__).resolve().parents[4] / 'scripts/h62/item6/migrate-yul'
sys.path.insert(0, str(scripts))
spec = importlib.util.spec_from_file_location('compiler_names', scripts / 'census-ir-names.py')
census = importlib.util.module_from_spec(spec)
spec.loader.exec_module(census)

class CompilerNames(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = pathlib.Path(self.tmp.name)
        self.summary = self.root / 'summary.json'
        self.inventory = self.root / 'inventory.json'
        self.name = ['str', ['anonymous'], 'example']
        self.snapshot = dict(module='Example', schema=3, declarations=[dict(name=self.name)],
            header=dict(extra_codegen_scope='IR-only names; not kernel ConstantInfo declarations',
                        extra_codegen_count=1, extra_codegen_names=[self.name]))
        self.report = dict(status='pass', migration_acceptance=False,
            scope='pinned old persisted-kernel inventory integrity only',
            base='c6f550e281a7e5affa9a99bc2cdaed556dec00e4', module_count=1,
            selected_for_verification=1, modules=[dict(module='Example', schema=3,
            summary=str(self.summary), summary_sha256='')])
        self.save()

    def save(self):
        self.summary.write_text(json.dumps(self.snapshot))
        self.report['modules'][0]['summary_sha256'] = hashlib.sha256(self.summary.read_bytes()).hexdigest()
        self.inventory.write_text(json.dumps(self.report))

    def test_overlap_is_retained_with_unknown_ir_type_and_visibility(self):
        result = census.collect(self.inventory)
        self.assertEqual(result['also_kernel_records'], 1)
        self.assertEqual(result['names'][0]['also_kernel_in'], ['Example'])
        self.assertIsNone(result['names'][0]['ir_type'])
        self.assertIsNone(result['names'][0]['public_visibility'])
        self.assertFalse(result['migration_acceptance'])

    def test_tampered_summary_rejected(self):
        self.summary.write_text(self.summary.read_text() + ' ')
        with self.assertRaisesRegex(ValueError, 'digest mismatch'):
            census.collect(self.inventory)

    def test_incomplete_inventory_rejected(self):
        self.report['selected_for_verification'] = 0
        self.save()
        with self.assertRaisesRegex(ValueError, 'incomplete'):
            census.collect(self.inventory)

    def test_duplicate_compiler_name_rejected(self):
        self.snapshot['header']['extra_codegen_names'].append(self.name)
        self.snapshot['header']['extra_codegen_count'] = 2
        self.save()
        with self.assertRaisesRegex(ValueError, 'duplicate extra'):
            census.collect(self.inventory)

    def test_invalid_name_rejected(self):
        self.snapshot['header']['extra_codegen_names'] = [['num', ['anonymous'], -1]]
        self.save()
        with self.assertRaisesRegex(ValueError, 'invalid name'):
            census.collect(self.inventory)

if __name__ == '__main__':
    unittest.main()
