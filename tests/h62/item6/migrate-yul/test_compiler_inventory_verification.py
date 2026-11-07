"""Partial results or a substituted corpus cannot claim original inventory pass."""
import importlib.util,json,pathlib,sys,tempfile,unittest
sys.dont_write_bytecode=True
scripts=pathlib.Path(__file__).resolve().parents[4]/'scripts/h62/item6/migrate-yul'
sys.path.insert(0,str(scripts))
spec=importlib.util.spec_from_file_location('compiler_inventory_verify',scripts/'verify-old-compiler-inventory.py')
verifier=importlib.util.module_from_spec(spec);spec.loader.exec_module(verifier)
class CompilerInventoryVerification(unittest.TestCase):
    def test_partial_and_substituted_corpus_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=pathlib.Path(tmp);manifest=root/'manifest.json';census=root/'census.json';names=root/'names.json'
            census.write_text('{}');names.write_text('{}')
            row=dict(status='running',base='c6f550e281a7e5affa9a99bc2cdaed556dec00e4',migration_acceptance=False,one_module_per_probe=True)
            manifest.write_text(json.dumps(row))
            with self.assertRaisesRegex(ValueError,'completed pinned'):
                verifier.verify(manifest,census,names)
            row['status']='pass';manifest.write_text(json.dumps(row))
            with self.assertRaisesRegex(ValueError,'exact original pinned census'):
                verifier.verify(manifest,census,names)
if __name__=='__main__':unittest.main()
