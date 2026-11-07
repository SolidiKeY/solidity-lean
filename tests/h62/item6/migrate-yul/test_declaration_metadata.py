"""Partial or uninitialized metadata cannot be accepted as a complete record."""
import importlib.util,json,pathlib,sys,tempfile,unittest
sys.dont_write_bytecode=True
scripts=pathlib.Path(__file__).resolve().parents[4]/'scripts/h62/item6/migrate-yul';sys.path.insert(0,str(scripts))
spec=importlib.util.spec_from_file_location('declaration_metadata',scripts/'declaration-metadata.py');metadata=importlib.util.module_from_spec(spec);spec.loader.exec_module(metadata)
class DeclarationMetadata(unittest.TestCase):
    def test_fail_closed_controls(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=pathlib.Path(tmp)/'raw.jsonl';module=metadata.interfaces.module_name('Example')
            h=dict(record='header',schema=1,module=module,loaded_extensions=True,import_all=True,import_level='private',expected_declarations=0,expected_classes=0,expected_instances=0,expected_defaults=0)
            f=dict(record='complete',module=module,declarations=0,classes=0,instances=0,defaults=0,migration_acceptance=False)
            def write(rows):p.write_text(''.join(json.dumps(row)+'\n' for row in rows))
            write([h,f]);self.assertFalse(metadata.inspect(p,'Example')['migration_acceptance'])
            write([h])
            with self.assertRaisesRegex(ValueError,'incomplete'):metadata.inspect(p,'Example')
            h['loaded_extensions']=False;write([h,f])
            with self.assertRaisesRegex(ValueError,'initialization'):metadata.inspect(p,'Example')
            h['loaded_extensions']=True;h['expected_instances']=1;write([h,f])
            with self.assertRaisesRegex(ValueError,'coverage/count'):metadata.inspect(p,'Example')
            h['expected_instances']=0;f['migration_acceptance']=True;write([h,f])
            with self.assertRaisesRegex(ValueError,'acceptance claim'):metadata.inspect(p,'Example')
if __name__=='__main__':unittest.main()
