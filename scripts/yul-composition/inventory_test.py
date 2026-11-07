import importlib.util, json, tempfile, unittest
from pathlib import Path
s=importlib.util.spec_from_file_location('inventory',Path(__file__).with_name('inventory.py'))
m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
class InventoryTests(unittest.TestCase):
    def test_real_archive_and_stale_extraction(self):
        with tempfile.TemporaryDirectory(dir='/workspace/vy5-composition') as d:
            dest=Path(d); archive=m.ROOT/'tests/upstream/solidity-0.8.38.tar.gz';snapshot=m.ROOT/'tests/upstream/snapshot.json'
            result=m.inventory(archive,snapshot,dest)
            self.assertEqual(len(result['files']),80)
            self.assertEqual(m.inventory(archive,snapshot,dest),result)
            (dest/result['files'][0]['path']).write_bytes(b'drift')
            with self.assertRaisesRegex(ValueError,'extraction drift'):m.inventory(archive,snapshot,dest)
    def test_pin_and_archive_drift(self):
        with tempfile.TemporaryDirectory(dir='/workspace/vy5-composition') as d:
            dest=Path(d);a=dest/'archive';a.write_bytes(b'not a tar');s=dest/'snapshot';s.write_text(json.dumps({'commit':m.PIN,'archiveSha256':m.ARCHIVE_SHA}))
            with self.assertRaisesRegex(ValueError,'archive drift'):m.inventory(a,s)
            s.write_text('{}')
            with self.assertRaisesRegex(ValueError,'snapshot pin'):m.inventory(a,s)
if __name__=='__main__':unittest.main()
