"""Guard private bind omissions and cache-link byte substitution."""
import hashlib
import importlib.util
from pathlib import Path
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
spec=importlib.util.spec_from_file_location('private_bind_controls',Path(__file__).with_name('check_private_bind.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);g=m.gate
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
class PrivateBindControls(unittest.TestCase):
    def test_inventory(self):
        raw=(g.ROOT/g.SOURCE).read_bytes()
        self.assertEqual(len(g.inventory(raw)),9)
        for bad in [raw.replace(b'import Lean\n',b''),b'import Extra.Module\n'+raw,raw+b'\nnamespace Extra\ntheorem padding : True := True.intro\nend Extra\n']:
            with self.assertRaises(ValueError):g.inventory(bad)
    def test_exact_private_probe(self):
        files=['Solidity/Backend/Passes/SourceCallBoundary.lean','Solidity/Backend/Passes/SourceTypedCall.lean','Solidity/Lowering/Readonly/PrimitiveReads.lean'];rows=[]
        for file in files:
            raw=subprocess.check_output(['git','show',g.original.BASE+':'+file],cwd=g.ROOT)
            rows.extend(r for r in g.original.export.census.declarations_text(file,raw.decode()) if r['source_name'] in g.INTERFACES)
        data={'modules':[{'file':f} for f in files],'declarations':rows}
        query=m.generate(data)
        self.assertEqual(query.count('info.value.getUsedConstants.contains'),3)
        for name,proof in zip(g.INTERFACES,g.NAMES[:3],strict=True):self.assertIn('H62-PRIVATE-USE '+name+' '+g.PREFIX+proof,query)
        with self.assertRaises(ValueError):m.generate(dict(data,declarations=rows[:-1]))
    def test_checked_parent_link_and_restore(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);relative='Solidity/Fixture.lean';captured=root/'captured.lean';captured.write_bytes(b'namespace Fixture\nend Fixture\n')
            old=root/'library/Solidity/Fixture.olean';old.parent.mkdir(parents=True);old.write_bytes(b'controlled fixture object')
            pin={'source_sha256':sha(captured)};record={'source_sha256':sha(captured),'artifact_sha256':sha(old)}
            owner=SimpleNamespace(root=root,receipt={'source_pins':{relative:pin},'artifacts':{relative:record}},gate=SimpleNamespace(check=SimpleNamespace(sha=sha)),used=[])
            original_shutil=g.cache_module.shutil;staged=root/'staged/Fixture.lean';artifact=root/'new-library/Fixture.olean'
            self.assertEqual(m.linked_copy(owner,relative,captured,staged,artifact),record)
            self.assertTrue(old.samefile(artifact));self.assertEqual(sha(old),record['artifact_sha256']);self.assertEqual(owner.used,[relative])
            self.assertIs(g.cache_module.shutil,original_shutil)
            captured.write_bytes(b'drift')
            with self.assertRaises(ValueError):m.linked_copy(owner,relative,captured,root/'bad-stage.lean',root/'bad.olean')
            self.assertFalse((root/'bad.olean').exists());self.assertIs(g.cache_module.shutil,original_shutil);self.assertEqual(sha(old),record['artifact_sha256'])
if __name__=='__main__':unittest.main()
