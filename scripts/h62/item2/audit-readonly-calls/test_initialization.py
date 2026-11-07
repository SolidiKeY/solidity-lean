"""Guard invalid initialization/cache credit and silent historical tool repair."""
import hashlib
import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock
spec=importlib.util.spec_from_file_location('initialization_gate',Path(__file__).with_name('check_initialization.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
c=m.cache_module

class InitializationControls(unittest.TestCase):
    def test_witness_inventory(self):
        raw=(m.ROOT/m.SOURCE).read_bytes();self.assertEqual(len(m.inventory(raw)),10)
        for bad in [b'import Extra.Module\n'+raw,raw+b'\nnamespace Extra\ntheorem other : True := True.intro\nend Extra\n']:
            with self.assertRaises(ValueError):m.inventory(bad)

    def test_cache_digest_before_parsing(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);(root/'receipt.json').write_text('not JSON')
            g=type('Inputs',(),{'current':m.current,'original':m.original,'check':m.check})
            with self.assertRaises(ValueError):c.Cache(g,root,'frozen',{},root/'archive')

    def test_copy_refuses_source_object_and_destination_substitution(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);rel='Solidity/Fixture.lean';raw=b'input';obj=b'object'
            source=root/'captured';source.write_bytes(raw);old=root/'library/Solidity/Fixture.olean';old.parent.mkdir(parents=True);old.write_bytes(obj)
            pin=hashlib.sha256(raw).hexdigest();record={'source_sha256':pin,'artifact_sha256':hashlib.sha256(obj).hexdigest()}
            cache=c.Cache.__new__(c.Cache);cache.root=root;cache.gate=m;cache.used=[]
            cache.receipt={'source_pins':{rel:{'source_sha256':pin}},'artifacts':{rel:record}}
            stage=root/'stage/Fixture.lean';dest=root/'out/Fixture.olean'
            self.assertEqual(cache.copy(rel,source,stage,dest),record)
            source.write_bytes(b'wrong')
            with self.assertRaises(ValueError):cache.copy(rel,source,stage,dest)
            source.write_bytes(raw);old.write_bytes(b'wrong')
            with self.assertRaises(ValueError):cache.copy(rel,source,stage,dest)
            old.write_bytes(obj)
            with mock.patch.object(c.shutil,'copyfile',side_effect=lambda a,b:Path(b).write_bytes(b'wrong')):
                with self.assertRaises(ValueError):cache.copy(rel,source,stage,dest)

    def test_exact_git_recovery_and_no_corrupt_snapshot_repair(self):
        with tempfile.TemporaryDirectory() as temp:
            repo=Path(temp)/'repo';repo.mkdir();tool=repo/'scripts/tool.py';tool.parent.mkdir();tool.write_bytes(b'old tool')
            def git(*args):return subprocess.check_output(['git',*args],cwd=repo,stderr=subprocess.DEVNULL)
            git('init','-q');git('add','.');git('-c','user.name=Fixture','-c','user.email=fixture@example.invalid','commit','-qm','fixture')
            head=git('rev-parse','HEAD').decode().strip();pin=hashlib.sha256(tool.read_bytes()).hexdigest();tool.write_bytes(b'new tool')
            archive=Path(temp)/'archive';pins,snaps=c.authenticate_tools(repo,head,{str(tool):pin},archive)
            saved=Path(snaps[str(tool)]['saved']);self.assertEqual(saved.read_bytes(),b'old tool');self.assertEqual(tool.read_bytes(),b'new tool')
            with self.assertRaises(ValueError):c.authenticate_tools(repo,head,{str(tool):pin},Path(temp)/'missing',create=False)
            saved.write_bytes(b'corruption')
            with self.assertRaises(ValueError):c.authenticate_tools(repo,head,{str(tool):pin},archive)
            with self.assertRaises(ValueError):c.authenticate_tools(repo,head,{str(tool):'0'*64},Path(temp)/'bad')
            artifact=repo/'artifact.olean';artifact.write_bytes(b'changed')
            with self.assertRaises(ValueError):c.authenticate_tools(repo,head,{str(artifact):pin},archive)

    def test_held_import_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            with self.assertRaisesRegex(ValueError,'held workload'):m.original.snapshot(lambda _:b'import Solidity.Backend.WorldCalls.Premises\n',m.TARGET,Path(temp))

if __name__=='__main__':unittest.main()
