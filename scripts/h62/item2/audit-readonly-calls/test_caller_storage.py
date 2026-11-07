"""Guard missing caller-storage obligations and mismapped helper proofs."""
import importlib.util
from pathlib import Path
import subprocess
import unittest
spec=importlib.util.spec_from_file_location('caller_storage_controls',Path(__file__).with_name('check_caller_storage.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);g=m.gate
class CallerStorageControls(unittest.TestCase):
    def test_complete_inventory(self):
        raw=(g.ROOT/g.SOURCE).read_bytes()
        self.assertEqual(len(g.inventory(raw)),9)
        self.assertEqual(g.NAMES[4:7],['storage_joint','exit_joint','owned_exit_joint'])
        self.assertEqual(g.INTERFACES,[g.TARGET+'.'+n for n in ['caller_storage','caller_exit','lowered_caller_exit']])
        for bad in [b'import Extra.Module\n'+raw,raw+b'\nnamespace Extra\ntheorem padding : True := True.intro\nend Extra\n']:
            with self.assertRaises(ValueError):g.inventory(bad)
    def test_original_premise_surface(self):
        file='Solidity/Lowering/Readonly/PrimitiveFields.lean'
        raw=subprocess.check_output(['git','show',g.original.BASE+':'+file],cwd=g.ROOT)
        rows={r['source_name']:r for r in g.original.export.census.declarations_text(file,raw.decode())}
        for name in g.INTERFACES:
            self.assertIn('raw : i.RawAt result final',rows[name]['signature'])
            self.assertIn('frames : i.RuntimeFrames final',rows[name]['signature'])
        self.assertIn('layout : CallLayout i C',rows[g.INTERFACES[2]]['signature'])
if __name__=='__main__':unittest.main()
