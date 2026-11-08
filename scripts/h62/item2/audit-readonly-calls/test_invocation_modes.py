"""Guard detached mode cases and missing exact original invocation identities."""
import importlib.util
from pathlib import Path
import subprocess
import unittest
spec=importlib.util.spec_from_file_location('invocation_controls',Path(__file__).with_name('check_invocation_modes.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);g=m.gate
class InvocationControls(unittest.TestCase):
    def test_complete_inventory(self):
        raw=(g.ROOT/g.SOURCE).read_bytes()
        self.assertEqual(len(g.inventory(raw)),8)
        self.assertEqual(g.INTERFACES,[g.TARGET+'.Invocation.'+n for n in ['inherited','view_mode','pure_mode']])
        for bad in [b'import Extra.Module\n'+raw,raw+b'\nnamespace Extra\ntheorem padding : True := True.intro\nend Extra\n']:
            with self.assertRaises(ValueError):g.inventory(bad)
    def test_exact_original_hypotheses(self):
        file='Solidity/Lowering/Readonly/InvocationFrame.lean'
        raw=subprocess.check_output(['git','show',g.original.BASE+':'+file],cwd=g.ROOT)
        rows={r['source_name']:r for r in g.original.export.census.declarations_text(file,raw.decode())}
        for name,premise in zip(g.INTERFACES,['h : i.frame.static = true','view : i.declaration.fnMut = some .view','pure : i.declaration.fnMut = some .pure'],strict=True):
            self.assertIn(premise,rows[name]['signature'])
if __name__=='__main__':unittest.main()
