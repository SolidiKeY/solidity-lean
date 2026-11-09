"""Guard dropped captured-value cases and accidental private-probe reuse."""
import importlib.util
from pathlib import Path
import subprocess
import unittest
spec=importlib.util.spec_from_file_location('captured_value_controls',Path(__file__).with_name('check_captured_values.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);g=m.gate
class CapturedValueControls(unittest.TestCase):
    def test_exact_inventory(self):
        raw=(g.ROOT/g.SOURCE).read_bytes()
        self.assertEqual(len(g.inventory(raw)),12);self.assertEqual(len(set(g.INTERFACES)),9)
        for bad in [b'import Lean\n'+raw,raw+b'\nnamespace Extra\ntheorem padding : True := True.intro\nend Extra\n']:
            with self.assertRaises(ValueError):g.inventory(bad)
    def test_exact_original_public_selection(self):
        files=['Solidity/Lowering/Readonly/ReceiverCapture.lean','Solidity/Lowering/Readonly/CapturedArguments.lean'];rows=[]
        for file in files:
            raw=subprocess.check_output(['git','show',g.original.BASE+':'+file],cwd=g.ROOT)
            rows.extend(r for r in g.original.export.census.declarations_text(file,raw.decode()) if r['source_name'] in g.INTERFACES)
        self.assertEqual({r['source_name'] for r in rows},set(g.INTERFACES));self.assertTrue(all('private' not in r['visibility'] for r in rows))
        query=g.original.export.generate({'modules':[{'file':f} for f in files],'declarations':rows})
        self.assertNotIn('H62-PRIVATE-USE',query)
        for name in g.INTERFACES:self.assertIn('run_cmd exportOne `'+name,query)
if __name__=='__main__':unittest.main()
