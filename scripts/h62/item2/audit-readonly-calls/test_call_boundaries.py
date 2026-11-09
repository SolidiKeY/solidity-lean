"""Guard dropped boundary cases and wrong original-interface witness inventories."""
import importlib.util
from pathlib import Path
import unittest
spec=importlib.util.spec_from_file_location('boundary_controls',Path(__file__).with_name('check_call_boundaries.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
g=m.gate
class BoundaryControls(unittest.TestCase):
    def test_inventory_and_mapping(self):
        raw=(g.ROOT/g.SOURCE).read_bytes()
        self.assertEqual(len(g.inventory(raw)),8)
        self.assertEqual(g.INTERFACES,[g.TARGET+'.'+n for n in ['static_operation','return_short','return_revert']])
        self.assertEqual(len(set(g.NAMES)),8)
        for bad in [b'import Extra.Module\n'+raw,raw+b'\nnamespace Extra\ntheorem padding : True := True.intro\nend Extra\n']:
            with self.assertRaises(ValueError):g.inventory(bad)
    def test_original_type_and_header_binding(self):
        import json
        import subprocess
        raw=subprocess.check_output(['git','show',g.original.BASE+':Solidity/Backend/Passes/SourceCallBoundary.lean'],cwd=g.ROOT)
        rows=g.original.export.census.declarations_text('Solidity/Backend/Passes/SourceCallBoundary.lean',raw.decode())
        actual={r['source_name']:r for r in rows}
        self.assertTrue(set(g.INTERFACES)<=set(actual))
        self.assertIn('(h : F.static = true)',actual[g.INTERFACES[0]]['signature'])
        self.assertIn('short : data.length < 32 * rs.length',actual[g.INTERFACES[1]]['signature'])
if __name__=='__main__':unittest.main()
