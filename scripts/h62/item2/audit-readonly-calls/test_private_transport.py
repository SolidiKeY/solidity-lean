"""Guard private-name substitution and omitted private interface/proof links."""
import importlib.util
from pathlib import Path
import subprocess
import unittest
spec=importlib.util.spec_from_file_location('private_transport_controls',Path(__file__).with_name('check_private_transport.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);g=m.gate
class PrivateTransportControls(unittest.TestCase):
    def test_inventory(self):
        raw=(g.ROOT/g.SOURCE).read_bytes()
        self.assertEqual(len(g.inventory(raw)),5)
        for bad in [raw.replace(b'import Lean\n',b''),b'import Extra.Module\n'+raw,raw+b'\nnamespace Extra\ntheorem padding : True := True.intro\nend Extra\n']:
            with self.assertRaises(ValueError):g.inventory(bad)
    def test_private_use_probe(self):
        files=['Solidity/Lowering/Readonly/PrimitiveFields.lean','Solidity/Lowering/Readonly/PrimitiveReads.lean']
        rows=[]
        for file in files:
            raw=subprocess.check_output(['git','show',g.original.BASE+':'+file],cwd=g.ROOT)
            rows.extend(r for r in g.original.export.census.declarations_text(file,raw.decode()) if r['source_name'] in g.INTERFACES)
        data={'modules':[{'file':f} for f in files],'declarations':rows}
        query=m.generate_with_private_uses(data)
        for name,proof in zip(g.INTERFACES,g.NAMES[:4],strict=True):
            self.assertIn('H62-PRIVATE-USE '+name+' '+g.PREFIX+proof,query)
        self.assertEqual(query.count('info.value.getUsedConstants.contains'),4)
        with self.assertRaises(ValueError):m.generate_with_private_uses(dict(data,declarations=rows[:-1]))
        altered=[dict(r,visibility=[]) for r in rows]
        with self.assertRaises(ValueError):m.generate_with_private_uses(dict(data,declarations=altered))
if __name__=='__main__':unittest.main()
