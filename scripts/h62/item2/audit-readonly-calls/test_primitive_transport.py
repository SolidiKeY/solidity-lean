"""Guard missing primitive inputs and captured-interface or trust substitution."""
import copy
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest
spec=importlib.util.spec_from_file_location('primitive_gate',Path(__file__).with_name('check_primitive_transport.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class PrimitiveControls(unittest.TestCase):
    def test_inventory(self):
        raw=(m.ROOT/m.SOURCE).read_bytes()
        self.assertEqual(len(m.inventory(raw)),11)
        with self.assertRaises(ValueError):m.inventory(b'import Extra.Module\n'+raw)
        with self.assertRaises(ValueError):m.inventory(raw+b'\nnamespace Other\ntheorem extra : True := True.intro\nend Other\n')

    def test_captured_interfaces(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);pins={};rows=[]
            for mod in [m.TARGET,'Solidity.Lowering.Readonly.PrimitiveValues']:
                path=mod.replace('.','/')+'.lean';raw=(m.ROOT/path).read_bytes()
                p=root/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
                pins[path]={'source_sha256':hashlib.sha256(raw).hexdigest()}
                rows+=m.original.export.census.declarations_text(path,raw.decode())
            selected=m.select({'declarations':rows},root,pins)
            self.assertEqual(len(selected['declarations']),8)
            bad=copy.deepcopy(rows);bad[0]['variable_context']=['variable (x : False)']
            with self.assertRaises(ValueError):m.select({'declarations':bad},root,pins)
            with self.assertRaises(ValueError):m.select({'declarations':rows[:-1]},root,pins)
            p.write_bytes(b'substitution')
            with self.assertRaises(ValueError):m.select({'declarations':rows},root,pins)

    def test_no_added_or_missing_axioms(self):
        lines=["'"+m.PREFIX+n+"' depends on axioms: [propext, Quot.sound]" for n in m.NAMES]
        self.assertEqual(len(m.joint.parse_axioms('\n'.join(lines),m.PREFIX,m.NAMES)),11)
        for raw in ['\n'.join(lines[:-1]),'\n'.join(lines+[lines[0]]),'\n'.join(lines).replace('Quot.sound','sorryAx')]:
            with self.assertRaises(ValueError):m.joint.parse_axioms(raw,m.PREFIX,m.NAMES)

    def test_preserve_compared_toolchain_and_held_fence(self):
        with tempfile.TemporaryDirectory() as temp:
            p=Path(temp)/'toolchain';p.write_bytes(b'original');digest=m.compatible_toolchain(b'original',p);p.write_bytes(b'changed')
            with self.assertRaises(ValueError):m.original.pin_authenticated_file({},p,digest)
            with self.assertRaisesRegex(ValueError,'held workload'):m.original.snapshot(lambda _:b'import Solidity.Backend.WorldCalls.Premises\n',m.TARGET,Path(temp))

if __name__=='__main__':unittest.main()
