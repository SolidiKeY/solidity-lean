"""Guard stale snapshots and incomplete premises replacing original effect cases."""
import copy
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest

spec=importlib.util.spec_from_file_location('effect_gate',Path(__file__).with_name('check_effect_rules.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)


class EffectRuleGateControls(unittest.TestCase):
    def test_exact_witness_inventory_and_imports(self):
        raw=(m.ROOT/m.SOURCE).read_bytes();self.assertEqual(len(m.inventory(raw)),16)
        for bad in [b'import Other.Module\n'+raw,raw+b'\nnamespace Extra\ntheorem hidden : True := True.intro\nend Extra\n']:
            with self.assertRaises(ValueError):m.inventory(bad)

    def test_toolchain_change_after_comparison_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            p=Path(temp)/'lean-toolchain';p.write_bytes(b'original')
            expected=m.compatible_toolchain(b'original',p);self.assertEqual(expected,hashlib.sha256(b'original').hexdigest())
            p.write_bytes(b'substituted')
            with self.assertRaises(ValueError):m.original.pin_authenticated_file({},p,expected)
            with self.assertRaises(ValueError):m.compatible_toolchain(b'original',p)

    def test_captured_interface_one_buffer_and_no_live_source_fallback(self):
        path=m.TARGET.replace('.','/')+'.lean';raw=(m.ROOT/path).read_bytes()
        rows=m.original.export.census.declarations_text(path,raw.decode());frozen={'declarations':rows}
        class Changing:
            reads=0
            def read_bytes(self):
                self.reads+=1
                return raw if self.reads==1 else b'changed source'
        captured=Changing();result=m.select_captured(frozen,captured,hashlib.sha256(raw).hexdigest())
        self.assertEqual(captured.reads,1);self.assertEqual(len(result['declarations']),10)
        with self.assertRaises(ValueError):m.select_captured(frozen,captured,hashlib.sha256(raw).hexdigest())

    def test_changed_context_or_missing_interface_refused(self):
        path=m.TARGET.replace('.','/')+'.lean';raw=(m.ROOT/path).read_bytes()
        rows=m.original.export.census.declarations_text(path,raw.decode())
        with self.assertRaises(ValueError):m.select({'declarations':rows[:-1]},raw)
        changed=copy.deepcopy(rows);changed[0]['variable_context']=['variable (extra : False)']
        with self.assertRaises(ValueError):m.select({'declarations':changed},raw)

    def test_incomplete_duplicate_and_new_axiom_records_refused(self):
        lines=["'"+m.PREFIX+n+"' depends on axioms: [propext, Quot.sound]" for n in m.NAMES]
        self.assertEqual(len(m.joint.parse_axioms('\n'.join(lines),m.PREFIX,m.NAMES)),16)
        for bad in ['\n'.join(lines[:-1]),'\n'.join(lines+[lines[0]]),'\n'.join(lines).replace('propext','sorryAx')]:
            with self.assertRaises(ValueError):m.joint.parse_axioms(bad,m.PREFIX,m.NAMES)

    def test_held_import_refused_before_compile(self):
        with tempfile.TemporaryDirectory() as temp:
            with self.assertRaisesRegex(ValueError,'held workload'):
                m.original.snapshot(lambda _:b'import Solidity.Backend.WorldCalls.Premises\n',m.TARGET,Path(temp))


if __name__=='__main__':unittest.main()
