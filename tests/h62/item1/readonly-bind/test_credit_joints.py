"""Guard forged credit parents and changed reused source/object/log evidence."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[4]
spec=importlib.util.spec_from_file_location('credit_joints',ROOT/'scripts/h62/item1/readonly-bind/check_credit_joints.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)


class CreditRefusals(unittest.TestCase):
    def test_parent_profile_and_byte_binding(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'receipt.json';path.write_text('{"base":"'+m.original.BASE+'"}')
            for mode in ['frozen','current','unowned']:
                with self.subTest(mode=mode),self.assertRaises(ValueError):m.read_parent(path,mode)

    def test_frozen_source_object_log_substitution(self):
        with tempfile.TemporaryDirectory() as tmp:
            parent=Path(tmp);relative='Solidity/A.lean';raw=b'original source'
            source=parent/'original'/relative;source.parent.mkdir(parents=True);source.write_bytes(raw)
            obj=parent/'library/Solidity/A.olean';obj.parent.mkdir(parents=True);obj.write_bytes(b'object')
            log=parent/'compile.log';log.write_bytes(b'passed')
            receipt={'base':m.original.BASE,'source_pins':{relative:{'source_sha256':m.check.sha(source)}},
                     'artifacts':{relative:{'artifact_sha256':m.check.sha(obj)}},
                     'steps':[{'log':str(log),'sha256':m.check.sha(log)}],
                     'protected_sha256':{str(p):m.check.sha(p) for p in [m.check.LEAN,ROOT/'lean-toolchain']}}
            with patch.object(m.original,'read_git',return_value=raw):
                m.verify_parent(parent,receipt,'frozen')
                for path in [source,obj,log]:
                    saved=path.read_bytes();path.write_bytes(b'substituted')
                    with self.subTest(path=path),self.assertRaises(ValueError):m.verify_parent(parent,receipt,'frozen')
                    path.write_bytes(saved)
                obj.unlink()
                with self.assertRaises(OSError):m.verify_parent(parent,receipt,'frozen')

    def test_current_flat_object_alias(self):
        with tempfile.TemporaryDirectory() as tmp:
            parent=Path(tmp);relative='tests/h62/item1/readonly-bind/PhaseControls.lean'
            obj=parent/'library/PhaseControls.olean';obj.parent.mkdir(parents=True);obj.write_bytes(b'object')
            pins={relative:{'source_sha256':'synthetic-source-observation'}}
            receipt={'project_order':[],'source_pins':pins,'artifacts':{relative:{'artifact_sha256':m.check.sha(obj)}},
                     'steps':[],'input_pins':{str(p):m.check.sha(p) for p in [m.check.LEAN,ROOT/'lean-toolchain']}}
            with patch.object(m.profile,'closure',return_value=([],pins)):
                m.verify_parent(parent,receipt,'current');obj.write_bytes(b'substituted')
                with self.assertRaises(ValueError):m.verify_parent(parent,receipt,'current')

    def test_frozen_artifact_refused(self):
        for raw in [b'{}',b'{"theorem_count":792}']:
            with self.assertRaises(ValueError):m.inventory(raw)

    def test_axiom_refusals(self):
        rows=["'"+m.PREFIX+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in m.NAMES]
        self.assertEqual(len(m.parse_axioms('\n'.join(rows))),8)
        for bad in ['\n'.join(rows[:-1]),'\n'.join(rows+[rows[0]]),
                    '\n'.join(rows).replace('propext','sorryAx'),'\n'.join(rows).replace(m.PREFIX,'Foreign.')]:
            with self.subTest(bad=bad),self.assertRaises(ValueError):m.parse_axioms(bad)

    def test_retained_parent_digest(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'receipt.json';path.write_bytes(b'admitted');digest=m.check.sha(path)
            pins={};path.write_bytes(b'substituted-after-admission')
            with self.assertRaises(ValueError):m.original.pin_authenticated_file(pins,path,digest)
            self.assertEqual(pins[str(path)],digest)


if __name__=='__main__':unittest.main()
