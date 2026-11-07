"""Guard unadmitted receipts, changed reused objects and foreign callback axioms."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[4]
spec=importlib.util.spec_from_file_location('callback_check',
    ROOT/'scripts/h62/item1/readonly-bind/check_callback_boundaries.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)


class ReuseRefusals(unittest.TestCase):
    def test_fabricated_receipt_not_admitted(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'receipt.json'
            for raw in [b'{}',b'{"full_goal_acceptance":false,"project_cache_fallback":false}',b'[]']:
                path.write_bytes(raw)
                with self.assertRaisesRegex(ValueError,'unadmitted parent receipt'):
                    m.read_parent(path)

    def test_source_object_mutation_and_missing(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)/'root';parent=Path(tmp)/'parent'
            source=root/'Solidity/A.lean';source.parent.mkdir(parents=True);source.write_bytes(b'source')
            artifact=parent/'library/Solidity/A.olean';artifact.parent.mkdir(parents=True);artifact.write_bytes(b'object')
            receipt={'source_pins':{'Solidity/A.lean':{'source_sha256':m.check.sha(source)}},
                     'artifacts':{'Solidity/A.lean':{'artifact_sha256':m.check.sha(artifact)}}}
            m.verify_objects(root,parent,receipt)
            source.write_bytes(b'changed')
            with self.assertRaisesRegex(ValueError,'source drift'):m.verify_objects(root,parent,receipt)
            source.write_bytes(b'source');artifact.write_bytes(b'changed')
            with self.assertRaisesRegex(ValueError,'object substitution'):m.verify_objects(root,parent,receipt)
            artifact.unlink()
            with self.assertRaises(OSError):m.verify_objects(root,parent,receipt)

    def test_extra_module_alias_checked(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)/'root';parent=Path(tmp)/'parent'
            relative='tests/h62/item1/readonly-bind/PhaseControls.lean'
            source=root/relative;source.parent.mkdir(parents=True);source.write_bytes(b'source')
            artifact=parent/'library/PhaseControls.olean';artifact.parent.mkdir(parents=True);artifact.write_bytes(b'object')
            receipt={'source_pins':{relative:{'source_sha256':m.check.sha(source)}},
                     'artifacts':{relative:{'artifact_sha256':m.check.sha(artifact)}}}
            m.verify_objects(root,parent,receipt)
            artifact.write_bytes(b'changed')
            with self.assertRaises(ValueError):m.verify_objects(root,parent,receipt)

    def test_axiom_record_refusals(self):
        rows=["'"+m.PREFIX+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in m.NAMES]
        self.assertEqual(len(m.parse_axioms('\n'.join(rows))),8)
        for raw in ['\n'.join(rows[:-1]),'\n'.join(rows+[rows[0]]),
                    '\n'.join(rows).replace('propext','sorryAx'),
                    '\n'.join(rows).replace(m.PREFIX,'Foreign.')]:
            with self.subTest(raw=raw),self.assertRaises(ValueError):m.parse_axioms(raw)


if __name__=='__main__':unittest.main()
