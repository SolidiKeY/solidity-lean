"""Guard regression: a partial audit or guarded rejection implies full coverage."""
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest

root = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('exact_audit_controls', root / 'scripts/h55/module-times/exact_audit_controls.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class ExactAuditControls(unittest.TestCase):
    def test_scope_driver_and_source_binding(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp).resolve()
            rows = []
            for name in module.ROLES:
                relative = module.PREFIX + name + '.lean'
                source = base / relative
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text('fixture')
                rows.append({'path': relative, 'sha256': hashlib.sha256(source.read_bytes()).hexdigest()})
            result = {r['candidate']['path']: r for r in module.classify(base, rows)}
            get = lambda name: result[module.PREFIX + name + '.lean']
            self.assertIn('outside frozen interface census', get('JointWitnessControls')['role'])
            self.assertIn('not full census', get('VisitedSetAudit')['role'])
            self.assertIn('explicitly selects', get('VisitedSetAudit')['driver'])
            self.assertIn('not H55 attestation', get('JointWitness')['expected_outcome'])
            self.assertIn('timing STOP', get('JointWitness')['expected_outcome'])
            self.assertIn('empty tuples', get('RecoveryAudit')['role'])
            with self.assertRaises(ValueError):
                module.classify(base, rows + rows[:1])
            (base / rows[0]['path']).write_text('changed')
            with self.assertRaises(ValueError):
                module.classify(base, rows)

if __name__ == '__main__':
    unittest.main()
