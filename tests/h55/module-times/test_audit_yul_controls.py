"""Guard regression: contradiction, generated output or an 1800s run implies a witness gate."""
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest

root = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('audit_yul_controls', root / 'scripts/h55/module-times/audit_yul_controls.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class AuditYulControls(unittest.TestCase):
    def test_witness_scope_effects_and_source_binding(self):
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
            self.assertIn('not a joint witness', get('ImpossiblePremises')['role'])
            self.assertIn('intentionally uncovered', get('DefaultWitnessControls')['role'])
            self.assertIn('fixed absolute path', get('DefaultWitnessControls')['effects'])
            self.assertIn('1800s', get('Success')['expected_outcome'])
            self.assertIn('possible error rows', get('KernelCensus')['effects'])
            with self.assertRaises(ValueError):
                module.classify(base, rows + rows[:1])
            (base / rows[0]['path']).write_text('changed')
            with self.assertRaises(ValueError):
                module.classify(base, rows)

if __name__ == '__main__':
    unittest.main()
