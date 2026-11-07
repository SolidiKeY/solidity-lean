"""Guard regression: finite impossibility or census output counts as a joint witness."""
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest

root = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('theories_audit_controls', root / 'scripts/h55/module-times/theories_audit_controls.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class TheoriesAuditControls(unittest.TestCase):
    def test_scope_effects_and_source_binding(self):
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
            self.assertIn('not a joint witness', get('FiniteBoundary')['role'])
            self.assertIn('not physical gas', get('MirrorWitnesses')['role'])
            self.assertIn('H62_AUDIT_CENSUS_OUT', get('ElaboratedCensus')['effects'])
            self.assertIn('not an RSS cap', get('CoreTotality')['expected_outcome'])
            with self.assertRaises(ValueError):
                module.classify(base, rows + rows[:1])
            (base / rows[0]['path']).write_text('changed')
            with self.assertRaises(ValueError):
                module.classify(base, rows)

if __name__ == '__main__':
    unittest.main()
