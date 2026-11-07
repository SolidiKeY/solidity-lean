"""Guard regression: target data inhabitance counts as joint or physical adequacy."""
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest

root = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('storage_audit_controls', root/'scripts/h55/module-times/storage_audit_controls.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class StorageAuditControls(unittest.TestCase):
    def test_scope_state_and_source_binding(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp).resolve()
            rows = []
            for name in module.ROLES:
                path = module.PREFIX + name + '.lean'
                source = base / path
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text('fixture')
                rows.append({'candidate': {'path':path, 'sha256':hashlib.sha256(source.read_bytes()).hexdigest()}, 'state':'new-candidate'})
            result = {r['candidate']['path']:r for r in module.classify(base, rows)}
            get = lambda name: result[module.PREFIX + name + '.lean']
            self.assertIn('not joint logical-premise', get('TargetInputWitnesses')['role'])
            self.assertIn('prerequisites or dependencies only', get('TargetTotality')['driver'])
            self.assertIn('not physical execution', get('GeneratedFamilyWitnesses')['role'])
            self.assertIn('no wall deadline', get('TargetTotality')['expected_outcome'])
            with self.assertRaises(ValueError):
                module.classify(base, rows + rows[:1])
            with self.assertRaises(ValueError):
                module.classify(base, [{**rows[0], 'state':'referenced-static-only'}])
            (base / rows[0]['candidate']['path']).write_text('changed')
            with self.assertRaises(ValueError):
                module.classify(base, rows)

if __name__ == '__main__':
    unittest.main()
