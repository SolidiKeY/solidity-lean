"""Guard regression: diagnostics and intentional negatives become passing proofs."""
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest

path = Path(__file__).resolve().parents[3] / 'scripts/h55/module-times/automation_controls.py'
spec = importlib.util.spec_from_file_location('automation_controls', path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class AutomationControls(unittest.TestCase):
    def test_roles_effects_and_source_binding(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            rows = []
            for name in module.ROLES:
                relative = module.PREFIX + name + '.lean'
                source = root / relative
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text('fixture')
                rows.append({'path': relative, 'sha256': hashlib.sha256(source.read_bytes()).hexdigest()})
            result = {r['candidate']['path']: r for r in module.classify(root, {'rows': rows})}
            get = lambda name: result[module.PREFIX + name + '.lean']
            self.assertIn('rejected', get('ClosedSpecRejected')['role'])
            self.assertIn('successful Lean exit', get('ClosedSpecRejected')['expected_outcome'])
            self.assertIn('temporary directory', get('ImportedAudit')['effects'])
            self.assertIn('do not prove', get('DerivationCertificate')['role'])
            self.assertIn('writes .lake/', get('ClosedSpecProposal')['effects'])
            self.assertIn('external verdicts', get('DirectRuntime')['role'])
            self.assertEqual('unresolved current invocation', get('ProfileSimp')['driver'])
            with self.assertRaises(ValueError):
                module.classify(root, {'rows': rows + rows[:1]})
            (root / rows[0]['path']).write_text('changed')
            with self.assertRaises(ValueError):
                module.classify(root, {'rows': rows})

if __name__ == '__main__':
    unittest.main()
