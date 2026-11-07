"""Guard regression: successful diagnostic transport hides failed guards."""
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest

path = Path(__file__).resolve().parents[3] / 'scripts/h55/module-times/generic_p10_controls.py'
spec = importlib.util.spec_from_file_location('generic_p10_controls', path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class GenericP10Controls(unittest.TestCase):
    def test_scope_and_source_binding(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            rows = []
            for name in module.ROLES:
                relative = module.PREFIX + name
                source = root / relative
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text('fixture')
                rows.append({'path': relative, 'sha256': hashlib.sha256(source.read_bytes()).hexdigest()})
            result = {r['candidate']['path']: r for r in module.classify(root, {'rows': rows})}
            get = lambda name: result[module.PREFIX + name]
            self.assertIn('not the central', get('GenericP10/AxiomAudit.lean')['role'])
            self.assertIn('not proof identity', get('GenericP10/Correspondence.lean')['role'])
            self.assertIn('exit alone does not prove guard success', get('GenericP10.lean')['expected_outcome'])
            with self.assertRaises(ValueError):
                module.classify(root, {'rows': rows + rows[:1]})
            (root / rows[0]['path']).write_text('changed')
            with self.assertRaises(ValueError):
                module.classify(root, {'rows': rows})

if __name__ == '__main__':
    unittest.main()
