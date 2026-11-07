"""Guard regression: historical conditional proofs become current migration acceptance."""
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest

path = Path(__file__).resolve().parents[3] / 'scripts/h55/module-times/source_relation_controls.py'
spec = importlib.util.spec_from_file_location('source_relation_controls', path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class SourceRelationControls(unittest.TestCase):
    def test_conditional_scope_and_source_binding(self):
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
            self.assertIn('assumes universal pointwise equivalence', get('ContextMapAcceptance')['role'])
            self.assertIn('no helper migration', get('HelperCompatibility')['role'])
            self.assertIn('default 600s is not the 300s gate', get('HelperCompatibility')['driver'])
            self.assertIn('not current gate acceptance', get('RelationRoundtrip')['expected_outcome'])
            with self.assertRaises(ValueError):
                module.classify(root, {'rows': rows + rows[:1]})
            (root / rows[0]['path']).write_text('changed')
            with self.assertRaises(ValueError):
                module.classify(root, {'rows': rows})

if __name__ == '__main__':
    unittest.main()
